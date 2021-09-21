//== MagicConstantMem.cpp - Magical constant memory---*- C++ -*--==//
//===----------------------------------------------------------------------===//
///
/// \file
/// This defines MagicConstantMem, a check that warns about
/// usage of system-dependable types together with 32-bit meaningful constants
/// in memory allocators
///
/// It checks for usage of any dangerous memory constant as a parameter
/// of a possible memory allocator, which is a subversion of alloc
///
//===----------------------------------------------------------------------===//

//Implementation

#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "regex"

using namespace clang;
using namespace ento;

namespace {

class ValueWalk: public StmtVisitor<ValueWalk> {
	BugReporter &BR;
	const CheckerBase *Checker;
	AnalysisDeclContext *AC;

	int insideCallFlag;
	std::list<int> constsList;
	std::list<std::string> funcsList;

	bool inMemFuncList(std::string);
	bool inMemConstList(IntegerLiteral*);
	void ThrowError(Stmt*);

public:
	explicit ValueWalk(BugReporter &B, const CheckerBase *Checker,
			AnalysisDeclContext *A) :
			BR(B), Checker(Checker), AC(A) {
		insideCallFlag = 0;
		//constsList init
		constsList.push_back(4);
		constsList.push_back(8);
	
		//funcList init
		funcsList.push_back(std::string("alloc"));
	}

	// The Necessary methods to recursively walk through AST
	void VisitChildren(Stmt *S);
	void VisitStmt(Stmt *S);
	// The method for checking potential call expressions
	void VisitCallExpr(CallExpr *CE);
	void VisitIntegerLiteral(IntegerLiteral *IL);
};

} // end of anonimous namespace

// ValueWalk methods begin

// Check if a function's name is a variation of alloc, rooting out "calloc cases"
// The name is preemtively lowered.
bool ValueWalk::inMemFuncList(std::string name) {
	// Check if a variation of calloc
	std::regex reg("(.*)calloc(.*)");
	if (regex_match(name, reg))
		return false;
	//Lowercase everything
	std::for_each(name.begin(), name.end(), [](char &c) {
		c = std::tolower(c);
	});
	//Check if a memory func
	bool funcFlag = false;
	std::for_each(funcsList.begin(), funcsList.end(),
			[&name, &funcFlag](std::string s) {
				if (name.find(s) != std::string::npos)
					funcFlag = true;
			});
	return funcFlag;
}

// Check if a constant inside a memory allocator
// is in the blacklist.
bool ValueWalk::inMemConstList(IntegerLiteral *IL) {
	for (auto iter = constsList.begin(); iter != constsList.end(); iter =
			std::next(iter, 1))
		if (*iter == IL->getValue())
			return true;
	return false;
}

// A general method to throw a warning
void ValueWalk::ThrowError(Stmt *S) {
	SourceRange R = S->getSourceRange();
	PathDiagnosticLocation ELoc = PathDiagnosticLocation::createBegin(S,
			BR.getSourceManager(), AC);
	BR.EmitBasicReport(AC->getDecl(), Checker,
			"Usage of a mamory allocator together with a 32-bit constant",
			"MagicConstantMem",
			"Usage of a memory allocator together with a 32-bit constant", ELoc,
			R);

}

void ValueWalk::VisitChildren(Stmt *S) {
	for (Stmt *Child : S->children())
		if (Child)
			Visit(Child);
}

void ValueWalk::VisitStmt(Stmt *S) {
	VisitChildren(S);
}

// Check every CallExpr of being the dangerous pattern
void ValueWalk::VisitCallExpr(CallExpr *CE) {

	if (FunctionDecl *FD = CE->getDirectCallee()) {
		std::string funcName = FD->getNameAsString();
		if (inMemFuncList(funcName))
			insideCallFlag++;
		VisitChildren(CE);
		if (inMemFuncList(funcName))
			insideCallFlag--;
	}
}

void ValueWalk::VisitIntegerLiteral(IntegerLiteral *IL) {
	if (insideCallFlag && inMemConstList(IL))
		ThrowError(IL);
}

//===----------------------------------------------------------------------===//
//  MagicConstantMem checker
//===----------------------------------------------------------------------===//

namespace {
class MagicConstantMem: public Checker<check::ASTCodeBody,
		check::ASTDecl<FieldDecl>> {
public:
	void checkASTCodeBody(const Decl *D, AnalysisManager &AM,
			BugReporter &BR) const;
	void checkASTDecl(const FieldDecl *D, AnalysisManager &AM,
			BugReporter &BR) const;
};
} // end anonymous namespace

void MagicConstantMem::checkASTCodeBody(const Decl *D, AnalysisManager &AM,
		BugReporter &BR) const {
	ValueWalk WalkerValue(BR, this, AM.getAnalysisDeclContext(D));
	WalkerValue.Visit(D->getBody());

}

void MagicConstantMem::checkASTDecl(const FieldDecl *FD, AnalysisManager &AM,
		BugReporter &BR) const {
	if (FD->hasInClassInitializer()) {
		ValueWalk WalkerValue(BR, this, AM.getAnalysisDeclContext(FD));
		WalkerValue.Visit(FD->getInClassInitializer());
	}
}

// Registration
void ento::registerMagicConstantMem(CheckerManager &Mgr) {
	Mgr.registerChecker<MagicConstantMem>();
}

bool ento::shouldRegisterMagicConstantMem(const LangOptions &LO) {
	return true;
}
