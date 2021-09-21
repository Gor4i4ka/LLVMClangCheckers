//== MagicConstant.cpp - Magical constant---*- C++ -*--==//
//===----------------------------------------------------------------------===//
///
/// \file
/// This defines MagicConstant, a check that warns about
/// usage of system-dependable types together with 32-bit meaningful constants
///
/// It checks for usage of any type not filtered by a regex expression together with
/// usage of any constant in the specified blacklist in multiple patterns.
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
#include "iostream"

using namespace clang;
using namespace ento;

namespace {

//Consts' blacklist
std::list<int> constsList;

void ListsInit(void) {
	//constslist
	constsList.push_back(0xFFFFFFFF);
	constsList.push_back(0x7FFFFFFF);
	constsList.push_back(0x80000000);

}

// Global flags used by all walkers to determine whether a dangerous type or constant used in context
bool constFlag = false;
bool typeFlag = false;

// flag FALSE setter
void FlagsFlush(void) {
	constFlag = false;
	typeFlag = false;
}

//A general method to throw a warning
//Adapted for statements and declarations
void ThrowError(Stmt *S, Decl *D, AnalysisDeclContext *AC, BugReporter &BR,
		const CheckerBase *Checker) {
	if (!S && !D)
		return;
	if (S) {
		SourceRange R = S->getSourceRange();
		PathDiagnosticLocation ELoc = PathDiagnosticLocation::createBegin(S,
				BR.getSourceManager(), AC);
		BR.EmitBasicReport(AC->getDecl(), Checker,
				"Usage of a system-dependent type together with a 32-bit constant",
				"MagicConstant",
				"Usage of a system-dependent type together with a 32-bit constant",
				ELoc, R);
	}
	if (D) {
		SourceRange R = D->getSourceRange();
		PathDiagnosticLocation ELoc = PathDiagnosticLocation::createBegin(D,
				BR.getSourceManager(), AC);
		BR.EmitBasicReport(AC->getDecl(), Checker,
				"Usage of a system-dependent type together with a 32-bit constant",
				"MagicConstant",
				"Usage of a system-dependent type together with a 32-bit constant",
				ELoc, R);
	}

}

// A method to check a type being a dangerous one
// Custom types are not touched, "safe" ones are filtered with regex
// with preemptive character-lowering.
// The check goes through all possible type's redefenitions (typedefs)

void CheckType(QualType qt, bool *FL) {
	const TypedefType *TD = dyn_cast < TypedefType > (qt);
	if (dyn_cast < RecordType > (&(*qt)))
		return;
	std::string str = qt.getAsString();
	std::regex reg(
			"(.*)8(.*)|(.*)16(.*)|(.*)32(.*)|(.*)64(.*)|(.*)128(.*)|(.*)long long(.*)|u(.*)");
	if (!str.empty()) {
		std::for_each(str.begin(), str.end(), [](char &c) {
			c = std::tolower(c);
		});
		*FL = true;
		if (regex_match(str, reg))
			*FL = false;
		if (*FL)
			if (TD)
				CheckType(
						TD->getDecl()->getCanonicalDecl()->getUnderlyingType(),
						FL);

	}
}

// A general method to check whether a statement or decl
// contain information about dangerous types or constants within.
// The function uses a corresponding method to extract the information for every subtype.

void SearchDanger(Stmt *S, Decl *D, bool *FL) {

	QualType qt;
	// "getType" method is defined only for Stmt subtypes.
	// Usage of templates is redundant
	if (FL == &typeFlag) {

		if (S) {
			if (auto E = dyn_cast < Expr > (S))
				qt = E->getType();

		}
		if (D) {

			if (auto FD = dyn_cast < FunctionDecl > (D))
				qt = FD->getDeclaredReturnType();

			if (auto VD = dyn_cast < VarDecl > (D))
				qt = VD->getType();

			if (auto FD = dyn_cast < FieldDecl > (D)) {
				qt = FD->getType();

			}
		}
		if (!*FL)
			CheckType(qt, FL);
	}
	if (FL == &constFlag)
	// The following code contains low-level calculations to be correctly performed
	// on a system of every bitsize.
	// The code checks a contstant's presence in the specified blacklist,
	// subsequently comparing it with every its member.
			{
		if (IntegerLiteral *IL = dyn_cast < IntegerLiteral > (S)) {
		  auto src = IL->getBeginLoc();
		  if (src.isMacroID())
		    return;
			auto val = *(IL->getValue().getRawData());
			int lsval;
			char *valp;
			char *lsvalp;

			for (auto iter = constsList.begin(); iter != constsList.end();
					iter = std::next(iter, 1)) {

				if (*FL) {

					break;
				}

				lsval = *iter;

				for (int i = 0; i < 4; i++) {

					valp = ((char*) &val + i);
					lsvalp = ((char*) &lsval + i);

					if (i == 3)
						if (*valp == *lsvalp)
							*FL = true;

					if (*valp != *lsvalp)
						break;
				}

			}

		}
	}
}
// A general method to check an expression for dangerous constant
// with an in-depth search.
// BitwiseOps and CallExprs are neglected.
  void CheckChildren(Expr *E) {
    auto src = E->getBeginLoc();
    if (auto BN = dyn_cast<BinaryOperator>(E)) {
      auto opcode = BN->getOpcode();
      if ((opcode == BO_OrAssign) || (opcode == BO_AndAssign))
	return;
      if (BN->isBitwiseOp() || BN->isEqualityOp())
	return;
    }
    if (src.isMacroID())
      return;    
    if (dyn_cast < CallExpr > (E))
      return;
    for (Stmt *Child : E->children()) {
      if (Child && (!constFlag || !typeFlag))
	SearchDanger(Child, NULL, &constFlag);
    }
  }
// General merhods end.

//===----------------------------------------------------------------------===//
// ExprWalk - realisation of a walker through
// potentionally interesting value statements
//===----------------------------------------------------------------------===//
class ExprWalk: public StmtVisitor<ExprWalk> {
	BugReporter &BR;
	const CheckerBase *Checker;
	AnalysisDeclContext *AC;

public:

	explicit ExprWalk(BugReporter &B, const CheckerBase *Checker,
			AnalysisDeclContext *A) :
			BR(B), Checker(Checker), AC(A) {
	}
	// The Necessary methods to recursively walk through AST
	void VisitChildren(Stmt *S);
	void VisitStmt(Stmt *S);
	// The method for checking potentionally relevant Expressing statements
	void VisitExpr(Expr *EX);
	// An empty method to make the walker skip the statements handled by the other walker
	void VisitDeclStmt(DeclStmt *DS);

};

//===----------------------------------------------------------------------===//
// VarWalk - realisation of a walker which handles
// variable and field declarations
//===----------------------------------------------------------------------===//
class VarWalk: public RecursiveASTVisitor<VarWalk> {
	BugReporter &BR;
	const CheckerBase *Checker;
	AnalysisDeclContext *AC;

public:

	explicit VarWalk(BugReporter &B, const CheckerBase *Checker,
			AnalysisDeclContext *A) :
			BR(B), Checker(Checker), AC(A) {
	}

	// Visiting corresponding nodes
	bool VisitVarDecl(VarDecl *VD);

};

} // End anonymous namespace

// VarWalk methods begin
bool VarWalk::VisitVarDecl(VarDecl *VD) {

	FlagsFlush();
	SearchDanger(NULL, VD, &typeFlag);
	if (typeFlag && VD->hasInit()) {
		Expr *E = VD->getInit();
		CheckChildren(E);
		if (constFlag)
			ThrowError(NULL, VD, AC, BR, Checker);
	}
	return true;
}
//VarWalk methods end

//ExprWalk methods begin
void ExprWalk::VisitDeclStmt(DeclStmt *DS) {
}

void ExprWalk::VisitExpr(Expr *EX) {
	FlagsFlush();
	SearchDanger(EX, NULL, &typeFlag);
	CheckChildren(EX);
	if (typeFlag && constFlag)
		ThrowError(EX, NULL, AC, BR, Checker);
	VisitChildren(EX);
}

void ExprWalk::VisitChildren(Stmt *S) {
	// the required VisitChildren method necessary to use Visit
	for (Stmt *Child : S->children())
		if (Child)
			Visit(Child);
}

void ExprWalk::VisitStmt(Stmt *S) {
	VisitChildren(S);
}
//ExprWalk methods end

//===----------------------------------------------------------------------===//
//  MagicConstant checker
//===----------------------------------------------------------------------===//

namespace {
class MagicConstant: public Checker<check::ASTCodeBody> {
public:
	void checkASTCodeBody(const Decl *D, AnalysisManager &AM,
			BugReporter &BR) const;
};
} // end anonymous namespace

void MagicConstant::checkASTCodeBody(const Decl *D, AnalysisManager &AM,
		BugReporter &BR) const {
	ListsInit();

	ExprWalk WalkerValue(BR, this, AM.getAnalysisDeclContext(D));
	VarWalk WalkerVar(BR, this, AM.getAnalysisDeclContext(D));

	FlagsFlush();
	WalkerValue.Visit(D->getBody());
	FlagsFlush();
	WalkerVar.TraverseDecl(const_cast<Decl*>(D));
}

// Registration
void ento::registerMagicConstant(CheckerManager &Mgr) {
	Mgr.registerChecker<MagicConstant>();
}

bool ento::shouldRegisterMagicConstant(const LangOptions &LO) {
	return true;
}
