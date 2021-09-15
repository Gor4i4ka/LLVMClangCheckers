//== SquareBrackets.cpp−Square brackets −−−*−C++ −*−−==//
//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//
///
/// \file
/// This defines SquareBrackets, a check that warns about
/// usage of volatile types in [] overflow, restricting usage of large numbers
/// as indexes
///
/// It checks for C++ operator [] overflow parameter’s type .
///
///
//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//
// Implementation
#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/DeclVisitor.h"
#include "clang/AST/Type.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/AST/DeclarationName.h"
#include "stdlib.h"
#include "regex"

using namespace clang ;
using namespace ento ;

//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//
// SquareBracketsChecker −checks for usage of volatile types in [] overflow
//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//

namespace {
class WalkAST: public RecursiveASTVisitor<WalkAST> {
	BugReporter &BR;
	const CheckerBase *Checker;
	AnalysisDeclContext *AC;

	bool checkType (QualType qt);

public:
explicit WalkAST(BugReporter &B, const CheckerBase *Checker, AnalysisDeclContext *A):
BR(B), Checker (Checker), AC(A) {}

// visits if statements searching for the possible mistake
bool VisitCXXMethodDecl (CXXMethodDecl *S) ;
};
} // end anonymous namespace

// Checks the type of [] overflow parameter being of a one having a determined size
bool 
WalkAST::checkType (QualType qt) {

	//We skip possible custom types .
	if (qt−>isRecordType ())
		return true;

	std::string qt_str = qt.getAsString ();
	// The regex checking the type’s name being a possible safe one
	std::regex regt ("(.*)8(.*)|(.*)16(.*)|(.*)32(.*)|(.*)64(.*)|(.*)128(.*)|(.*)size_t(.*)|(.*)ptr(.*)|(.*)long long(.*)");

	if (regex_match(qt_str, regt))
		return true;
	return false;
}

bool 
WalkAST::VisitCXXMethodDecl (CXXMethodDecl *S) {
	FunctionDecl *fd = dyn_cast <FunctionDecl> (S);
	if (fd) {
		DeclarationNameInfo info = fd−>getNameInfo();
		std::string str1 = info.getAsString();
		std::string str2 ("operator[]");

		// Checking whether it is the dangerous pattern and throwing an error if it is.
		if (!str1.compare(str2)){
			if(fd−>getNumParams() < 1)
				return false;

			ParmVarDecl *parm = fd−>getParamDecl(0);
			if (!parm)
				return false;

			QualType qt = parm−>getOriginalType ();
			if (!checkType(qt)) {
				// Throwing a warning
				PathDiagnosticLocation ELoc(S, BR.getSourceManager());
				BR. EmitBasicReport (AC−>getDecl(), Checker, "index operator overload bit error possible", "SquareBracketsChecker",
						"index operator overload bit error possible", ELoc);
			}
		}
	}
	return false;
}

//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//
// SquareBracketsChecker
//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//
//
namespace {
	class SquareBracketsChecker: public Checker<check::ASTCodeBody> {
		public:

			void checkASTCodeBody( const Decl *D, AnalysisManager &AM, BugReporter &BR) const;
	};
} // end anonymous namespace

void 
SquareBracketsChecker::checkASTCodeBody(const Decl *D, AnalysisManager &AM, BugReporter &BR) const {
	WalkAST Walker (BR, this, AM.getAnalysisDeclContext (D));
	Walker.TraverseDecl(const_cast<Decl*>(D));
}

void 
ento::registerSquareBracketsChecker(CheckerManager &Mgr){
	Mgr.registerChecker<SquareBracketsChecker>();
}

bool 
ento::shouldRegisterSquareBracketsChecker(const LangOptions &LO) {
	return true;
}
