//== SecFuncWithoutPrototype.cpp −Second function without prototype−−−∗−C
//
//
//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//
///
/// \file
/// This defines SecFuncWithoutPrototype, a check that warns about
/// implicit function declaration happening within address calculations
///
/// It checks for use of assignment operators which have a pointer as LHS and
/// a call expression of a previously undeclared function .
///
//
//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//
// Implementation

#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
using namespace clang;
using namespace ento;


//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//
// WalkAST −realisation of a walker through
// potentionally interesting assignment binary expressions.
//
//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//

namespace {
	class WalkAST: public StmtVisitor<WalkAST> {
		BugReporter &BR;
		const CheckerBase *Checker;
		AnalysisDeclContext *AC;

		// A general method to throw an error
		void ThrowError (Stmt *S);

		public :
		explicit WalkAST(BugReporter &B, const CheckerBase *checker, AnalysisDeclContext *A): BR(B), Checker(Checker), AC(A){}

		// The Necessary methods to recursively walk through AST

		void VisitChildren(Stmt *S);
		void VisitStmt(Stmt *S);

		// The method for checking potentionally relevant assignment operators
		void VisitBinaryOperator (BinaryOperator *bn);
	};
} // End anonymous namespace

void 
WalkAST::ThrowError (Stmt *S) {

	//A general method to "throw" a warning

	SourceRange R = S−>getSourceRange () ;
	PathDiagnosticLocation ELoc = PathDiagnosticLocation::createBegin (S, BR. getSourceManager(), AC);
	BR.EmitBasicReport (AC−>getDecl(), Checker, "Usage of an implicit function in address calculations", 
			"SEC_FUNC_WITHOUT_PROTOTYPE", "Usage of an implicit function in address calculations", ELoc, R);
}

void 
WalkAST::VisitBinaryOperator(BinaryOperator *bn) {
	// The method to check every binary operator having the dangerous pattern.
	// It sequentially checks if the operator is of assignment type, if its LHS
	// is of a pointer type and if RHS represents an implicit declaration of a function.

	if (bn−>isAssignmentOp()) {
		Expr *left = bn−>getLHS();
		Expr *right = bn−>getRHS();
		QualType qt = left−>getType();
		const Type *tp = qt.getTypePtr();
		// Check i f LHS i s a pointer
		if (tp−>isPointerType())
		// Sequentially getting the possible implicit function declaration
		// The dangerous patter always has the same path in AST tree .
		if ((right−>child_begin()) != right−>child_end())
		if (Stmt *chld1 = *(right−>child_begin()))
		if ((chld1−>child_begin()) != chld1−>child_end())
		if (Stmt *сhld2 = *(chld1−>child_begin()))
		if ((chld2−>child_begin()) != chld2−>child_end())
		if (Stmt *chld3 = *(chld2−>child_begin()))
		if (DeclRefExpr *dre = dyn_cast<DeclRefExpr>(chld3))
		if (ValueDecl *vd = dre−>getDecl () )
		if (FunctionDecl *fd = dyn_cast<FunctionDecl>(vd))
		if (fd−>isImplicit() && !fd−>getBuiltinID())
			ThrowError(right);
	}
	VisitChildren (bn) ;
}

void 
WalkAST::VisitChildren(Stmt *S) {
	// The required VisitChildren method necessary to use Visit
	for (Stmt *Child: S−>children())
		if(Child)
			Visit(Child);
}

// Getting through all the children
void 
WalkAST::VisitStmt (Stmt *S) {
	VisitChildren(S);
}

//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//
// SecFuncWithoutPrototype checker
//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//

namespace {
class SecFuncWithoutPrototype: public Checker<check::ASTCodeBody> {
	public:
	void checkASTCodeBody(const Decl *D, AnalysisManager &AM, BugReporter &BR) const;

};
} // end anonymous namespace

void 
SecFuncWithoutPrototype::checkASTCodeBody(const Decl *D, AnalysisManager &AM, BugReporter &BR) const {
	WalkAST Walker (BR, this , AM.getAnalysisDeclContext(D));
	Walker.Visit (D−>getBody());
}

// Registration
void 
ento::registerSecFuncWithoutPrototype(CheckerManager &Mgr) {
	Mgr.registerChecker <SecFuncWithoutPrototype>();
}

bool 
ento::shouldRegisterSecFuncWithoutPrototype(const LangOptions &LO) {
	return true;
}

