//== SecSignExtension.cpp − Second signextension −−−*− C++ −*−−==//
//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//
///
///\ file
/// This defines SecSignExtention, a check that warns about
/// a subvariety of possible overflow errors present in a system of 32−bit though
/// absent in a system of 64−bit and vice−versa
///
/// It checks for presence of undefined behaviour on one of the bit systems
/// in subvariety of possible cases.
///
//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//

// Implementation

#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"

using namespace clang;
using namespace ento;

namespace {
// A conveniet unit to store information about a type and its size depending on bitness

struct TypeInfo {

std:: string typeName;
int typeSize32;
int typeSize64;

TypeInfo (std::stringstr, int size32, int size64) {
	typeName = str;
	typeSize32 = size32;
	typeSize64 = size64;
}
};

// Initialization of a global list
std::list<TypeInfo>typeList;

void 
ListsInit(void) {
// typelist
typeList.push_back(TypeInfo(std::string("char"), 1, 1));
typeList.push_back(TypeInfo(std::string("signed char"), 1, 1));
typeList.push_back(TypeInfo(std::string("unsigned char"), 1, 1));
typeList.push_back(TypeInfo(std::string("short"), 2, 2));
typeList.push_back(TypeInfo(std::string("short int"), 2, 2));
typeList.push_back(TypeInfo(std::string("signed short"), 2, 2));
typeList.push_back(TypeInfo(std::string("signed short int"), 2, 2));
typeList.push_back(TypeInfo(std::string("int"), 4, 4));
typeList.push_back(TypeInfo(std::string("int8_t"), 1, 1));
typeList.push_back(TypeInfo(std::string("int16_t"), 2, 2));
typeList.push_back(TypeInfo(std::string("int32_t"), 4, 4));
typeList.push_back(TypeInfo(std::string("int64_t"), 8, 8));
typeList.push_back(TypeInfo(std::string("uint8_t"), 1, 1));
typeList.push_back(TypeInfo(std::string("uint16_t"), 2, 2));
typeList.push_back(TypeInfo(std::string("uint32_t"), 4, 4));
typeList.push_back(TypeInfo(std::string("uint64_t"), 8, 8));
typeList.push_back(TypeInfo(std::string("signed"), 4, 4));
typeList.push_back(TypeInfo(std::string("signed int"), 4,4));
typeList.push_back(TypeInfo(std::string("unsigned int"), 4, 4));
typeList.push_back(TypeInfo(std::string("long"), 4, 8));
typeList.push_back(TypeInfo(std::string("long int"), 4, 8));
typeList.push_back(TypeInfo(std::string("signed long"), 4, 8));
typeList.push_back(TypeInfo(std::string("signed long int"), 4, 8));
typeList.push_back(TypeInfo(std::string("unsigned long"), 4, 8));
typeList.push_back(TypeInfo(std::string("unsigned long int"), 4, 8));
typeList.push_back(TypeInfo(std::string("long long"), 8, 8));
typeList.push_back(TypeInfo(std::string("long long int"), 8, 8));
typeList.push_back(TypeInfo(std::string("signed long long"), 8, 8));
typeList.push_back(TypeInfo(std::string("signed long long int"), 8, 8));
typeList.push_back(TypeInfo(std::string("unsigned long long"), 8, 8));
typeList.push_back(TypeInfo(std::string("unsigned long long int"), 8, 8));
}

// A method to write 32 and 64 bit size into corresponding variables,
// getting the data from the list.

bool FindList(QualType qtype, int *bit 32, int *bit 64) {
	std::string typeName = qtype.getAsString();
	for(auto it = typeList.begin(); it != typeList.end(); it = next(it, 1 ))
		if (typeName == (*it).typeName) {
			*bit32 = (*it).typeSize32;
			*bit64 = (*it).typeSize64;
			return true;
	}
	return false;
}

// A method to check if conversion from exprTypeQ to castTypeQ is
// defined according to precisely one of the bitness platforms
bool ExprCheck (QualType castTypeQ, QualType exprTypeQ) {

int castSize32, exprSize32, castSize64, exprSize64;

bool foundCast = FindList(castTypeQ, &castSize32, &castSize64);
bool foundExpr = FindList(exprTypeQ, &exprSize32, &exprSize64);

const Type *castType = castTypeQ.getTypePtrOrNull();
const Type *exprType = exprTypeQ.getTypePtrOrNull();

// Implementation of the abovementioned check, taking standart C++ type conversions into consideration
// as a rule.

if (castType && exprType) {
if (foundCast && foundExpr) {

if (castType−>isSignedIntegerType() && exprType->isUnsignedIntegerType()){

if ((castSize32 / exprSize32 < 2 && !(castSize64/exprSize64 < 2)) 
	|| ( castSize64 / exprSize64 < 2 && ! (castSize32 / exprSize32 < 2))) 
	return true;
}
if ((castType−>isSignedIntegerType() || 
	castType−>isUnsignedIntegerType())
	&& exprType−>isSignedIntegerType()) {
		if ((castSize32/exprSize32 < 1
			&& !(castSize64 / exprSize64 < 1))
			|| (castSize64 / exprSize64 < 1
				&& !(castSize32 / exprSize32 < 1))) {
			return true ;
}
}
}
}
return false;
}

class CastWalk:publicStmtVisitor<CastWalk>{
BugReporter &BR;
const CheckerBase *Checker;
AnalysisDeclContext *AC;
void ThrowError(Stmt *S);

public :
explicit CastWalk(BugReporter &B, const CheckerBase *Checker,
AnalysisDeclContext *A): BR(B), Checker (Checker), AC(A) {}
// The Necessary methods to recursively walk through AST
void VisitChildren(Stmt *S);
void VisitStmt(Stmt *S);

// Visiting potential true cases
void VisitBinaryOperator(BinaryOperator *BN);
void VisitCallExpr(CallExpr *CE);
};

class FuncWalk:publicRecursiveASTVisitor<FuncWalk>{
BugReporter &BR;
const CheckerBase *Checker;
AnalysisDeclContext *AC;
void ThrowError(Stmt *S);
QualType funcqt;

public :
explicit FuncWalk(BugReporter &B, const CheckerBase *Checker, AnalysisDeclContext *A): BR(B) , Checker ( Checker ) , AC(A) {}
// The methods to check the declared type and return type of a function t o
// follow the abovementioned rules
bool VisitFunctionDecl(FunctionDecl *FD);
bool VisitReturnStmt(ReturnStmt *RS);

};
}

void 
FuncWalk::ThrowError(Stmt *S) {
	//A general method to "throw" a warning

	SourceRange R = S−>getSourceRange();
	PathDiagnosticLocation ELoc = PathDiagnosticLocation::createBegin(S,
	BR.getSourceManager(), AC);
	BR.EmitBasicReport (AC−>getDecl(), Checker, "Overflow 32-bit/64-bit", "SecSignExtension", "Overflow 32-bit/64-bit", ELoc, R);
}

// Storing function’s return type for future children (ReturnStmt).
bool 
FuncWalk::VisitFunctionDecl(FunctionDecl *FD) {
	funcqt = FD−>getDeclaredReturnType();
	return true;
}

// Getting the actual return value type and comparing it to the  declared one.
bool 
FuncWalk::VisitReturnStmt(ReturnStmt *RS) {
	if (auto expr = RS−>getRetValue ())
		if (ExprCheck(funcqt, expr−>getType()))
			ThrowError(RS);
	return false;
}

// A method to check possible errors, when an actual type of a parameter to a function
// is different from the declared one in a "dangerous" way we search for

void 
CastWalk::VisitCallExpr(CallExpr *CE) {
	if(auto FD = CE−>getDirectCallee())
		if(!FD−>getBuiltinID()){
			unsigned min = CE−>getNumArgs();
			if(min > FD−>getNumParams())
				min = FD−>getNumParams();
				for (unsigned i = 0; i < min; i++)
					if (auto iparm = FD−>getParamDecl(i))
						if (auto iarg = CE−>getArg(i)) {
							QualType parmqt = iparm−>getOriginalType();
							QualType argqt = iarg−>getType();

							if (auto icastarg = dyn_cast<CastExpr> (iarg))
								if (auto isubexpr = icastarg−>getSubExpr())
									argqt = isubexpr−>getType();

							if (ExprCheck(parmqt, argqt))
								ThrowError(CE);
						}

		}
}

void 
CastWalk::ThrowError(Stmt *S){

	//A general method to "throw" a warning
	SourceRange R = S−>getSourceRange();
	PathDiagnosticLocation ELoc = PathDiagnosticLocation::createBegin (S, BR.getSourceManager(), AC);
	BR.EmitBasicReport(AC->getDecl(), Checker, "Overflow 32-bit/64-bit", "SecSignExtension", "Overflow 32-bit/64-bit", ELoc, R);
}

void 
CastWalk::VisitChildren(Stmt *S) {
	for (Stmt *Child: S−>children())
		if (Child)
			Visit( Child );
}

void 
CastWalk::VisitStmt (Stmt *S) {
	VisitChildren(S);
}

// Here only assignment operations are taken into consideration,
// as th e most obvious mistakes easy to fix.
// Bit wise operations are left as prone to being probably false or safe cases.
// Callexpressions are real so managed separately.

void 
CastWalk::VisitBinaryOperator (Binary Operator *BN) {
	if (BN−>isAssignmentOp()){
		auto opcode = BN−>getOpcode();
		if ((opcode != BO_OrAssign) && (opcode != BO_AndAssign)){
			if (opcode != BO_Assign) {
				if (ExprCheck(BN−>getLHS()−>getType(), BN−>getRHS()−>getType()))
					ThrowError(BN);


			} 
			else {
				auto exp1 = BN−>getRHS();
				if (auto exp2 = dyn_cast<CastExpr>(exp1))
					if ( auto exp3 = exp2−>getSubExpr())
						if (ExprCheck(BN−>getLHS()−>getType(), exp3−>getType()))
							ThrowError(BN);

			}

		}
	}
	VisitChildren(BN);

}

//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//
// SecSignExtension checker
//===−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−===//

namespace {
	class SecSignExtension: public Checker<check::ASTCodeBody>{

		public:

			void checkASTCodeBody (const Decl *D, AnalysisManager &AM, BugReporter &BR) const;


	};
} // end anonymous namespace

void 
SecSignExtension::checkASTCodeBody(const Decl *D, AnalysisManager &AM, BugReporter &BR) const {
	ListsInit();

	CastWalk WalkerCast (BR, this, AM.getAnalysisDeclContext (D));
	FuncWalk WalkerFunc (BR, this, AM.getAnalysisDeclContext (D));
	WalkerCast.Visit(D−>getBody());
	WalkerFunc.TraverseDecl(const_cast<Decl *>(D));
}

// Registration

void 
ento::registerSecSignExtension(CheckerManager &Mgr) {
	Mgr.registerChecker<SecSignExtension>();
}
bool 
ento::shouldRegisterSecSignExtension (const LangOptions &LO) {return true;}
