#ifndef TAINT_H_
#define TAINT_H_
 
#include <llvm/ADT/Statistic.h>
#include <llvm/ADT/SCCIterator.h>
#include <llvm/Support/Debug.h>
#include <llvm/Pass.h>
#include "llvm/ADT/SmallSet.h"
#include <llvm/Analysis/CallGraph.h>
#include <llvm/IR/InstVisitor.h>
#include "llvm/IR/Dominators.h"
#include "llvm/ADT/SmallVector.h"

using namespace llvm;

namespace taint{


class TaintAnalysis : public InstVisitor<TaintAnalysis> {
public:

	SmallSet<Value*, 16> TaintedVariables;
	DominatorTree DT;
	Function *Func;

    TaintAnalysis(Function &F, std::vector<bool> taintSource);
	bool isValueTainted(Value *v);
	void taintBBInstructions(BasicBlock *bb);

	void visitLoadInst(LoadInst &I);

	void visitStoreInst(StoreInst &I);

	void visitCallInst(CallInst &I);

	void visitCallInstSink(CallInst & I);

	void visitReturnInst(ReturnInst &I);

	void visitCastInst(CastInst &I);

	void visitBinaryOperator(BinaryOperator &I);

	void visitVACopyInst(VACopyInst &I);

	void visitBranchInst(BranchInst &I);
	void visitPHINode(PHINode &I);
	void visitGetElementPtrInst(GetElementPtrInst &I);
	void visitSelectInst(SelectInst &I);
	void visitCmpInst(CmpInst &I);
    void print();
};
}
#endif
