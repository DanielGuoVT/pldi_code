//===- Branch.cpp - Transform branches dependent on secrete data ---------------===//
//   - 10/04 treat all input as sensitive
//
//===---------------------------------------------------------------------------===//
 
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/PassSupport.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/User.h"
#include "llvm/IR/PassManager.h"
#include "Taint.h"
#include <vector>
#define DEBUG_TYPE "taint"

using namespace llvm;

namespace taint{
    

    TaintAnalysis::TaintAnalysis(Function &F, std::vector<bool> taintSource) {
    	DT.recalculate(F);
		//assert(taintSource.size() == F.arg_size() && "TaintAnalysis object create failed due to uncompatible function and its taint configuration!");
		int i = 0;
		for (Function::arg_iterator A = F.arg_begin(), E = F.arg_end(); A != E; ++A) {
			if (taintSource[i])
				TaintedVariables.insert(&*A);
			i++;
		}
	}

	inline bool TaintAnalysis::isValueTainted(Value *v)
	{
        if(std::find(TaintedVariables.begin(), TaintedVariables.end(), v)!= TaintedVariables.end())
			return true;
        return false;
	}

	void TaintAnalysis::visitLoadInst(LoadInst &I) {
		DEBUG(errs() << "LOAD [p=*q]: "; I.print(errs()); errs() << "\n");
		Value *q = I.getPointerOperand();
		if (isValueTainted(q))
			TaintedVariables.insert(&I);
	}

	//**************************************************************************************

	void TaintAnalysis::visitStoreInst(StoreInst &I)
	{ 
		DEBUG(dbgs() << "STORE [*p=q]: "; I.print(dbgs()); dbgs() << "\n");
		Value *q = I.getValueOperand();
		Value *p = I.getPointerOperand();

		if (isValueTainted(q)) {
			TaintedVariables.insert(p);

			while(true){
				GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(p);
				CastInst *cast = dyn_cast<CastInst>(p);

				if(gep)
					p = gep->getPointerOperand();
				else if(cast)
					p = cast->getOperand(0);
				else
					break;
				TaintedVariables.insert(p);
			}
		}
	}

	void TaintAnalysis::visitPHINode(PHINode &I)
	{
		 for (unsigned i = 0, e = I.getNumIncomingValues(); i != e; ++i)
		 {
			 if (isValueTainted(I.getIncomingValue(i)))
			 {
				 TaintedVariables.insert(&I);
				 return;
			 }
		 }

	}

	//**************************************************************************************

	void TaintAnalysis::visitCallInst(CallInst & I)
	{
		bool hasTaintedArg = false;


		for(int i=0; i< I.getNumArgOperands(); i++)
		{
			if(isValueTainted(I.getArgOperand(i)))
			{
				hasTaintedArg = true;
			}
		}

		if(!hasTaintedArg)
			return;

		if(I.getType()->isVoidTy())
		{
			for(int i=0; i< I.getNumArgOperands(); i++)
			{
				Value *arg = I.getArgOperand(i);
				if(isa<Constant>(arg))
					continue;

				TaintedVariables.insert(arg);
				while(true){
					GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(arg);
					CastInst *cast = dyn_cast<CastInst>(arg);

					if(gep)
						arg = gep->getPointerOperand();
					else if(cast)
						arg = cast->getOperand(0);
					else
						break;
					TaintedVariables.insert(arg);
				}
			}

		}
		else
		{
			TaintedVariables.insert(&I);
		}

	}

	//**************************************************************************************

	void TaintAnalysis::visitCallInstSink(CallInst & I)
	{
		/*DEBUG(errs() << "CALL SINK [call func]: "; I.print(errs()); errs() << "\n");
		Function *callee = I.getCalledFunction();
		if (!callee) return;

		string calleeName = callee->getName().str();

		unsigned formatPos = isFormatSink(calleeName);

		if (_FUNCTION_NOT_FORMAT != formatPos) {
			DEBUG_WITH_TYPE("saint-sinks", errs() << "[SAINT]Handling sink format string function '" << calleeName << "'\n");
			handleFormatSink(I, *callee, formatPos);
		}
		else if (_formatSinks.count(calleeName) > 0) {
			DEBUG_WITH_TYPE("saint-sinks", errs() << "[SAINT]Handling sink function '" << calleeName << "'\n");
			checkTaintedValueUse(I, *callee);
		}
         */
	}

	//**************************************************************************************

	void TaintAnalysis::visitReturnInst(ReturnInst &I) {
 
		Function *F = I.getParent()->getParent();
		//DEBUG_WITH_TYPE("saint-table", errs() << "Analyzing return instruction for " << F->getName() << "\n");
		Value *retVal = I.getReturnValue();

		if (!retVal || retVal->getType()->isVoidTy()) {
			//DEBUG_WITH_TYPE("saint-table", errs() << "Void return value for: " << F->getName() << "\n");
			return;
		}

		//DEBUG_WITH_TYPE("saint-table", errs() << "\t";retVal->print(errs());errs()<< "\n");

	}

	//**************************************************************************************

	void TaintAnalysis::visitCastInst(CastInst &I)
	{
		DEBUG(errs() << "CAST []: "; I.print(errs()); errs() << "\n");
		//TODO: Fix this. the code below hides some correct bugs warnings.
		//It also adds a lot of false positives
		Value *v = I.getOperand(0);
		if (isValueTainted(v))
            TaintedVariables.insert(&I);
	}

	//**************************************************************************************

	void TaintAnalysis::visitBinaryOperator(BinaryOperator &I)
	{
		DEBUG(errs() << "BINARYOPERATOR [r = a+b]: "; I.print(errs()); errs() << "\n");
		Value *left = I.getOperand(0);
		Value *right = I.getOperand(1);

		if (isValueTainted(right) || isValueTainted(left))
			TaintedVariables.insert(&I);
	}

	//**************************************************************************************

	void TaintAnalysis::visitVACopyInst(VACopyInst &I) {
		DEBUG(errs() << "VACOPY: "; I.print(errs()); errs() << "\n");
		Value *src = I.getSrc();
		Value *dest = I.getDest();
		if (isValueTainted(src))
			TaintedVariables.insert(dest);
	}

	//**************************************************************************************

	inline void TaintAnalysis::taintBBInstructions(BasicBlock *bb)
	{
		for (BasicBlock::iterator it = bb->begin(), itE = bb->end(); it != itE; ++it) {
			if (LoadInst *L = dyn_cast<LoadInst>(it)) {
				TaintedVariables.insert(L);
			}
			else if (StoreInst *S = dyn_cast<StoreInst>(it)) {
				TaintedVariables.insert(S->getPointerOperand());
			}
			else if (BinaryOperator *B = dyn_cast<BinaryOperator>(it)) {
				TaintedVariables.insert(B);
			}
		}
	}

	void TaintAnalysis::visitBranchInst(BranchInst &I)
	{
		//DEBUG_WITH_TYPE("saint-table", errs() << "BRANCH: ";I.print(errs());errs()<<"\n");

		if (I.isConditional()) {
			//Value *cond = I.getCondition();
			//errs() << "The condition is: "; cond->print(errs()); errs() << "\n";

			if (CmpInst *C = dyn_cast<CmpInst>(I.getCondition())) {
				Value *anOp = 0;
				for (unsigned i = 0; i < C->getNumOperands(); ++i) {
					anOp = C->getOperand(i);
					if (isValueTainted(anOp)) {
						//errs() << "Implicit taint happens because of: ";
						//anOp->dump();errs()<<"\n";

			        	bool hasElse = (DT.getNode(I.getParent())->getNumChildren() == 3);

			        	SmallVector<BasicBlock*, 8> WL;

			        	DT.getDescendants(I.getSuccessor(0), WL);
			        	for(auto bb : WL)
			        		taintBBInstructions(bb);

			        	if(hasElse)
			        	{
			        		DT.getDescendants(I.getSuccessor(1), WL);
			        		for(auto bb : WL)
			        			taintBBInstructions(bb);
			        	}
						return; //as long as the condition is tainted, the whole branch is tainted
					}
				}
			}
		}
	}
	/**
	* For handling arrays and structs
	*/
	void TaintAnalysis::visitGetElementPtrInst(GetElementPtrInst &I)
	{
		DEBUG(errs() << "GetElementPtrInst: "; I.print(errs()); errs() << "\n");
		Value *p = I.getPointerOperand();
		if (isValueTainted(p)) {
			TaintedVariables.insert(&I);
			return;
		}

		for (int i = 1; i < (int)(I.getNumOperands()); i++)
		{

			Value *Index = I.getOperand(i);
			if (isValueTainted(Index))
			{
				TaintedVariables.insert(&I);
				return;
			}
		}


	}

	void TaintAnalysis::visitSelectInst(SelectInst &I)
	{
		Value *anOp;
		for (unsigned i = 0; i < I.getNumOperands(); ++i) {
			anOp = I.getOperand(i);
			if (isValueTainted(anOp))
			{
				TaintedVariables.insert(&I);
				return;
			}
		}

	}

	void TaintAnalysis::visitCmpInst(CmpInst &I)
	{
		Value *anOp;
		for (unsigned i = 0; i < I.getNumOperands(); ++i) {
			anOp = I.getOperand(i);
			if (isValueTainted(anOp))
			{
				TaintedVariables.insert(&I);
				return;
			}
		}
	}

    void TaintAnalysis::print()
    {
        for(auto I:TaintedVariables)
        {
            I->dump();
        }
        
    }
}
