#ifndef CACHE_ANALYSIS_H
#define CACHE_ANALYSIS_H
 
#include "llvm/ADT/SmallSet.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include <llvm/Pass.h>
#include <llvm/IR/InstVisitor.h>
#include "llvm/IR/Dominators.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/IR/Value.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/IR/CFG.h"
#define CACHE_LINE_NUM 32
#define CACHE_LINE_SIZE 16
#define ARCH_SIZE 8 // 64-bit
using namespace std;
using namespace llvm;

namespace cache {

class CacheModel{
public:
	unsigned CacheLineNum;
	unsigned CacheLineSize;
	unsigned MaxAddr;
	vector<unsigned> Ages;
	vector<Value*> Vars;
	void SetMaxAddr(unsigned addr)
	{
		this->MaxAddr = addr;
	}
	void SetMap(ValueMap<Value*, unsigned> &from, ValueMap<Value*, unsigned> &to);
	void SetAges(vector<unsigned> ages);
	void SetVars(vector<Value*> vars);
	ValueMap<Value*, unsigned> AddrMap;
	ValueMap<Value*, unsigned> SizeMap;
	static unsigned GetTySize(Type *ty)
    {
        Type *eleTy;
        unsigned len;
        
        if (ty->isArrayTy())
        {
            ArrayType *arrayTy = dyn_cast<ArrayType>(ty);
            len = arrayTy->getNumElements();
            eleTy = arrayTy->getElementType();
            return len*GetTySize(eleTy);
        }
        else if (ty->isPointerTy())
        {
            //PointerType *pointerTy = dyn_cast<PointerType>(ty);
            //len = 1;
            // eleTy = pointerTy->getElementType();
            //return len*GetTySize(eleTy);
        	return ARCH_SIZE;
        }
        else if (ty->isVectorTy())
        {
            VectorType *vectorTy = dyn_cast<VectorType>(ty);
            len = vectorTy->getNumElements();
            eleTy = vectorTy->getElementType();
            return len*GetTySize(eleTy);
        }
        else if (ty->isIntegerTy())
        {
            IntegerType *intTy = dyn_cast<IntegerType>(ty);
            return (intTy->getBitWidth())/8;
        }
        else if (ty->isStructTy())
        {
            unsigned size = 0;
            StructType *stTy = dyn_cast<StructType>(ty);
            len = stTy->getStructNumElements();
            for (StructType::element_iterator it = stTy->element_begin(); it != stTy->element_end(); ++it)
            {
                size += GetTySize((Type*)it);
            }
            return size;
        }
        return 0;
    }

	static int GEPInstPos(GetElementPtrInst &I, unsigned &from, unsigned &to)
	{
		Value* dest = I.getPointerOperand();
		unsigned size =0;
		uint64_t index;
		Type* ty;
		from = to =0;



		ty = dest->getType();
		if (ConstantExpr *GEPC = dyn_cast<ConstantExpr>(dest))
		{
			if(GEPC->isGEPWithNoNotionalOverIndexing())
			{
				GetElementPtrInst *GEP = cast<GetElementPtrInst>(GEPC->getAsInstruction());
				CacheModel::GEPInstPos(*GEP, from, to);
				delete(GEP);
				to =0;
			}
			else
				return -1;
		}



		for(unsigned i=1; i<= I.getNumIndices(); i++)
		{
			if (ConstantInt *CI = dyn_cast<ConstantInt>(I.getOperand(i)))
			{
				index = CI->getZExtValue();
			}
			else
			{
				size = CacheModel::GetTySize(ty);
				to = from + size -1;
				return 0; //gep is a range, none determinized location
			}

			if(SequentialType* seqTy = dyn_cast<SequentialType>(ty))
			{
				ty = seqTy->getElementType();
				size = CacheModel::GetTySize(ty);
				from += index*size;
			}
			else if(StructType* stTy = dyn_cast<StructType>(ty))
			{
				for(unsigned ele=0; ele < index; ++ele)
				{
					size = CacheModel::GetTySize(stTy->getElementType(ele));
					from += size;
				}
			}
			else{
				dbgs() << I <<"\n\tGep indice "<< i <<" parse error:" << "\n\ttype is" << *ty;
				to = from;
				return -1;
			}
		}
		if(to >0)
			to -= 1;
		return 1; //gep is a specific location

	}
	unsigned IsInCache(Value * var, unsigned offset);
	unsigned GetAge(Value* var, unsigned offset = 0);
	unsigned SetAge(Value* var, unsigned age, unsigned offset = 0);
	unsigned SetAge(Value* var, unsigned age, unsigned b, unsigned e);
	CacheModel(int lineSize, int lineNum);
	unsigned Access(Value * var, unsigned offset, bool may = false);
	unsigned Access(Value * var, unsigned begin, unsigned end);
	unsigned LocateVar(Value* var, unsigned offset);
	unsigned AddVar(Value* var, Type* ty, unsigned alignment = 1);
	CacheModel* fork();
	CacheModel* merge(CacheModel* mod, bool may = false);
	void dump();

};
    
struct PointerLocation{
    Value* Dest;
    unsigned Offset;
    PointerLocation(Value* dest, unsigned offset):Dest(dest),Offset(offset){};
};

class CacheAnalysis : public InstVisitor<CacheAnalysis> {
private:
	CacheModel *model;
	Function* F;
	DominatorTree *DT;
	ValueMap<BasicBlock*, CacheModel*> cacheModel;
	ValueMap<Value*, PointerLocation*> AliasMap;
	AliasAnalysis* AA;
	Instruction* beginInst;
	Instruction* endInst;
	BasicBlock* beginBB;
	BasicBlock* endBB;

public:
	CacheAnalysis(Function &F, DominatorTree &DT,AliasAnalysis* AA, unsigned lineSize, unsigned lineNum);

	bool CacheSim(Instruction* from, Instruction* dest,Instruction* to);
	bool IsValueInCache(Instruction* inst);
	bool GetInstCacheRange(Value* inst, GlobalVariable *&GV, unsigned& offset_b, unsigned& offset_e);
    unsigned IsAliasTo(Value* from, Value* &to, unsigned &offset);
    vector<Value*> GetAlias(Value * val, unsigned offset=0);
	void InitModel();
	void InitModel(GlobalVariable* var, unsigned b, unsigned e);
	
	CacheModel* visitEntrance(BasicBlock *bb);
	//void taintBBInstructions(BasicBlock *bb);
	void visitAllocaInst(AllocaInst &I);
	void visitLoadInst(LoadInst &I);
    void visitBitCastInst(BitCastInst &I);
	void visitStoreInst(StoreInst &I);

	void visitVACopyInst(VACopyInst &I);

	void visitBranchInst(BranchInst &I);

	void visitGetElementPtrInst(GetElementPtrInst &I);
	//PointerLocation* aliasGetElementPtrInst(GetElementPtrInst &I);
	void visitInstruction(Instruction &I);
};
}
#endif
