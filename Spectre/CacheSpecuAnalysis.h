#ifndef CACHE_SPECU_ANALYSIS_H
#define CACHE_SPECU_ANALYSIS_H
 
#include "llvm/ADT/SmallSet.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include <llvm/Pass.h>
#include <llvm/IR/InstVisitor.h>
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
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

namespace spectre {
struct Var{
	Value* Val;
    unsigned AddrB, AddrE; // address range, used to calculate set/line number
    unsigned LineB, LineE; //
    unsigned AgeSize;     // the number of cache lines this var can occupy
    unsigned AgeIndex;    // the starting index of <vector> Ages
    Type *ty;
    unsigned alignment;
//    Var* Pre, Next;    // pointer to other value in the same cache line if any
};

class CacheModel{
public:
//	unsigned cacheRecord[100000] = {0};
	std::set<unsigned> cacheRecord;
	unsigned CacheLineNum;
	unsigned CacheLineSize;
	unsigned CacheSetNum;
	unsigned CacheLinesPerSet;

	unsigned MaxAddr;
	vector<unsigned> Ages;
	bool MustMod;  // true: must-hit analysis; false: may-miss analysis
	ValueMap<Value*, Var*> Vars;

	//cache hit/miss info
	unsigned HitCount, MissCount;
	unsigned SpecuHitCount, SpecuMissCount;

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
            while(len--)
            {
            	size += GetTySize(stTy->getElementType(len));
            }
            return size;
        }
        else if(ty->isFloatingPointTy())
        {
        	if(ty->isHalfTy())
        		return 2;
        	if(ty->isFloatTy())
        		return 4;
        	if(ty->isDoubleTy())
        		return 8;
        	if(ty->isX86_FP80Ty())
        		return 10;
        	if(ty->isFP128Ty() | ty->isPPC_FP128Ty())
        	    return 16;
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

	void SetMaxAddr(unsigned addr)
	{
		this->MaxAddr = addr;
	}
	void SetAges(vector<unsigned> ages);
	void SetVarsMap(ValueMap<Value*, Var*> &vars);
	bool ConfigConsistent(CacheModel* model){
		if(this->CacheLineNum== model->CacheLineNum
				&& this->CacheLineSize == model->CacheLineSize
				&& this->CacheLinesPerSet == model->CacheLinesPerSet
				&& this->CacheSetNum == model->CacheSetNum)
			return true;
		else
			return false;
	}

	bool isVarPartiallyCached(Var* var)
	{
		for(int i= var->AgeIndex;i<(var->AgeIndex+var->AgeSize);++i)
		{
			if(Ages[i] < CacheLineNum)
				return true;
		}
		return false;
	}

	bool CacheConsistent(CacheModel* model){
		if(this->Vars.size() != model->Vars.size())
			return false;
		if(this->Ages.size() != model->Ages.size())
			return false;

		for(const auto &var : this->Vars)
		{
			Var *var1 = var.second;
			if(model->Vars.find(var.first) == model->Vars.end())
				return false;
			Var *var2 = model->Vars[var.first];

			if(!(var1->AgeIndex==var2->AgeIndex && var1->AgeSize==var2->AgeSize))
				return false;
		}
		return true;
	}

	unsigned GetAge(Value* var, unsigned offset = 0);
	unsigned SetAge(Value* var, unsigned age, unsigned offset = 0);
	unsigned SetAge(Value* var, unsigned age, unsigned b, unsigned e);
	CacheModel(unsigned lineSize, unsigned lineNum, unsigned setNum, bool must = true);
	unsigned Access(Value * var, unsigned offset  =0);
	unsigned Access(Value * var, bool force);
	unsigned LocateVar(Value* var, unsigned offset);
	unsigned AddVar(Value* var, Type* ty, unsigned alignment = 1);
	CacheModel* fork();
	bool equal(CacheModel* model);
	CacheModel* merge(CacheModel* mod);
	void dump(bool verbose = false);
	bool isInCache(string varName);

};
    
struct PointerLocation{
    Value* Dest;
    unsigned Offset;
    PointerLocation(Value* dest, unsigned offset):Dest(dest),Offset(offset){};
};

class CacheSpecuInfo{
public:
	unsigned Depth;
	BasicBlock* CauseBB;
	DominatorTree *DT;
	bool HasElse;
	DomTreeNode *DTIf;
	DomTreeNode *DTElse;
	BasicBlock *IfEndBB;
	BasicBlock *ElseEndBB; // bb that specu execution reach depth
	BasicBlock* MergeBB; // bb specu state should finally merge
	DomTreeNode *DTEnd;  // merge bb of two branch in CFG
	CacheModel* IfModel;
	CacheModel* ElseModel;
	unsigned Finished;  // 0: unfinished 1: specu sim finished 2: propagate finished
	unsigned IfDepth, ElseDepth;
	SmallSet<BasicBlock*, 4> WLIf; // 2 worklists to store the
	SmallSet<BasicBlock*, 4> WLElse;

	CacheSpecuInfo(BasicBlock* Cause, DominatorTree *Dt, DomTreeNode *If, DomTreeNode *Else, DomTreeNode *End, unsigned depth, bool hasElse)
				: CauseBB(Cause), DT(Dt), DTIf(If), DTElse(Else), DTEnd(End), Depth(depth), HasElse(hasElse){
		IfDepth = ElseDepth = 0;
		Finished = 0;
		IfModel = ElseModel = nullptr;
		WLIf.insert(DTIf->getBlock());
		WLElse.insert(DTElse->getBlock());
	}


	void Reset()
	{
		Finished = 0;
		IfDepth = ElseDepth = 0;
		WLIf.clear();
		WLElse.clear();
		WLIf.insert(DTIf->getBlock());
		WLElse.insert(DTElse->getBlock());

	}

    //check if bb should be speculatively execute
	// ret: 0b01 in if branch specu path
	//      0b10 in else branch specu path
	//      0b11 in both specu path
	unsigned IsSpeculative(BasicBlock* bb){
		unsigned ret = 0;
		if(this->WLIf.count(bb) && (IfDepth < Depth))
			ret |= 0x1;

		if(this->WLElse.count(bb) && (ElseDepth < Depth))
			ret |= 0x2;
		return ret; // bb is speculatively executed
	}

	int IsSpecuEntry(BasicBlock* bb)
	{
		if(DTIf->getBlock() == bb)
			return 1;
		if(DTElse->getBlock() == bb)
			return 2;
		return 0;
	}

	bool AddModel(CacheModel* model, bool If, bool cacheUpdate)
	{
		//TODO: make sure depth is not out of bound when call this function
		if(If)
		{
			if((IfModel!=nullptr) && cacheUpdate)
				IfModel->merge(model);
			else
				IfModel = model->fork();
			IfDepth++;
			return (IfDepth>=Depth);
		}
		else
		{
			if((ElseModel!=nullptr) && cacheUpdate)
				ElseModel->merge(model);
			else
				ElseModel = model->fork();
			ElseDepth++;
			return (ElseDepth>=Depth);
		}
	}
	bool IsFinished()
	{
		return (IfDepth>=Depth) && (ElseDepth>=Depth);
	}

	void dump(bool verbose = false)
	{
		dbgs() << "Specu Execution: ";
		CauseBB->print(dbgs());
		dbgs() << "If Depth: "<<IfDepth <<"; Else Depth: "<<ElseDepth<<"\n";
		if(verbose)
		{
			if(IfEndBB)
			{
				dbgs() <<"\nIf End at:"; IfEndBB->print(dbgs());
			}
			if(ElseEndBB)
			{
				dbgs() <<"\nElse End at:"; ElseEndBB->print(dbgs());
			}
			if(MergeBB)
			{
				dbgs() <<"\nMerge at:"; MergeBB->print(dbgs());
			}
		}
	}
};



class CacheSpecuAnalysis : public InstVisitor<CacheSpecuAnalysis> {
private:
	Function* F;
	DominatorTree *DT;
	PostDominatorTree *PDT;
	ValueMap<BasicBlock*, CacheModel*> cacheTrace;
	ValueMap<BasicBlock*, CacheModel*> propCacheTrace;
	ValueMap<Value*, PointerLocation*> AliasMap;
	AliasAnalysis* AA;
	SmallVector<std::pair<const BasicBlock*,const BasicBlock*>, 8> backEdges;
	unsigned loopBound[20];
	bool runSpecu = false;
	unsigned HitSpecuDepth =0, MissSpecuDepth =0;
	unsigned MergeOption = 0;

	std::map<std::pair<const BasicBlock*,const BasicBlock*>, CacheModel*> wideningMap;
	std::map<std::pair<const BasicBlock*,const BasicBlock*>, int> wideningMapCount;
	vector<CacheSpecuInfo*> SpecuInfo;

	std::map<const BasicBlock*, int> result;
	int missNum;
	bool cacheChanged;
public:
	void dump(int mod);
	bool wideningOp(CacheModel* last, CacheModel* current);

	CacheModel *model;  //tmp pointer to current model
	CacheSpecuAnalysis(Function &F, DominatorTree &DT,PostDominatorTree &PDT, AliasAnalysis* AA, unsigned, unsigned, unsigned, unsigned, unsigned);
	inline bool IsBackEdge(BasicBlock* from,BasicBlock* to)
	{
		return (std::find(this->backEdges.begin(),
								this->backEdges.end(),
								std::pair<const BasicBlock*,const BasicBlock*>(from, to))
		        != this->backEdges.end());
	}
	bool SpecuSim(BasicBlock* from,BasicBlock* to, CacheModel* init = nullptr);
	unsigned GetSpecuInfo(CacheSpecuInfo* &specuInfo, BasicBlock* bb);
	BasicBlock* SpecuPropagation(BasicBlock* startBB, BasicBlock* termBB, CacheModel* initModl);

	bool CacheSim(Instruction* from, Instruction* dest,Instruction* to);
	bool IsValueInCache(Instruction* inst);
	bool GetInstCacheRange(Value* inst, GlobalVariable *&GV, unsigned& offset_b, unsigned& offset_e);
    unsigned IsAliasTo(Value* from, Value* &to, unsigned &offset);
    vector<Value*> GetAlias(Value * val, unsigned offset=0);
	void InitModel();
	void InitModel(GlobalVariable* var, unsigned b, unsigned e);
	void ExtractGEPC(ConstantExpr* source, Value* &target, unsigned &offset);
	//void taintBBInstructions(BasicBlock *bb);
	void visitAllocaInst(AllocaInst &I);
	void visitLoadInst(LoadInst &I);
    void visitBitCastInst(BitCastInst &I);
	void visitStoreInst(StoreInst &I);
	void visitCallInst(CallInst &I);
	void visitPHINode(PHINode &I);
	void visitSelectInst(SelectInst &I);
    void visitIntrinsicInst(IntrinsicInst &I);
	void visitVACopyInst(VACopyInst &I);

	void visitBranchInst(BranchInst &I);

	void visitGetElementPtrInst(GetElementPtrInst &I);
	//PointerLocation* aliasGetElementPtrInst(GetElementPtrInst &I);
	void visitInstruction(Instruction &I);
};
}
#endif
