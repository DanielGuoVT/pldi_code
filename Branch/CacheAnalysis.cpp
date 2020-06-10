//===- Branch.cpp - Transform branches dependent on secrete data ---------------===//
//   - 10/04 treat all input as sensitive
// 
//===---------------------------------------------------------------------------===//

#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/User.h"
#include "CacheAnalysis.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/CFG.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/IR/Constants.h"
#include <deque>
using namespace llvm;
using namespace std;
#define DEBUG_TYPE "branch"
namespace cache {

void CacheModel::SetMap(ValueMap<Value*, unsigned> &from, ValueMap<Value*, unsigned> &to)
{
	for (ValueMap<Value*, unsigned>::iterator i = from.begin(); i != from.end(); ++i)
	{
		to[i->first] = i->second;
	}
}

void CacheModel::SetAges(vector<unsigned> ages)
{
	this->Ages = ages;
}

void CacheModel::SetVars(vector<Value*> vars)
{
	this->Vars = vars;
}

CacheModel::CacheModel(int lineSize, int lineNum)
{
	this->CacheLineNum = lineNum;
	this->CacheLineSize = lineSize;
	this->MaxAddr = 0;
    if(Ages.size()==0)
        Ages.push_back(CacheLineNum);
}


unsigned CacheModel::LocateVar(Value * var, unsigned offset)
{
	if(offset == -1)
		offset =0;

	ValueMap<Value*, unsigned>::iterator v = this->AddrMap.find(var);
	if (v == this->AddrMap.end())
		return -1;
	else
		return (v->second + offset)/CacheLineSize;
}


unsigned CacheModel::GetAge(Value * var, unsigned offset)
{
	unsigned CacheLoc = LocateVar(var, offset);

	if (CacheLoc == (unsigned)-1 || CacheLoc >= Ages.size())
		return -1;
	else
		return Ages[CacheLoc];
}

unsigned CacheModel::SetAge(Value * var, unsigned age, unsigned offset)
{
	unsigned b =0;

	if(offset == -1)
	{
		if (this->SizeMap.find(var)== this->SizeMap.end())
			return -1;
		offset = 0;
		b = this->SizeMap[var];
	}

	unsigned CacheLoc = LocateVar(var, offset);

	if (CacheLoc == (unsigned)-1 || CacheLoc >= Ages.size())
		return -1;
	
	for(int i=0; i<= b; ++i)
	{
		Ages[CacheLoc+i] = age;
	}

	return age;
}

unsigned CacheModel::Access(Value * var, unsigned begin, unsigned end)
{
	unsigned b = LocateVar(var, begin);
	unsigned e = LocateVar(var, end);

	if (b >= Ages.size() || e >= Ages.size())
		return -1;

	for(; b<= e; ++b)
	{
		unsigned age = Ages[b];
		Ages[b] = 0;

		for (unsigned i = 0; i < Ages.size(); ++i)
		{
			if (Ages[i] <= age && i != b)
			{
				if(Ages[i]<CacheLineNum)
					Ages[i]++;
			}
		}
	}

}




unsigned CacheModel::AddVar(Value *var, Type *ty, unsigned alignment)
{
	ValueMap<Value*, unsigned>::iterator v = this->AddrMap.find(var);

	if (v == this->AddrMap.end())
	{
		unsigned size = GetTySize(ty);
		if(size ==0)
			return MaxAddr;
		if(alignment ==0)
			alignment =1;

		if (MaxAddr%alignment)
		{
			MaxAddr = (MaxAddr / alignment + 1)*alignment;
			unsigned newSize = (MaxAddr-1)/CacheLineSize -
				this->AddrMap[this->Vars.back()]/CacheLineSize + 1;

			for(unsigned i=0; i< (newSize- this->SizeMap[this->Vars.back()]);++i)
				this->Ages.push_back(CacheLineNum);

			this->SizeMap[this->Vars.back()] = newSize;

		}
		this->AddrMap[var] = MaxAddr;
		this->Vars.push_back(var);
        
        unsigned b = (MaxAddr+size-1)/CacheLineSize - MaxAddr/CacheLineSize +1;

//        if((MaxAddr+size)%CacheLineSize)
//        	b+=1;

        for(unsigned i=0; i< b;++i)
            this->Ages.push_back(CacheLineNum);
        this->SizeMap[var]=b;
		MaxAddr += size;
		return MaxAddr;
	}
	return v->second;
}

unsigned CacheModel::Access(Value * var, unsigned offset, bool may)
{

	unsigned CacheLoc = LocateVar(var, offset);
	if (CacheLoc == (unsigned)-1)
		return -1;

	if(CacheLoc >= Ages.size())
	{
		errs() << "Fatal error when locate variable in cache analysis:";
		var->dump();
		errs() << "@Function CacheModel::Access().\n";
		return -1;
	}

	// if offset is unknown
	if(offset == -1)
	{
		unsigned size = this->SizeMap[var];
		unsigned locEnd = CacheLoc+size-1;

		for(;CacheLoc< locEnd; ++CacheLoc)
		{
			// choose untouched cache line if possible
			if(Ages[CacheLoc] >= CacheLineNum)
				break;
		}
	}



	unsigned age = Ages[CacheLoc];
	Ages[CacheLoc] = 0;

	for (unsigned i = 0; i < Ages.size(); ++i)
	{
		if (Ages[i] <= age && i != CacheLoc)
		{
			if (Ages[i] == age && !may)
				continue;
			if(Ages[i]<CacheLineNum)
                Ages[i]++;
		}
	}

	// return 1, if var in cache, else 0. use return value to count cache hits/miss
	return age<CacheLineNum? 1:0;
}

//unsigned CacheModel::IsInCache(Value * var, unsigned offset)
//{
//
//	unsigned CacheLoc = LocateVar(var, offset);
//	if (CacheLoc == (unsigned)-1)
//		return -1;
//
//	// if offset is unknown
//	if(offset == -1)
//	{
//		unsigned size = this->SizeMap[var];
//		for(;CacheLoc< CacheLoc+size ; ++CacheLoc)
//		{
//			// choose untouched cache line if possible
//			if(Ages[CacheLoc] >= CacheLineNum)
//				break;
//		}
//	}
//
//	unsigned age = Ages[CacheLoc];
//	Ages[CacheLoc] = 0;
//
//	for (unsigned i = 0; i < Ages.size(); ++i)
//	{
//		if (Ages[i] <= age && i != CacheLoc)
//		{
//			if (Ages[i] == age && !may)
//				continue;
//			if(Ages[i]<CacheLineNum)
//                Ages[i]++;
//		}
//	}
//
//	// return 1, if var in cache, else 0. use return value to count cache hits/miss
//	return age<CacheLineNum? 1:0;
//}


CacheModel* CacheModel::fork()
{
	CacheModel *ret = new CacheModel(this->CacheLineSize,this->CacheLineNum);
	ret->SetMaxAddr(this->MaxAddr);
	ret->SetMap(this->AddrMap, ret->AddrMap);
	ret->SetMap(this->SizeMap, ret->SizeMap);
	ret->SetAges(this->Ages);
	ret->SetVars(this->Vars);
	return ret;
}

CacheModel* CacheModel::merge(CacheModel *mod, bool may)
{
	if (may)
	{
		for (ValueMap<Value*, unsigned>::iterator i = this->AddrMap.begin();
			i != this->AddrMap.end(); ++i)
		{
			unsigned k = mod->GetAge(i->first);
			if (k == -1)
				continue;

			unsigned j = this->GetAge(i->first);
			unsigned min = j > k ? k : j;
			this->SetAge(i->first, min);
		}

		for (ValueMap<Value*, unsigned>::iterator i = mod->AddrMap.begin();
			i != mod->AddrMap.end(); ++i)
		{
			unsigned j = this->GetAge(i->first);
			unsigned k = mod->GetAge(i->first);
			if (j == -1)
			{
				this->AddVar(i->first, i->first->getType());
				this->SetAge(i->first, k);
			}
			else
			{
				unsigned min = j > k ? k : j;
				this->SetAge(i->first, min);
			}
		}
	}
	else
	{
		for (ValueMap<Value*, unsigned>::iterator i = this->AddrMap.begin();
			i != this->AddrMap.end(); ++i)
		{
			unsigned j = this->GetAge(i->first);
			unsigned k = mod->GetAge(i->first);
			unsigned max = j > k ? j : k;

			if (max == (unsigned)-1)
				max = CacheLineNum;

			this->SetAge(i->first, max);
		}

		for (ValueMap<Value*, unsigned>::iterator i = mod->AddrMap.begin();
			i != mod->AddrMap.end(); ++i)
		{
			unsigned j = this->GetAge(i->first);
			unsigned k = mod->GetAge(i->first);
			unsigned max = j > k ? j : k;

			if (j == (unsigned)-1)
			{
				this->AddVar(i->first, i->first->getType());
			}
			else
			{
				this->SetAge(i->first, max);
			}

		}
	}
    return this;
}


void CacheModel::dump()
{
	for (const auto &v : this->Vars)
	{
		unsigned int linesize = this->SizeMap[v];

		if(v->hasName())
			dbgs() << v->getName();
		else
		{
			v->dump();
		}
		dbgs() << "\toccupy "<< linesize << " lines at "<<this->AddrMap[v]<<" : ";

		unsigned int sl = this->AddrMap[v]/CacheLineSize;

		for(int i=0;i<linesize;++i)
		{
			dbgs() << Ages[sl++]<<", ";
		}
		dbgs() <<"\n";
	}
}

CacheAnalysis::CacheAnalysis(Function &F, DominatorTree &DT, AliasAnalysis* AA, unsigned lineSize, unsigned lineNum)
{
	this->AA = AA;
	this->F = &F;
	this->DT = &DT;
	this->model = new CacheModel(lineSize, lineNum);
}

bool CacheAnalysis::IsValueInCache(Instruction* inst)
{
	Value* loadPointer;
	GlobalVariable *GV;
	unsigned offset_b=0, offset_e=0;

	if (LoadInst *load = dyn_cast<LoadInst>(inst))
		loadPointer = load->getPointerOperand();
	else
		return false;

	if(!GetInstCacheRange(loadPointer, GV, offset_b, offset_e))
		return false;

	unsigned CacheLoc = this->model->LocateVar(GV, offset_b);
	unsigned CacheLoc_e = this->model->LocateVar(GV, offset_e);
	if (CacheLoc == (unsigned)-1)
	{
		//DEBUG(dbgs() << "Cannot find Value when check in cache: "; GV->print(dbgs()); dbgs() << "\n");
		return false;
	}

	for (; CacheLoc <= CacheLoc_e; ++CacheLoc)
	{
		if(this->model->Ages[CacheLoc]>=this->model->CacheLineNum)
			return false;
	}

	return true;
}

bool CacheAnalysis::GetInstCacheRange(Value* inst, GlobalVariable *&GV, unsigned& offset_b, unsigned& offset_e)
{
	GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(inst);
	offset_b = 0;
	offset_e = 0;

	while(GEP)
	{
		if (ConstantExpr *GEPC = dyn_cast<ConstantExpr>(GEP->getPointerOperand()))
		{
			if(GEPC->isGEPWithNoNotionalOverIndexing())
			{
				GetElementPtrInst *GEPCGEP = cast<GetElementPtrInst>(GEPC->getAsInstruction());
				GV = dyn_cast<GlobalVariable>(GEPCGEP->getPointerOperand());
				delete(GEPCGEP);
				if(!GV)
					return false;
			}
			else
				return false;


			if(CacheModel::GEPInstPos(*GEP, offset_b, offset_e) == -1)
			{
				return false;
			}
			return true;

		}
		else if (isa<GetElementPtrInst>(GEP->getPointerOperand()))
		{
			GEP = cast<GetElementPtrInst>(GEP->getPointerOperand());
			continue;
		}
		else if(isa<GlobalVariable>(GEP->getPointerOperand()))
		{
			GV = cast<GlobalVariable>(GEP->getPointerOperand());
			offset_e = CacheModel::GetTySize(GV->getValueType())-1;
			return true;
		}
		else
		{
			return false;
		}



	}


}



bool CacheAnalysis::CacheSim(Instruction* from, Instruction* dest,Instruction* to)
{

	GlobalVariable *GV;

	unsigned offset_b, offset_e;
	BasicBlock* bb_b = from->getParent();
	BasicBlock* bb_e = to->getParent();

	this->DT->recalculate(*(this->F));

	if(bb_b != bb_e)
	{
		if(!this->DT->dominates(bb_b, bb_e))
			return false; // if bb_b does not dominate bb_e, treat it cache miss anyway
	}


	if(GetInstCacheRange(dest, GV, offset_b, offset_e))
	{
		if(from->hasName())
			this->InitModel(GV, offset_b, offset_e);
		else
			this->model->Access(GV,-1);
	}
	else
	{
		DEBUG(dbgs() << "Cache Sim failed at init cache: "; dest->print(dbgs()); dbgs() << "\n");
		return false;
	}




	bool flag = false;
	if(bb_b == bb_e)
	{
		for (BasicBlock::iterator i = bb_b->begin(); i != bb_b->end(); ++i)
		{
			if(&*i == to)
				break;

			if(flag)
				this->visit(*i);

			if(&*i == from)
				flag =  true;
		}
		return true;
	}


	for (BasicBlock::iterator i = bb_b->begin(); i != bb_b->end(); ++i)
	{
		if(flag)
			this->visit(*i);

		if(&*i == from)
			flag =  true;
	}

	this->cacheModel[bb_b] = this->model;

	SmallVector<BasicBlock*, 128> BBL;
	std::deque<BasicBlock*> wl;
	DenseMap<const BasicBlock*, bool> VisitedBB;
	VisitedBB[bb_b] = true;
	VisitedBB[bb_e] = true;
	//BBL.push_back(bb_e);


	for (auto it = succ_begin(bb_b), et = succ_end(bb_b); it != et; ++it)
	{
		BasicBlock* succ = *it;
		if (llvm::isPotentiallyReachable(succ, bb_e, DT) && succ!=bb_e)
			wl.push_back(succ);
	}


	while(!wl.empty())
	{
		BasicBlock* bb = wl.front();
		wl.pop_front();
		bool predVisited = true;

		for (auto it = pred_begin(bb), et = pred_end(bb); it != et; ++it)
		{
			BasicBlock* pred = *it;
			if(VisitedBB.find(pred) == VisitedBB.end())
			{
				wl.push_back(bb);
				predVisited = false;
				break;
			}
		}

		if(predVisited)
		{
			VisitedBB[bb] = true;
			BBL.push_back(bb);
		}

		for (auto it = succ_begin(bb), et = succ_end(bb); it != et; ++it)
		{
		  BasicBlock* succ = *it;
		  if(VisitedBB.find(succ) == VisitedBB.end() &&
				  (llvm::isPotentiallyReachable(succ, bb_e, DT)) &&
				  (succ!=bb_e))
		  {
			  wl.push_back(succ);
		  }
		}
	}

	CacheModel* preModel = nullptr;
	for(auto b = BBL.begin(), e = BBL.end(); b!=e; ++b)
	{
		BasicBlock* bb = *b;

		preModel = nullptr;
		for (auto it = pred_begin(bb), et = pred_end(bb); it != et; ++it)
		{
			if(preModel)
				preModel->merge(this->cacheModel[*it]);
			else
				preModel = this->cacheModel[*it]->fork();
		}

		if(preModel)
			this->model = preModel;
		else
		{
			DEBUG(dbgs() << "error: Cannot get cache model from BB's predessors.\n"; bb->print(dbgs()););
			return  false;
		}
	    this->visit(bb);
	    this->cacheModel[bb] = this->model;
	}

	preModel = nullptr;
	for (auto it = pred_begin(bb_e), et = pred_end(bb_e); it != et; ++it)
	{
		if(preModel)
			preModel->merge(this->cacheModel[*it]);
		else
			preModel = this->cacheModel[*it]->fork();
	}

	if(preModel)
		this->model = preModel;
	else
	{
		DEBUG(dbgs() << "error: Cannot get cache model from end BB's predessors.\n");
		return false;
	}

	for (BasicBlock::iterator i = bb_e->begin(); i != bb_e->end(); ++i)
	{
		if(&*i == to)
			break;
		this->visit(*i);
	}

	// can delete this->cacheModel here, only keep current model is enough
	return true;
}








    
unsigned CacheAnalysis::IsAliasTo(Value* from, Value* &to, unsigned &offset)
{
    offset = 0;
    to = from;
    auto dest = AliasMap.find(from);

    while( dest != AliasMap.end())
    {
    	if(dest->second->Offset == (unsigned)-1 || offset==(unsigned)-1)
    		offset = dest->second->Offset;
    	else
    		offset += dest->second->Offset;
    	to = dest->second->Dest;
    	dest = AliasMap.find(to);
    }
    return 1;

//    unused code
//    GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(from);
//    if(GEP)
//    {
//        Value* val = GEP->getPointerOperand();
//        if (this->model->AddrMap.find(val) != this->model->AddrMap.end())
//            to = val;
//        else{
//            for (const auto &v : this->model->AddrMap)
//            {
//                AliasResult R = this->AA->alias(from, v.first);
//                if (R != AliasResult::NoAlias)
//                {
//                    to = v.first;
//                }
//            }
//        }
//        ConstantInt* index = dyn_cast<ConstantInt>(GEP->getOperand(GEP->getNumIndices()));
//        if(index)
//            offset = index->getZExtValue();
//        return 0;
//    }
//	else
//    {
//        if (this->model->AddrMap.find(from) != this->model->AddrMap.end())
//            to = from;
//        else{
//            GetAlias(from);
//            for (const auto &v : this->model->AddrMap)
//            {
//                AliasResult R = this->AA->alias(from, v.first);
//                if (R != AliasResult::NoAlias)
//                {
//                    to = v.first;
//                    return 0;
//                }
//            }
//        }
//    }
}

    
vector<Value*> CacheAnalysis::GetAlias(Value * val, unsigned offset)
{
    vector<Value*> aas;
    dbgs() << "The alias of\n\t";
    val->dump();
    dbgs() << "are";
    for (const auto &v : this->model->AddrMap)
    {
        AliasResult R = this->AA->alias(val, v.first);
        if (R != AliasResult::NoAlias)
        {
        	dbgs() << R;
            v.first->dump();
            aas.push_back(v.first);
        }
    }
    return aas;
}




void CacheAnalysis::InitModel()
{
	Module *module = this->F->getParent();
	for (Module::global_iterator i = module->global_begin();
		i != module->global_end(); ++i)
	{
		GlobalVariable &v = *i;
		unsigned alignment = v.getAlignment();
		Type *ty = v.getValueType();
		//errs()<< "\nGV " <<v.getName()<<" has type:"; ty->print(errs());
		this->model->AddVar(&v, ty, alignment);
	}
} 

void CacheAnalysis::InitModel(GlobalVariable* var, unsigned begin, unsigned end)
{
	this->model->Access(var, begin, end);
}


CacheModel* CacheAnalysis::visitEntrance(BasicBlock * bb)
{
	CacheModel* preModel = nullptr;
	for (auto it = pred_begin(bb), et = pred_end(bb); it != et; ++it)
	{
		if (this->cacheModel.find(*it) == this->cacheModel.end())
			this->visitEntrance(*it);

		if(preModel)
			preModel->merge(preModel);
		else
			preModel = this->cacheModel[*it]->fork();
	}
	if(preModel)
		this->model = preModel;

    this->visit(bb);
    this->cacheModel[bb] = this->model;
}

void CacheAnalysis::visitLoadInst(LoadInst &I)
{
	Value* var = I.getPointerOperand();
    Value* to;
    unsigned offset;
    unsigned hit;
    
    this->IsAliasTo(var, to, offset);
    hit = this->model->Access(to, offset);
    //dbgs() << "Access value" << *to << "@" <<offset << " : "<< (int)hit << "\n";

}


void CacheAnalysis::visitAllocaInst(AllocaInst &I)
{
	unsigned alignment = I.getAlignment();
	Type *ty = I.getAllocatedType();
	this->model->AddVar(&I, ty, alignment);
}

void CacheAnalysis::visitStoreInst(StoreInst &I)
{
	if(I.getValueOperand()->getType()->isPointerTy()
       && I.getPointerOperand()->getType()->getContainedType(0)->isPointerTy())
    {
        AliasMap[I.getPointerOperand()] = new PointerLocation(I.getValueOperand(),0);
    }
}



void CacheAnalysis::visitVACopyInst(VACopyInst &I)
{

}

void CacheAnalysis::visitBranchInst(BranchInst &I)
{

}

void CacheAnalysis::visitBitCastInst(BitCastInst &I)
{
    this->AliasMap[&I] = new PointerLocation(I.getOperand(0),0);
}



    
void CacheAnalysis::visitGetElementPtrInst(GetElementPtrInst &I)
{
	Value* dest = I.getPointerOperand();
    unsigned offset =0, from, to;
    uint64_t index;
    Type* ty;

    if (ConstantExpr *GEPC = dyn_cast<ConstantExpr>(dest))
    {
    	if(GEPC->isGEPWithNoNotionalOverIndexing())
    	{
    		GetElementPtrInst* GEP = cast<GetElementPtrInst>(GEPC->getAsInstruction());
//    		if(!CacheModel::GEPInstPos(*GEP, from, to))
//    		{
//    			this->AliasMap[&I] = new PointerLocation(dest,-1);
//    			delete(GEP);
//    			return;
//    		}
    		dest = GEP->getPointerOperand();
    		delete(GEP);
    	}
    }

    offset = from;

	if (!CacheModel::GEPInstPos(I, from, to))
    {
    	this->AliasMap[&I] = new PointerLocation(dest,-1);
    	return;
    }
    
    this->AliasMap[&I] = new PointerLocation(dest,from);
}

void CacheAnalysis::visitInstruction(Instruction & I)
{

	

}




}
















