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
#include "CacheSpecuAnalysis.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/CFG.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/IR/Constants.h"
#include <deque>
using namespace llvm;
using namespace std;
#define DEBUG_TYPE "spectre"
namespace spectre{


void CacheModel::SetAges(vector<unsigned> ages)
{
	this->Ages = ages;
}

void CacheModel::SetVarsMap(ValueMap<Value*, Var*> &vars)
{
	for(const auto &i : vars)
		this->Vars[i.first] = i.second;
}

CacheModel::CacheModel(unsigned lineSize, unsigned lineNum, unsigned setNum, bool must)
{
	auto isPowerOf2 = [](unsigned x)->bool{return (x&(x-1))==0;};
	if(!(isPowerOf2(lineSize) && isPowerOf2(setNum)) && (lineNum%setNum ==0))
		errs()<<"Fatal: cache configuration invalid!\n";

	CacheLineNum = lineNum;
	CacheLineSize = lineSize;
	CacheSetNum = setNum;
	CacheLinesPerSet = lineNum/setNum;
	MustMod = must;
	MaxAddr = 0;
	HitCount = MissCount = SpecuHitCount = SpecuMissCount = 0;
}


unsigned CacheModel::LocateVar(Value * var, unsigned offset)
{
	if(offset == -1)
		offset =0;
	if(this->Vars.find(var) == this->Vars.end())
		return -1;

	return (this->Vars[var]->AddrB+offset)/CacheLineSize;
}


unsigned CacheModel::GetAge(Value * var, unsigned offset)
{
	return offset;
}

unsigned CacheModel::SetAge(Value * var, unsigned age, unsigned offset)
{
	return age;
}

unsigned CacheModel::Access(Value * var, bool force)
{
	if (!force)
		return 1;
	// this is used to force access a variable, do not use in normal way.
	static int age = 0;
	for(int i = (this->Vars[var]->AgeIndex + this->Vars[var]->AgeSize)-1; i >= (int)(this->Vars[var]->AgeIndex); --i)
	{
		Ages[i] = age;
		age ++;
	}
	return 0;
}

unsigned CacheModel::AddVar(Value *var, Type *ty, unsigned alignment)
{
	if(this->Vars.find(var) != this->Vars.end())
		return 1;

	unsigned size = GetTySize(ty);
	if(size ==0)
		return 1;
	if(alignment ==0)
		alignment =1;
	Var* newVar =new Var{};;
	if (MaxAddr%alignment)
		MaxAddr = (MaxAddr / alignment + 1)*alignment;

	newVar->AddrB = MaxAddr;
	newVar->AddrE = MaxAddr + size -1;
	MaxAddr = MaxAddr +size;
	newVar->Val = var;
	newVar->ty = ty;
	newVar->alignment= alignment;

	unsigned lineB = newVar->AddrB/CacheLineSize;
	unsigned lineE = newVar->AddrE/CacheLineSize;

	newVar->AgeIndex = lineB;
	newVar->AgeSize = lineE - lineB + 1;
	newVar->LineB = lineB % CacheLineNum;
	newVar->LineE = lineE % CacheLineNum;
	while(Ages.size() < lineE+1)
	{
		Ages.push_back(CacheLinesPerSet);
	}

	this->Vars[var] = newVar;
	return 0;

}

unsigned CacheModel::Access(Value * var, unsigned offset)
{
	if(this->Vars.find(var) == this->Vars.end())
	{
//		errs() << "Fatal: try to access variable not been added!\n";
		return 1;
	}

	// if offset is unknown, chose the line uncached if possible
	unsigned CacheLoc = -1;
	if(offset == -1)
		offset = 0;


	if(offset == -1)
	{
		for(int i = this->Vars[var]->AgeIndex; i < (this->Vars[var]->AgeIndex + this->Vars[var]->AgeSize); i++)
		{
			if(Ages[i] >= CacheLinesPerSet)
			{
				CacheLoc = i;
				break;
			}
		}
		if(CacheLoc == (unsigned)-1)
			CacheLoc = this->Vars[var]->AddrB/CacheLineSize;
	}
	else{
		unsigned addr = this->Vars[var]->AddrB + offset;
		if(addr > this->Vars[var]->AddrE)
		{
//			errs() << "Fatal: try to access variable offset out of bound!\n";
			return 2;
		}
		CacheLoc = addr/CacheLineSize;
	}

	if(CacheLoc >= Ages.size())
	{
		errs() << "Fatal error when locate variable in cache analysis:";
		var->dump();
		errs() << "@Function CacheModel::Access().\n";
		return -1;
	}



	unsigned age = Ages[CacheLoc];
	unsigned SetNum = CacheLoc%CacheSetNum;
	if(cacheRecord.find(CacheLoc) == cacheRecord.end())
		cacheRecord.insert(CacheLoc);

	for (unsigned i = SetNum; i < Ages.size(); i+=CacheSetNum)
	{
		if(i == CacheLoc)
			Ages[CacheLoc] = 0;
		else if (Ages[i] <= age)
		{
			if (Ages[i] == age && MustMod)
				continue;
			if(Ages[i]<CacheLinesPerSet)
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
	CacheModel *ret = new CacheModel(this->CacheLineSize,this->CacheLineNum, this->CacheSetNum, this->MustMod);
	ret->SetMaxAddr(this->MaxAddr);
	ret->SetVarsMap(this->Vars);
	ret->SetAges(this->Ages);
	ret->HitCount = this->HitCount;
	ret->MissCount = this->MissCount;
	ret->SpecuHitCount = this->SpecuHitCount;
	ret->SpecuMissCount = this->SpecuMissCount;
	ret->cacheRecord = this->cacheRecord;

	return ret;
}


bool CacheModel::equal(CacheModel* model)
{
	//TODO: implement
	return true;
}
CacheModel* CacheModel::merge(CacheModel *mod)
{
	if(mod == nullptr)
		return this;
	if (MustMod)
	{
		for(const auto &var : mod->Vars)
		{
			Value *val = var.first;
			if(this->Vars.find(val) == this->Vars.end())
			{
				this->AddVar(val,var.second->ty, var.second->alignment);
				for(int i=0; i< mod->Vars[val]->AgeSize; i++)
				{
//					unsigned modAge = mod->Ages[mod->Vars[val]->AgeIndex+i];
					this->Ages[this->Vars[val]->AgeIndex+i] = CacheLinesPerSet;
				}
				continue;
			}

			for(int i=0; i< mod->Vars[val]->AgeSize; i++)
			{
				unsigned modAge = mod->Ages[mod->Vars[val]->AgeIndex+i];
				unsigned thisAge = this->Ages[this->Vars[val]->AgeIndex+i];
				thisAge = thisAge > modAge ? thisAge : modAge;
				this->Ages[this->Vars[val]->AgeIndex+i] = thisAge;
			}
		}
		for(const auto &var : this->Vars)
		{
			Value *val = var.first;
			if(mod->Vars.find(val) == mod->Vars.end())
			{
				for(int i=0; i< this->Vars[val]->AgeSize; i++)
					this->Ages[this->Vars[val]->AgeIndex+i] = CacheLinesPerSet;
			}
		}

	}

	if(this->MissCount == mod->MissCount)
		this->SpecuMissCount = this->SpecuMissCount < mod->SpecuMissCount? this->SpecuMissCount : mod->SpecuMissCount;
	else
		this->SpecuMissCount = this->MissCount > mod->MissCount? this->SpecuMissCount : mod->SpecuMissCount;

	this->MissCount = this->MissCount > mod->MissCount? this->MissCount : mod->MissCount;
	for(auto cr : mod->cacheRecord)
	{
		if(this->cacheRecord.find(cr) == this->cacheRecord.end())
			this->cacheRecord.insert(cr);
	}

	return this;
}


bool CacheModel::isInCache(string varName)
{

    bool incache = false;
	for (const auto &v : this->Vars)
	{
		if(!isVarPartiallyCached(v.second))
			continue;
		Value* val = v.first;
		if(val->getName() == varName)
		{
			if(Ages[v.second->AgeIndex] < this->CacheLinesPerSet)
				incache = true;
		}
	}
	return incache;
}


void CacheModel::dump(bool verbose)
{
	dbgs() << "========cache state===========\n";
	for (const auto &v : this->Vars)
	{
		if(!isVarPartiallyCached(v.second) && !verbose)
			continue;

		Value* val = v.first;

		if(val->hasName())
			dbgs() << val->getName()<< "\n";
		else
			val->dump();

		if(verbose)
		{
			dbgs() << "\t addrB: " << v.second->AddrB << "\t addrE:" << v.second->AddrE
					<< "\n\t ageIndex:" <<v.second->AgeIndex << "\t ageSize:" << v.second->AgeSize
					<< "\n\t align:"<< v.second->alignment <<"\n" ;
		}

		dbgs() << "\t occupy "<< v.second->AgeSize << " lines at "<<v.second->AddrB<<" : ";

		for(int i= v.second->AgeIndex;i<(v.second->AgeIndex+v.second->AgeSize);++i)
		{
			dbgs() << Ages[i]<<", ";
		}
		dbgs() <<"\n";
	}
	dbgs() << "\nTotal #Misses: " << this->MissCount;
	dbgs() << "\t#SpecuMisses: " << this->SpecuMissCount;
	dbgs() << "\n===================\n";
}

CacheSpecuAnalysis::CacheSpecuAnalysis(Function &F, DominatorTree &DT, PostDominatorTree &PDT, AliasAnalysis* AA,
		unsigned lineSize,unsigned lineNum, unsigned setNum, unsigned depth, unsigned merge)
{
	this->AA = AA;
	this->F = &F;
	this->DT = &DT;
	this->PDT = &PDT;
	this->model = new CacheModel(lineSize, lineNum, setNum);

	if(depth >0)
		runSpecu = true;
	this->MissSpecuDepth = depth;
	if(merge == 1)
		this->MergeOption = 1;

	missNum = 0;
	llvm::FindFunctionBackedges(F,backEdges);
}

bool CacheSpecuAnalysis::IsValueInCache(Instruction* inst)
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

bool CacheSpecuAnalysis::GetInstCacheRange(Value* inst, GlobalVariable *&GV, unsigned& offset_b, unsigned& offset_e)
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
	return true;

}

//return false, if reached fixed point. Otherwise, return true.
bool CacheSpecuAnalysis::wideningOp(CacheModel* last, CacheModel* current)
{
	// add new vars, keep going
	if(!last->ConfigConsistent(current))
	{
		errs()<<"Fatal: cache configuration inconsistent when widening!";
		return false;
	}

	if(!last->CacheConsistent(current))
		return true;


	/******Begin Debug: True fixed point*********/
	for(int i =0; i < last->Ages.size(); ++i)
	{
		if(current->Ages[i] != last->Ages[i])
			return true;
	}
	return false;
	/**********End of Debug**********************/


	bool fixed = true;;
	for(int i =0; i < last->Ages.size(); ++i)
	{
		if(current->Ages[i] >= current->CacheLinesPerSet)
		{
			current->Ages[i] = current->CacheLinesPerSet;
			continue;
		}

		if(current->Ages[i] > last->Ages[i])
		{
			// this var is aging
			if(current->Ages[i] < current->CacheLinesPerSet/4)
				current->Ages[i] = current->CacheLinesPerSet/4;
			else if(current->Ages[i] < current->CacheLinesPerSet/2)
				current->Ages[i] = current->CacheLinesPerSet/2;
			else
				current->Ages[i] = current->CacheLinesPerSet;
			fixed = false;
		}
		else
		{
			//this var is accessed in loop
			fixed= false;
		}

	}
	return !fixed; // reached fixed point
}

bool CacheSpecuAnalysis::SpecuSim(BasicBlock* from,BasicBlock* to, CacheModel* initModel)
{
	this->cacheTrace.clear();

	std::deque<BasicBlock*> WL;
	WL.push_back(from);

//	this->model = initModel;
//	this->visit(from);
//	this->cacheTrace[from] = this->model;
//
//	for (auto it = succ_begin(from), et = succ_end(from); it != et; ++it)
//		WL.push_back(*it);

	CacheModel* predModel;
	BasicBlock* bb;
	bool skipBB = false;
	int debugcounter = 1;

	while(!WL.empty())
	{
		bb = WL.front();
		WL.pop_front();

//		dbgs()<<"=====" <<debugcounter <<": ";
//		bb->printAsOperand(dbgs(), false);
//		dbgs()<<" =======\n";
		debugcounter++;

		skipBB = false;
		if(bb == from)
			predModel = initModel->fork();
		else
			predModel = nullptr;

		for (auto it = pred_begin(bb), et = pred_end(bb); it != et; ++it)
		{
			if(this->cacheTrace.find(*it) == this->cacheTrace.end())
			{
				if(!IsBackEdge(*it, bb))
				{
					WL.push_back(bb); // if pred is not a back edge, and is unvisited, do it later
					skipBB = true;
//					dbgs()<<"\nHas unvisited pred bb, skip this bb.\n";
					break;
				}
				continue;
			}

			// stop back trace if loop reach fixed point
			if(IsBackEdge(*it, bb))
			{
				predModel = this->cacheTrace[*it]->fork();
				auto edge = std::pair<const BasicBlock*,const BasicBlock*>(*it, bb);
//				dbgs()<<"\nbb from back edge: ";

				if(wideningMap.find(edge) == wideningMap.end())
				{
					wideningMap[edge] = predModel;
					wideningMapCount[edge] = 1;
				}
				else if(wideningMap[edge] == nullptr)
				{
//					dbgs()<<"fixed point already reached before!\n";
					// already reached fix-point before, skip it anyway
					skipBB = true;
				}
				else if(wideningOp(wideningMap[edge], predModel))
				{
//					dbgs()<<"keep looping!\n";
					// loop havn't reach fix-point
					wideningMap[edge] = predModel;

					if(++wideningMapCount[edge] < 10)
					{
//						dbgs()<<"fixed point reached!\n";
						wideningMap[edge] = nullptr;
						wideningMapCount[edge] = 0;
						skipBB = true; // wideningOp reach fixed point, finish this loop
					}
				}
				else
				{
//					dbgs()<<"fixed point reached!\n";
					wideningMap[edge] = nullptr;
					wideningMapCount[edge] = 0;
					skipBB = true; // wideningOp reach fixed point, finish this loop
				}
				if(skipBB)
				{
					for (auto suc = succ_begin(bb), suce = succ_end(bb); suc != suce; ++suc)
					{
						if(isPotentiallyReachable(*suc, bb, this->DT)) continue;

						if(std::find(WL.begin(), WL.end(), *suc) == WL.end())
							WL.push_back(*suc);
					}

				}
				break;
			}

			if(predModel)
				predModel->merge(this->cacheTrace[*it]);
			else
				predModel = this->cacheTrace[*it]->fork();
		}

		if(skipBB) continue;
		this->model = predModel;

		for(auto it = bb->begin(), et= bb->end(); it != et; ++it)
		{
			unsigned hitCount = this->model->HitCount;
			unsigned missCount = this->model->MissCount;

			this->cacheChanged = false;
			this->visit(*it);

			CacheModel *tmpMod = this->model; // save model cause specu propagation may change it

			for(auto &sp: SpecuInfo)
			{
				if(sp->Finished)
					continue;
				unsigned isSpecu = sp->IsSpeculative(bb);

				if(isSpecu != 0)
				{
					if(this->model->HitCount != hitCount)
						this->model->SpecuHitCount++;
					if(this->model->MissCount != missCount)
						this->model->SpecuMissCount++;
				}
				else
				{
					continue;
				}

				if(isSpecu & 0x1)
				{
//					dbgs()<<"\nBB is speculatively executed at if branch with depth: " << sp->IfDepth <<"\n";
					if(sp->AddModel(this->model, true, cacheChanged))
						sp->IfEndBB = bb;
				}

				if(isSpecu & 0x2)
				{
//					dbgs()<<"\nBB is speculatively executed at else branch with depth: " << sp->ElseDepth <<"\n";
					if(sp->AddModel(this->model, false, cacheChanged))
						sp->ElseEndBB = bb;
				}

				if(sp->IsFinished()){

					// record iteration info
					if(this->result.find(sp->CauseBB) == this->result.end())
						this->result[sp->CauseBB] = 1;
					else
						this->result[sp->CauseBB] = this->result[sp->CauseBB]+1;


					if(this->MergeOption ==1)
					{
						// merge at eariler point:
						BasicBlock *spIfbb = sp->DTIf->getBlock();

						if(this->propCacheTrace.find(spIfbb) != this->propCacheTrace.end())
							this->propCacheTrace[spIfbb] = this->propCacheTrace[spIfbb]->merge(sp->IfModel);
						else
							this->propCacheTrace[spIfbb] = sp->IfModel->fork();

						if(std::find(WL.begin(), WL.end(), spIfbb) == WL.end())
							WL.push_back(spIfbb);

						BasicBlock *spElsebb = sp->DTElse->getBlock();
						if(this->propCacheTrace.find(spElsebb) != this->propCacheTrace.end())
							this->propCacheTrace[spElsebb] = this->propCacheTrace[spElsebb]->merge(sp->ElseModel);
						else
							this->propCacheTrace[spElsebb] = sp->ElseModel->fork();
						if(std::find(WL.begin(), WL.end(), spElsebb) == WL.end())
							WL.push_back(spElsebb);
					}
					else
					{
						// merge at late point
						//dbgs()<<"Finished specu execution, begin to propagate states:\n";
						//both if and else branch end bb have determined, now calculate the merge bb of propagation
						//which should be the nearest common post dominator of IfEndBB and ElseEndBB

						BasicBlock* mergeBB = PDT->findNearestCommonDominator(sp->IfEndBB, sp->ElseEndBB);
						if(mergeBB)
						{
							sp->MergeBB = mergeBB;
						}
						else
						{
							errs()<<"Fatal: cannot find merge point for specu propagation!\n";
							return false;
						}

						BasicBlock* propMergeBB  =SpecuPropagation(sp->DTIf->getBlock(), sp->MergeBB, sp->ElseModel);
						//					dbgs() << "If propagate to: \n\t";
						//					propMergeBB->print(dbgs());
						if(propMergeBB && std::find(WL.begin(), WL.end(), propMergeBB) == WL.end())
							WL.push_back(propMergeBB);

						propMergeBB = SpecuPropagation(sp->DTElse->getBlock(), sp->MergeBB, sp->IfModel);
						//					dbgs() << "Else propagate to: \n\t";
						//					propMergeBB->print(dbgs());
						if(propMergeBB && std::find(WL.begin(), WL.end(), propMergeBB) == WL.end())
							WL.push_back(propMergeBB);

					}
					sp->Finished = 2;
				}
			}
			this->model = tmpMod;

		}

		if(this->propCacheTrace.find(bb) != this->propCacheTrace.end())
		{
			this->cacheTrace[bb] = this->propCacheTrace[bb]->merge(this->model);//->fork();
			this->propCacheTrace.erase(bb);
		}
		else
			this->cacheTrace[bb] = this->model;
//		if(this->cacheTrace.find(bb) == this->cacheTrace.end())
//			this->cacheTrace[bb] = this->model;
//		else
//			this->cacheTrace[bb] = this->cacheTrace[bb]->merge(this->model);

		for (auto it = succ_begin(bb), et = succ_end(bb); it != et; ++it)
		{
			if(std::find(WL.begin(), WL.end(), *it) == WL.end())
				WL.push_back(*it);


			for(auto &sp: SpecuInfo)
			{
				// if bb is still speculative, which means not reached depth, add its succ to specu WL
				unsigned isSpecu = sp->IsSpeculative(bb);
				if(isSpecu & 0x1)
				{
					sp->WLIf.erase(bb);
					sp->WLIf.insert(*it);
				}
				if(isSpecu & 0x2)
				{
					sp->WLElse.erase(bb);
					sp->WLElse.insert(*it);
				}
			}

		}

		if(!runSpecu)
			continue;

		CacheSpecuInfo* specuInfo = nullptr;
		unsigned addSpecu = GetSpecuInfo(specuInfo, bb);

	    if(addSpecu ==1)
	    	if(specuInfo->Finished)
	    		specuInfo->Reset();
	    if(addSpecu ==2)
	    	SpecuInfo.push_back(specuInfo);
	}

//	this->model->dump(true);
 	bool buffincache = this->model->isInCache("buff");
 	buffincache |= this->model->isInCache("doencryption.buf");

 	int i=0, totalIter =0;
 	for(auto spresult : this->result)
 	{
 		i++;
 		//dbgs()<<"========"<< i<<"th bb: "<<spresult.second<< " iterations======\n";
 		totalIter +=spresult.second;
// 		spresult.first->dump();
 	}
 	dbgs()<<"========Num Specu Branch:"<< i << "======\n";
 	dbgs()<<"========Num Cache Misses:"<< this->model->MissCount<< "=====\n";
 	dbgs()<<"========Num Specu Misses:"<< this->model->SpecuMissCount<< "======\n";
 	dbgs()<<"========Total iterations:"<< totalIter<< "======\n";
// 	dbgs()<<"========Num cache lines used:"<< this->model->cacheRecord.size()<< "======\n";
 	dbgs()<<"========Buff is in cache:"<< buffincache << "======\n";
	return true;
}


// Propagate the speculative state to other basic blocks from startBB, untill
//     1. reach the termBB
//     2. back edge to a loop entry, that will be revisited again
BasicBlock* CacheSpecuAnalysis::SpecuPropagation(BasicBlock* startBB, BasicBlock* termBB, CacheModel* initModl)
{
	ValueMap<BasicBlock*, CacheModel*> cacheSpecuTrace;
	std::deque<BasicBlock*> WL;

	this->model = initModl;
	this->visit(startBB);
	cacheSpecuTrace[startBB] = this->model;
	for (auto it = succ_begin(startBB), et = succ_end(startBB); it != et; ++it)
		WL.push_back(*it);

	if(WL.empty())
		return startBB;

	while(!WL.empty())
	{
		BasicBlock *sp_bb = WL.front();
		WL.pop_front();


		this->model = nullptr;
		for (auto it = pred_begin(sp_bb), et = pred_end(sp_bb); it != et; ++it)
		{
			if(cacheSpecuTrace.find(*it) != cacheSpecuTrace.end())
			{
				if(this->model)
					this->model->merge(cacheSpecuTrace[*it]);
				else
					this->model = cacheSpecuTrace[*it]->fork();
			}
		}
		if(!this->model)
			continue;

		this->visit(sp_bb);
		cacheSpecuTrace[sp_bb] = this->model;

		CacheSpecuInfo* unusedSpecuInfo = nullptr;
		if((sp_bb == termBB) ||(GetSpecuInfo(unusedSpecuInfo, sp_bb) !=2))
		{
			if(this->propCacheTrace.find(sp_bb) != this->propCacheTrace.end())
				this->propCacheTrace[sp_bb] = this->propCacheTrace[sp_bb]->merge(this->model);
			else
				this->propCacheTrace[sp_bb] = this->model->fork();

			return sp_bb;
		}

		for (auto it = succ_begin(sp_bb), et = succ_end(sp_bb); it != et; ++it)
		{
			if(std::find(WL.begin(), WL.end(), *it) == WL.end())
				WL.push_back(*it);
		}
	}
	errs()<< "Fatal: specu propagate terminate on null!\n";
	return nullptr;
}


unsigned CacheSpecuAnalysis::GetSpecuInfo(CacheSpecuInfo* &specuInfo, BasicBlock* bb)
{
	// is bb end with conditional branch that initial speculative execution?
	BranchInst *BI = dyn_cast<BranchInst>(bb->getTerminator());
	if (!BI || BI->isUnconditional()) {
		return 0;
	}
	else
	{
//		dbgs()<<"Detect a specu entry point.\n";
		DomTreeNode *S0 = DT->getNode(BI->getParent());
		DomTreeNode *S1 = DT->getNode(BI->getSuccessor(0));
		DomTreeNode *S2 = DT->getNode(BI->getSuccessor(1));
		DomTreeNode *S3 = S2;
		bool hasElse = S0->getNumChildren() == 3;
		for (DomTreeNode::iterator child = S0->begin(); child != S0->end(); ++child)
		{
			DomTreeNode *node = *child;
			if (node == S1 || node == S2)
				continue;
			S3 = *child;
		}
		//TODO: add depth opt here
		for(auto &sp: SpecuInfo)
		{
			if(sp->CauseBB == bb)
			{
				specuInfo = sp;
				return 1;
			}
		}
		specuInfo = new CacheSpecuInfo(bb,this->DT, S1, S2, S3, this->MissSpecuDepth, hasElse);
		return 2;
	}
}


unsigned CacheSpecuAnalysis::IsAliasTo(Value* from, Value* &to, unsigned &offset)
{
//    offset = 0;
    to = from;

    if((!from->getType()->isPointerTy()) && this->model->Vars.find(from) != this->model->Vars.end())
    	return 2;

    auto dest = AliasMap.find(from);
    if(dest == AliasMap.end())
    	return 0;

    int counter = 0;
    while( dest != AliasMap.end())
    {
    	if(dest->second->Offset == (unsigned)-1 || offset==(unsigned)-1)
    		offset = dest->second->Offset;
    	else
    		offset += dest->second->Offset;
    	to = dest->second->Dest;
    	dest = AliasMap.find(to);

    	if(counter++ >100 )
    	{
    		if(this->model->Vars.find(to) != this->model->Vars.end())
    		{
    			dbgs() << "Return random global var: ";
    			to->dump();
    			dbgs() <<"after too many iterations when searching alias for: ";
    			from->dump();
    			return 3;
    		}
    	}
    	if(counter >200)
    	{
    		dbgs() << "Error when searching alias for: ";
    		from->dump();
    		return 0;
    	}

    }
    return 1;

}

    
vector<Value*> CacheSpecuAnalysis::GetAlias(Value * val, unsigned offset)
{
    vector<Value*> aas;
    dbgs() << "The alias of\n\t";
    val->dump();
    dbgs() << "are";
    for (const auto &v : this->model->Vars)
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




void CacheSpecuAnalysis::InitModel()
{
	Module *module = this->F->getParent();
	int i =0;

	for (auto& A : F->getArgumentList())
	{
		i++;
		unsigned alignment = F->getParamAlignment(i);
		Type *ty = A.getType();
		this->model->AddVar(&A, ty, alignment);
	}


	for (Module::global_iterator i = module->global_begin();
		i != module->global_end(); ++i)
	{
		GlobalVariable &v = *i;
		unsigned alignment = v.getAlignment();
		Type *ty = v.getValueType();
		//errs()<< "\nGV " <<v.getName()<<" has type:"; ty->print(errs());
		this->model->AddVar(&v, ty, alignment);
		if(v.getName() == "buff" || v.getName() == "doencryption.buf" || v.getName() == "doencryption.obuf")
		{
			//preload buff into cache
			this->model->Access(&v, true);
		}

	}

//	this->model->dump();
} 

void CacheSpecuAnalysis::visitLoadInst(LoadInst &I)
{
	Value* var = I.getPointerOperand();
    Value* to;
    unsigned offset =0;
    unsigned hit;
    this->cacheChanged = true;
	if (ConstantExpr *GEPC = dyn_cast<ConstantExpr>(var))
		this->ExtractGEPC(GEPC,var, offset);

    this->IsAliasTo(var, to, offset);
    AliasMap[&I] = new PointerLocation(var,0);


    hit = this->model->Access(to, offset);

    if(hit ==0)
    {
    	this->model->MissCount++;
    	missNum++;
//    	dbgs() << "Load value" << *to << "@" <<offset << " : "<< missNum << "\n";
    }
    else
    {
    	this->model->HitCount++;
    }

}

void CacheSpecuAnalysis::visitIntrinsicInst(IntrinsicInst &I)
{
	unsigned offset =0;
	unsigned hit;

	if(I.getName().find("llvm.memset") != std::string::npos)
	{



	}

	if((I.getName().find("llvm.memmov") != std::string::npos)||
		(I.getName().find("llvm.memcpy") != std::string::npos))
	{
		Value* src = I.getArgOperand(0);
		Value* dec = I.getArgOperand(1);
		Value* to;
		if (ConstantExpr *GEPC = dyn_cast<ConstantExpr>(src))
			this->ExtractGEPC(GEPC,src, offset);

		this->IsAliasTo(src, to, offset);
		AliasMap[&I] = new PointerLocation(src,0);


		hit = this->model->Access(to, offset);

	}
}


void CacheSpecuAnalysis::visitCallInst(CallInst &I)
{

}

void CacheSpecuAnalysis::visitAllocaInst(AllocaInst &I)
{
	unsigned alignment = I.getAlignment();
	Type *ty = I.getAllocatedType();
	this->cacheChanged = true;
	this->model->AddVar(&I, ty, alignment);
}

void CacheSpecuAnalysis::visitStoreInst(StoreInst &I)
{
	unsigned from, to, offset, hit;
	PointerLocation *pl=nullptr;
	Value* target;
	Value* var = I.getPointerOperand();
	Value* alias;
	this->cacheChanged = true;
	if(I.getValueOperand()->getType()->isPointerTy()
       && I.getPointerOperand()->getType()->getContainedType(0)->isPointerTy())
    {
	    if (ConstantExpr *GEPC = dyn_cast<ConstantExpr>(I.getValueOperand()))
	    {
	    	if(GEPC->isGEPWithNoNotionalOverIndexing())
	    	{
	    		GetElementPtrInst* GEP = cast<GetElementPtrInst>(GEPC->getAsInstruction());
	    		target = GEP->getPointerOperand();
		    	if (!CacheModel::GEPInstPos(*GEP, from, to))
		    		offset = 0;
		    	else
		    		offset = from;
		    	delete(GEP);
	    	}
	    }
	    else
	    {
	    	target = I.getValueOperand();
	    	offset =0;
	    }

		this->IsAliasTo(target, alias, offset);
		if(var != alias)
			AliasMap[var] = new PointerLocation(alias, offset);
    }


	if (ConstantExpr *GEPC = dyn_cast<ConstantExpr>(var))
		this->ExtractGEPC(GEPC,var, offset);
	this->IsAliasTo(var, alias, offset);

	hit = this->model->Access(alias, offset);

    if(hit ==0)
    {
    	this->model->MissCount++;
    	missNum++;
//    	dbgs() << "Store value" << *alias << "@" <<offset << " : "<< missNum << "\n";
    }
    else
    {
    	this->model->HitCount++;
    }
}



void CacheSpecuAnalysis::visitVACopyInst(VACopyInst &I)
{

}

void CacheSpecuAnalysis::visitBranchInst(BranchInst &I)
{

}

void CacheSpecuAnalysis::visitBitCastInst(BitCastInst &I)
{
	Value *target = I.getOperand(0);
	unsigned offset =0, from, to;

	if (ConstantExpr *GEPC = dyn_cast<ConstantExpr>(target))
		this->ExtractGEPC(GEPC,target, offset);

    this->AliasMap[&I] = new PointerLocation(target,offset);
}

void CacheSpecuAnalysis::ExtractGEPC(ConstantExpr* source, Value* &target, unsigned &offset)
{
	target = source;
	offset = 0;
	unsigned from, to;

	if(source->isGEPWithNoNotionalOverIndexing())
	{
		GetElementPtrInst* GEP = cast<GetElementPtrInst>(source->getAsInstruction());
		target = GEP->getPointerOperand();
		if (!CacheModel::GEPInstPos(*GEP, from, to))
			offset = 0;
		else
			offset = from;
		delete(GEP);
	}

}
void CacheSpecuAnalysis::visitPHINode(PHINode &I)
{
	unsigned i = I.getNumIncomingValues();
	Value *alias, *target;
	unsigned offset = 0;
	while(i--)
	{
		target = I.getIncomingValue(i);

		if (ConstantExpr *GEPC = dyn_cast<ConstantExpr>(target))
			this->ExtractGEPC(GEPC,target, offset);

		if(this->IsAliasTo(target, alias, offset))
		{
			this->AliasMap[&I] = new PointerLocation(alias,offset);
			return;
		}
	}
}
void CacheSpecuAnalysis::visitSelectInst(SelectInst &I)
{
	Value *alias, *target;
	unsigned offset =0;

	target = I.getTrueValue();
	if (ConstantExpr *GEPC = dyn_cast<ConstantExpr>(target))
		this->ExtractGEPC(GEPC,target, offset);

	if(this->IsAliasTo(target, alias, offset))
	{
		this->AliasMap[&I] = new PointerLocation(alias,offset);
		return;
	}

	target = I.getFalseValue();
	if (ConstantExpr *GEPC = dyn_cast<ConstantExpr>(target))
		this->ExtractGEPC(GEPC,target, offset);

	if(this->IsAliasTo(target, alias, offset))
	{
		this->AliasMap[&I] = new PointerLocation(alias,offset);
		return;
	}
}

    
void CacheSpecuAnalysis::visitGetElementPtrInst(GetElementPtrInst &I)
{
	Value* dest = I.getPointerOperand();
    unsigned from, to;

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


	if (!CacheModel::GEPInstPos(I, from, to))
    {
    	this->AliasMap[&I] = new PointerLocation(dest,-1);
    	return;
    }
    
    this->AliasMap[&I] = new PointerLocation(dest,from);
}

void CacheSpecuAnalysis::visitInstruction(Instruction & I)
{


}


void CacheSpecuAnalysis::dump(int mod)
{
	if(mod == 1)
	{
		for(const auto &ed : backEdges)
		{
			dbgs()<<"back edge from";
			ed.first->dump();dbgs()<<" to ";
			ed.second->dump();dbgs()<<"\n";
		}
	}

	if(mod ==2)
	{
		for(const auto &alia : AliasMap)
		{
			dbgs()<<"Alia from";
			alia.first->dump();
			dbgs()<<"to\t";
			alia.second->Dest->dump();
			dbgs()<<" @ "<<alia.second->Offset<<"\n";
		}
	}
}


}













