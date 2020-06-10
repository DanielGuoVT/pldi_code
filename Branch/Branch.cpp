//===- Branch.cpp - Transform branches dependent on secrete data ---------------===//
//   - 10/04 treat all input as sensitive
//
//===---------------------------------------------------------------------------===//

#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopUnrollAnalyzer.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/IR/User.h"
#include "Taint.h"
#include "CacheAnalysis.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/IR/InlineAsm.h"

using namespace std;
using namespace llvm;
using namespace taint;
using namespace cache;
#define DEBUG_TYPE "branch"

typedef ValueMap<const Value *, WeakVH> ValueToValueMapTy;

//#define OPT_ENABLE
//#define USE_PRELOAD
//#define USE_SELECT
#define USE_CMOV
//#define USE_BITWISE

namespace {
    
    typedef DenseMap<const Value*, Value*> ValueToValueMap;
    // Hello - The first implementation, without getAnalysisUsage.
    struct Branch : public FunctionPass {
        static char ID; // Pass identification, replacement for typeid
        Branch() : FunctionPass(ID) {
        }
        TaintAnalysis *taintAnalysis;
        CacheAnalysis* cacheAnalysis;
        DominatorTree DT;
        SmallVector<Instruction*, 4> realVars;
//        AllocaInst *index = nullptr;

        unsigned cacheLineSize = 64;
        unsigned cacheLineNum = 511;
        
        unsigned indexCount;
        unsigned branchCount;

        Instruction* tmpInst = nullptr;
        Instruction* tmpVar = nullptr;

        bool IsSensitiveIndex(GetElementPtrInst *indexInst)
        {
        	for (int i = 1; i < (int)(indexInst->getNumOperands()); i++)
        	{
        		if (taintAnalysis->isValueTainted(indexInst->getOperand(i)))
        			return true;
        	}
        	return false;
        }



        Instruction* tryToMitigateIndex(Function &F, Instruction *inst)
        {
        	GetElementPtrInst *indexInst = dyn_cast<GetElementPtrInst>(inst);
        	if (!indexInst)
        		return nullptr;

        	//DEBUG(dbgs() << "Check if GEP need mitigate: "; indexInst->print(dbgs()); dbgs() << "\n");
        	// at least one of its indices is sensitive
        	SmallVector<Value*, 4> TaintedIndices;
        	for (int i = 1; i < (int)(indexInst->getNumOperands()); i++)
        	{

        		Value *Index = indexInst->getOperand(i);
        		if (taintAnalysis->isValueTainted(Index))
        			TaintedIndices.push_back(Index);
        	}

        	if (TaintedIndices.empty())
        	{
        		//DEBUG(dbgs() << "Index of GEP not sensitive: no mitigate \n");
        		return nullptr;
        	}

        	Value* truePos = TaintedIndices.back();
        	// and GEP instruction on an array


        	ArrayType *sourceTy = dyn_cast<ArrayType>(indexInst->getSourceElementType());
        	if (!sourceTy)
        	{
        		Value* GEPO0 = indexInst->getOperand(0);

        		while(GEPO0)
        		{
        			if (ConstantExpr *GEPC = dyn_cast<ConstantExpr>(GEPO0))
        			{
        				if(GEPC->isGEPWithNoNotionalOverIndexing())
        				{
        					GetElementPtrInst* GEPCGEP = cast<GetElementPtrInst>(GEPC->getAsInstruction());
        					GEPO0 = GEPCGEP->getOperand(0);
        					if(dyn_cast<GlobalVariable>(GEPO0) &&
        							(sourceTy = dyn_cast<ArrayType>(GEPCGEP->getSourceElementType())))
        					{
        						delete(GEPCGEP);
        						break;
        					}

        					delete(GEPCGEP);
        				}
        				else
        					return nullptr;
        			}
        			else if(isa<GetElementPtrInst>(GEPO0))
        			{
        				GetElementPtrInst* GEPCGEP = cast<GetElementPtrInst>(GEPO0);
        				GEPO0 = GEPCGEP->getOperand(0);

        				if(dyn_cast<GlobalVariable>(GEPO0) &&
        						(sourceTy = dyn_cast<ArrayType>(GEPCGEP->getSourceElementType())))
        				{
        					break;
        				}
        			}
        			else
        			{
        				return nullptr;
        			}
        		}
        	}



        	uint64_t  numElements = sourceTy->getNumElements();
        	uint64_t  sizeElement = 1;

        	// and array element is integer (this is the case for crypto) FIXME: not necessary
        	IntegerType *resultTy = dyn_cast<IntegerType>(indexInst->getResultElementType());
        	if (!resultTy)
        		return nullptr;
        	else
        		sizeElement =(resultTy->getBitWidth())/8;


			if(!(sizeElement==1 | sizeElement==2 |sizeElement==4 |sizeElement==8))
			{
				errs() << "Fatal Error: Size of element is invalid!!";
				return nullptr;
			}


        	SmallVector<Instruction*, 8> UserOfGEP;
        	for (auto U : indexInst->users())
        	{
        		if (LoadInst *I = dyn_cast<LoadInst>(U))
        		{
        			UserOfGEP.push_back(I);
        		}
        	}

        	// use of gep must be load
        	if (indexInst->getNumUses() != UserOfGEP.size())
        	{
        		//DEBUG(dbgs() << "Use of GEP not load: no mitigate.\n");
        		return nullptr;
        	}

        	uint64_t usedCacheLineNum = (sizeElement * numElements) / cacheLineSize;
        	if ((sizeElement * numElements)%cacheLineSize != 0)
        		usedCacheLineNum += 1;

        	if(usedCacheLineNum <2)
        		return nullptr;

#ifdef OPT_ENABLE
        	if(this->tmpInst)
        	{
        		this->cacheAnalysis->CacheSim(this->tmpInst, this->tmpVar, indexInst);
        		bool hit = this->cacheAnalysis->IsValueInCache(UserOfGEP.back());
        		this->tmpInst = UserOfGEP.back();
        		this->tmpVar = indexInst;

        		if(hit)
        		{
        			//this->tmpInst->dump();
        			//errs() << "Optimize out this inst.\n";
        			return nullptr;
        		}
        	}
#endif

        	DEBUG(dbgs() << "\nYes! Need to mitigate:";indexInst->print(dbgs()););
//        	GlobalVariable *ptrVal = dyn_cast<GlobalVariable>(indexInst->getOperand(0));
//        	if(ptrVal)
//        		ptrVal->setAlignment(cacheLineSize*8);
        	//else{warning:}
//        	BasicBlock *preBB = indexInst->getParent();
//        	BasicBlock *endBB = preBB->splitBasicBlock(indexInst);



        	uint64_t elesInCacheLine = cacheLineSize/sizeElement;

        	IntegerType *i64 = IntegerType::get(F.getContext(), 64);
        	IntegerType *i16 = IntegerType::get(F.getContext(), 16);
        	IntegerType *i8 = IntegerType::get(F.getContext(), 8);

//        	if(!index)
//        		index = new AllocaInst(i64, "", &*inst_begin(F));

        	Instruction* realVal = nullptr;
//        	for(auto &I:realVars)
//        	{
//        		if(I->getType() == UserOfGEP.back()->getType())
//        		{
//        			realVal = I;
//        			break;
//        		}
//        	}
//        	if(!realVal)
//        	{
//        		realVal = new AllocaInst(UserOfGEP.back()->getType(), "", &*inst_begin(F)); // true return value from GEP;
//        		realVars.push_back(realVal);
//        	}
//
//        	new StoreInst( ConstantInt::get(UserOfGEP.back()->getType(), 0), realVal, preBB->getTerminator());

        	//AllocaInst *dummyVal = new AllocaInst(UserOfGEP.back()->getType(), "", &*inst_begin(F)); // dummy return value from GEP;

//        	Instruction *indexUpBound = new AllocaInst(i64, "", &*inst_begin(F));  // i64 indexUpBound;
//
//        	Instruction *indexUpBoundAssign = new StoreInst(ConstantInt::get(i64, numElements - 1), indexUpBound, preBB->getTerminator()); // indexUpBound = N-1;
//        	Instruction *indexUpBoundLoad = new LoadInst(indexUpBound, "", preBB->getTerminator());

        	//new LoadInst(realVal, preBB->getTerminator());
        	//new LoadInst(dummyVal, preBB->getTerminator());

//        	BasicBlock *getValBB;

        	Value *offset;
        	Instruction *newGEP;

//        	Instruction *preTerm = preBB->getTerminator();
//        	preTerm->removeFromParent();

        	bool canOverflow = (numElements%cacheLineSize != 0);

        	for (uint64_t i = 0; i < usedCacheLineNum; i++)
        	{
//        		getValBB = preBB;

        		if (i==0)
        		{
        			//preBB->getTerminator()->replaceUsesOfWith(endBB, getValBB);
        			offset = BinaryOperator::CreateSRem(truePos, ConstantInt::get(i64, elesInCacheLine), "", indexInst);
        		}
        		else
        		{
        			//LoadInst *loadIndex = new LoadInst(index, "", getValBB);
        			offset = BinaryOperator::CreateAdd(offset, ConstantInt::get(i64, elesInCacheLine), "", indexInst);
        		}

        		if (i == (usedCacheLineNum-1) && canOverflow)
        		{
        			ICmpInst *offsetOverflow = new ICmpInst(indexInst, CmpInst::Predicate::ICMP_SGE, offset, ConstantInt::get(i64, numElements), "");
        			Instruction *selectOffset = SelectInst::Create(offsetOverflow,ConstantInt::get(i64, numElements - 1),offset,"",indexInst);
        			offset = selectOffset;
        		}

        		newGEP = indexInst->clone();
        		newGEP->replaceUsesOfWith(truePos, offset);
        		newGEP->insertBefore(indexInst);


        		Instruction *loadGEP = UserOfGEP.back()->clone();
        		loadGEP->replaceUsesOfWith(indexInst, newGEP);
        		loadGEP->insertBefore(indexInst);

        		ICmpInst *assignCond = new ICmpInst(indexInst, CmpInst::Predicate::ICMP_EQ, truePos, offset, ""); // if offset == truePos

#ifdef USE_BITWISE
        		SExtInst *ext = new SExtInst(assignCond, UserOfGEP.back()->getType(),"", indexInst);
        		BinaryOperator *negext = BinaryOperator::CreateXor(ext,ConstantInt::get(UserOfGEP.back()->getType(), -1),"", indexInst);

        		BinaryOperator *andReaval, *andLoadGEP;
        		if(i == 0)
        			andReaval = BinaryOperator::CreateAnd(negext,ConstantInt::get(UserOfGEP.back()->getType(), 0),"", indexInst);
        		else
        			andReaval = BinaryOperator::CreateAnd(negext,realVal,"", indexInst);

        		andLoadGEP = BinaryOperator::CreateAnd(ext,loadGEP,"", indexInst);
        		realVal = BinaryOperator::CreateOr(andLoadGEP, andReaval,"",indexInst);
#endif
#ifdef  USE_CMOV

        		Type* valueTy = UserOfGEP.back()->getType();

        		if(sizeElement ==1)
        		{
        			ZExtInst* zext = new ZExtInst(loadGEP, i16,"", indexInst);
        			loadGEP = zext;
        			valueTy = i16;
        		}

          		if(i==0)
          		{
          			realVal = SelectInst::Create(assignCond,loadGEP,ConstantInt::get(valueTy, 0),"",indexInst);
          		}
          		else
          		{
          			realVal = SelectInst::Create(assignCond,loadGEP,realVal,"",indexInst);
          		}

        		if(sizeElement ==1 && i == (usedCacheLineNum-1))
        		{
        			TruncInst* trunc = new TruncInst(realVal, i8,"", indexInst);
        			realVal = trunc;
        		}
#endif
#ifdef USE_SELECT
        		if(i==0)
        		{
        			realVal = SelectInst::Create(assignCond,loadGEP,ConstantInt::get(UserOfGEP.back()->getType(), 0),"",indexInst);
        		}
        		else
        		{
        			realVal = SelectInst::Create(assignCond,loadGEP,realVal,"",indexInst);
				}
#endif

        	}



        	SmallVector<Instruction*, 8> usersOfI;
        	for (auto I : UserOfGEP)
        	{
        		usersOfI.clear();
        		for (auto U : I->users())
        		{
        			usersOfI.push_back((Instruction*)U);
        		}

        		for (auto U : usersOfI)
        		{
        			U->replaceUsesOfWith(I, realVal);
        		}
        		I->eraseFromParent();
        	}
    		this->tmpInst = realVal;
        	this->tmpVar = newGEP;
        	this->tmpInst->setName("Mitigated");
        	indexInst->eraseFromParent();
        	return realVal;
        }

        Instruction* tryToMitigateIndexViaPreload(Function &F, Instruction *inst)
        {
        	GetElementPtrInst *indexInst = dyn_cast<GetElementPtrInst>(inst);
        	if (!indexInst)
        		return nullptr;

        	//DEBUG(dbgs() << "Check if GEP need mitigate: "; indexInst->print(dbgs()); dbgs() << "\n");
        	// at least one of its indices is sensitive
        	SmallVector<Value*, 4> TaintedIndices;
        	for (int i = 1; i < (int)(indexInst->getNumOperands()); i++)
        	{

        		Value *Index = indexInst->getOperand(i);
        		if (taintAnalysis->isValueTainted(Index))
        			TaintedIndices.push_back(Index);
        	}

        	if (TaintedIndices.empty())
        	{
        		//DEBUG(dbgs() << "Index of GEP not sensitive: no mitigate \n");
        		return nullptr;
        	}

        	Value* truePos = TaintedIndices.back();
        	// and GEP instruction on an array


        	ArrayType *sourceTy = dyn_cast<ArrayType>(indexInst->getSourceElementType());
        	if (!sourceTy)
        	{
        		Value* GEPO0 = indexInst->getOperand(0);

        		while(GEPO0)
        		{
        			if (ConstantExpr *GEPC = dyn_cast<ConstantExpr>(GEPO0))
        			{
        				if(GEPC->isGEPWithNoNotionalOverIndexing())
        				{
        					GetElementPtrInst* GEPCGEP = cast<GetElementPtrInst>(GEPC->getAsInstruction());
        					GEPO0 = GEPCGEP->getOperand(0);
        					if(dyn_cast<GlobalVariable>(GEPO0) &&
        							(sourceTy = dyn_cast<ArrayType>(GEPCGEP->getSourceElementType())))
        					{
        						delete(GEPCGEP);
        						break;
        					}

        					delete(GEPCGEP);
        				}
        				else
        					return nullptr;
        			}
        			else if(isa<GetElementPtrInst>(GEPO0))
        			{
        				GetElementPtrInst* GEPCGEP = cast<GetElementPtrInst>(GEPO0);
        				GEPO0 = GEPCGEP->getOperand(0);

        				if(dyn_cast<GlobalVariable>(GEPO0) &&
        						(sourceTy = dyn_cast<ArrayType>(GEPCGEP->getSourceElementType())))
        				{
        					break;
        				}
        			}
        			else
        			{
        				return nullptr;
        			}
        		}
        	}



        	uint64_t  numElements = sourceTy->getNumElements();
        	uint64_t  sizeElement = 1;

        	// and array element is integer (this is the case for crypto) FIXME: not necessary
        	IntegerType *resultTy = dyn_cast<IntegerType>(indexInst->getResultElementType());
        	if (!resultTy)
        		return nullptr;
        	else
        		sizeElement =(resultTy->getBitWidth())/8;

        	SmallVector<Instruction*, 8> UserOfGEP;
        	for (auto U : indexInst->users())
        	{
        		if (LoadInst *I = dyn_cast<LoadInst>(U))
        		{
        			UserOfGEP.push_back(I);
        		}
        	}

        	// use of gep must be load
        	if (indexInst->getNumUses() != UserOfGEP.size())
        	{
        		//DEBUG(dbgs() << "Use of GEP not load: no mitigate.\n");
        		return nullptr;
        	}

        	uint64_t usedCacheLineNum = (sizeElement * numElements) / cacheLineSize;

        	uint64_t numElePreLine = cacheLineSize/sizeElement;

        	if ((sizeElement * numElements)%cacheLineSize != 0)
        		usedCacheLineNum += 1;

        	if(usedCacheLineNum <2)
        		return nullptr;

#ifdef OPT_ENABLE
        	if(this->tmpInst)
        	{
        		this->cacheAnalysis->CacheSim(this->tmpInst, this->tmpVar, indexInst);
        		bool hit = this->cacheAnalysis->IsValueInCache(UserOfGEP.back());
        		this->tmpInst = UserOfGEP.back();
        		this->tmpVar = indexInst;

        		if(hit)
        		{
        			//this->tmpInst->dump();
        			//errs() << "Optimize out this inst.\n";
        			return nullptr;
        		}
        	}
#endif

        	DEBUG(dbgs() << "\nYes! Need to mitigate:";indexInst->print(dbgs()););
        	IntegerType *i64 = IntegerType::get(F.getContext(), 64);

        	Instruction* realVal = nullptr;

        	for(auto &I:realVars)
        	{
        		AllocaInst* allocaI = cast<AllocaInst>(I);

        		if(allocaI->getAllocatedType() == UserOfGEP.back()->getType())
        		{
        			realVal = I;
        			break;
        		}
        	}
        	if(!realVal)
        	{
        		realVal = new AllocaInst(resultTy, "", &*inst_begin(F));  // i64 index;
        		realVars.push_back(realVal);
        	}


        	Instruction *newGEP, *loadGEP, *storeGEP;
        	uint64_t pos = 0;

        	for (uint64_t i = 0; i < usedCacheLineNum; i++)
        	{
        		pos = (i*cacheLineSize)/sizeElement;
        		if((i*cacheLineSize)%sizeElement !=0)
        			pos++;

        		newGEP = indexInst->clone();
        		newGEP->replaceUsesOfWith(truePos, ConstantInt::get(i64, pos));
        		newGEP->insertBefore(indexInst);

        		loadGEP = UserOfGEP.back()->clone();
        		loadGEP->replaceUsesOfWith(indexInst, newGEP);
        		loadGEP->insertBefore(indexInst);
        		storeGEP = new StoreInst(loadGEP, realVal, indexInst);
        	}

        	this->tmpInst = UserOfGEP.back();
        	this->tmpVar = indexInst;
        	this->tmpInst->setName("Mitigated");
        	return UserOfGEP.back();
        }


        void mitigateIndex(Function &F)
        {

        	AliasAnalysis* AA = &getAnalysis<AAResultsWrapperPass>().getAAResults();
        	this->tmpInst = nullptr;
        	this->cacheAnalysis = new CacheAnalysis(F, DT, AA,this->cacheLineSize , this->cacheLineNum);
        	this->cacheAnalysis->InitModel();
        	Instruction* inst;
        	inst = &*(inst_begin(F));

            bool findIndex;
            do
            {
            	for (inst_iterator it = inst_begin(F); it != inst_end(F);++it)
            	{
            		if(inst && &*it != inst)
            			continue;
#ifdef USE_PRELOAD
            		inst = tryToMitigateIndexViaPreload(F, &*it);
#else
            		inst = tryToMitigateIndex(F, &*it);
#endif


            		if(inst)
            		{
            			indexCount++;
            			break;
            		}


            	}
            }
            while(inst);
        }
        
        bool UnrollLoopOnce(BasicBlock* bb)
        {
        	LoopInfo* LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
        	Loop* L = LI->getLoopFor(bb);

        	if(!L)
        		return false;

            ScalarEvolution *SE = &getAnalysis<ScalarEvolutionWrapperPass>().getSE();

            // Find trip count and trip multiple if count is not available
            unsigned TripCount = 0;
            unsigned TripMultiple = 1;
            // If there are multiple exiting blocks but one of them is the latch, use the
            // latch for the trip count estimation. Otherwise insist on a single exiting
            // block for the trip count estimation.
            BasicBlock *ExitingBlock = L->getLoopLatch();
            if (!ExitingBlock || !L->isLoopExiting(ExitingBlock))
            	ExitingBlock = L->getExitingBlock();
            if (ExitingBlock) {
            	TripCount = SE->getSmallConstantTripCount(L, ExitingBlock);
            	TripMultiple = SE->getSmallConstantTripMultiple(L, ExitingBlock);
            }

            if(TripCount < 2)
            	return false;

            BasicBlock *Preheader = L->getLoopPreheader();
            if (!Preheader) {
            	DEBUG(dbgs() << "  Can't unroll; loop preheader-insertion failed.\n");
            	return false;
            }

            BasicBlock *LatchBlock = L->getLoopLatch();
            if (!LatchBlock) {
            	DEBUG(dbgs() << "  Can't unroll; loop exit-block-insertion failed.\n");
            	return false;
            }

            // Loops with indirectbr cannot be cloned.
            if (!L->isSafeToClone()) {
            	DEBUG(dbgs() << "  Can't unroll; Loop body cannot be cloned.\n");
            	return false;
            }

            BasicBlock *Header = L->getHeader();
            BranchInst *BI = dyn_cast<BranchInst>(LatchBlock->getTerminator());

            if (!BI || BI->isUnconditional()) {
            	// The loop-rotate pass can be helpful to avoid this in many cases.
            	DEBUG(dbgs() <<
            			"  Can't unroll; loop not terminated by a conditional branch.\n");
            	return false;
            }

            if (Header->hasAddressTaken()) {
            	// The loop-rotate pass can be helpful to avoid this in many cases.
            	DEBUG(dbgs() <<
            			"  Won't unroll loop: address of header block is taken.\n");
            	return false;
            }

            // Effectively "DCE" unrolled iterations that are beyond the tripcount
            // and will never be executed.
            assert(TripMultiple > 0);
            assert(TripCount == 0 || TripCount % TripMultiple == 0);

            // Are we eliminating the loop control altogether?
            bool CompletelyUnroll = false;
            SmallVector<BasicBlock *, 4> ExitBlocks;
            L->getExitBlocks(ExitBlocks);
            std::vector<BasicBlock*> OriginalLoopBlocks = L->getBlocks();

            bool ContinueOnTrue = L->contains(BI->getSuccessor(0));
            BasicBlock *LoopExit = BI->getSuccessor(ContinueOnTrue);

            // For the first iteration of the loop, we should use the precloned values for
            // PHI nodes.  Insert associations now.
            ValueToValueMapTy LastValueMap;
            std::vector<PHINode*> OrigPHINode;
            for (BasicBlock::iterator I = Header->begin(); isa<PHINode>(I); ++I) {
            	OrigPHINode.push_back(cast<PHINode>(I));
            }

            BasicBlock* NewHeader;
            BasicBlock* NewLatch;

            // The current on-the-fly SSA update requires blocks to be processed in
            // reverse postorder so that LastValueMap contains the correct value at each
            // exit.
            LoopBlocksDFS DFS(L);
            DFS.perform(LI);

            // Stash the DFS iterators before adding blocks to the loop.
            LoopBlocksDFS::RPOIterator BlockBegin = DFS.beginRPO();
            LoopBlocksDFS::RPOIterator BlockEnd = DFS.endRPO();

            std::vector<BasicBlock*> UnrolledLoopBlocks = L->getBlocks();

            std::vector<BasicBlock*> NewBlocks;
            SmallDenseMap<const Loop *, Loop *, 4> NewLoops;
            NewLoops[L] = L;

            for (LoopBlocksDFS::RPOIterator BB = BlockBegin; BB != BlockEnd; ++BB) {
            	ValueToValueMapTy VMap;
            	BasicBlock *New = CloneBasicBlock(*BB, VMap, "lu.");
            	Header->getParent()->getBasicBlockList().push_back(New);

            	// Tell LI about New.
            	if (*BB == Header) {
            		assert(LI->getLoopFor(*BB) == L && "Header should not be in a sub-loop");
            		L->addBasicBlockToLoop(New, *LI);
            	} else {
            		// Figure out which loop New is in.
            		const Loop *OldLoop = LI->getLoopFor(*BB);
            		assert(OldLoop && "Should (at least) be in the loop being unrolled!");

            		Loop *&NewLoop = NewLoops[OldLoop];
            		if (!NewLoop) {
            			// Found a new sub-loop.
            			assert(*BB == OldLoop->getHeader() &&
            					"Header should be first in RPO");

            			Loop *NewLoopParent = NewLoops.lookup(OldLoop->getParentLoop());
            			assert(NewLoopParent &&
            					"Expected parent loop before sub-loop in RPO");
            			NewLoop = new Loop;
            			NewLoopParent->addChildLoop(NewLoop);
            		}
            		NewLoop->addBasicBlockToLoop(New, *LI);
            	}

            	if (*BB == Header)
            		// Loop over all of the PHI nodes in the block, changing them to use
            		// the incoming values from the previous block.
            		for (PHINode *OrigPHI : OrigPHINode) {
            			PHINode *NewPHI = cast<PHINode>(VMap[OrigPHI]);
            			Value *InVal = NewPHI->getIncomingValueForBlock(Preheader);
            			VMap[OrigPHI] = InVal;
            			New->getInstList().erase(NewPHI);
            		}


            	// Update our running map of newest clones
            	LastValueMap[*BB] = New;
            	for (ValueToValueMapTy::iterator VI = VMap.begin(), VE = VMap.end();
            			VI != VE; ++VI)
            		LastValueMap[VI->first] = VI->second;

            	// Keep track of new headers and latches as we create them, so that
            	// we can insert the proper branches later.
            	if (*BB == Header)
            		NewHeader = New;
            	if (*BB == LatchBlock)
            		NewLatch = New;

            	NewBlocks.push_back(New);
            	UnrolledLoopBlocks.push_back(New);
            }

            // Remap all instructions in the most recent iteration
            for (BasicBlock *NewBlock : NewBlocks)
            	for (Instruction &I : *NewBlock)
            		remapInstruction(&I, LastValueMap);


            for (PHINode *PN : OrigPHINode) {
            	PN->removeIncomingValue(Preheader, false);
            	Value *InVal = PN->getIncomingValueForBlock(LatchBlock);

            	// If this value was defined in the loop, take the value defined by the
            	// last iteration of the loop.
            	if (Instruction *InValI = dyn_cast<Instruction>(InVal)) {
            		if (L->contains(InValI))
            			InVal = LastValueMap[InVal];
            	}
            	assert(NewLatch == LastValueMap[LatchBlock] && "bad last latch");
            	PN->addIncoming(InVal, NewLatch);

              }

            // Now that all the basic blocks for the unrolled iterations are in place,
            // set up the branches to connect them.
            BranchInst *Term = cast<BranchInst>(NewLatch->getTerminator());
            BranchInst::Create(Header, Term);
            Term->eraseFromParent();

            Term = cast<BranchInst>(Preheader->getTerminator());
            BranchInst::Create(NewHeader, Term);
            Term->eraseFromParent();


            // At this point, the code is well formed.  We now do a quick sweep over the
            // inserted code, doing constant propagation and dead code elimination as we
            // go.
            const DataLayout &DL = Header->getModule()->getDataLayout();
            const std::vector<BasicBlock*> &NewLoopBlocks = L->getBlocks();
            for (BasicBlock *BB : NewLoopBlocks) {
            	for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ) {
            		Instruction *Inst = &*I++;

            		if (Value *V = SimplifyInstruction(Inst, DL))
            			if (LI->replacementPreservesLCSSAForm(Inst, V))
            				Inst->replaceAllUsesWith(V);
            		if (isInstructionTriviallyDead(Inst))
            			BB->getInstList().erase(Inst);
            	}
            }

            Loop *OuterL = L->getParentLoop();
            return true;
        }

        /// Convert the instruction operands from referencing the current values into
        /// those specified by VMap.
        static inline void remapInstruction(Instruction *I, ValueToValueMapTy &VMap)
        {
        	for (unsigned op = 0, E = I->getNumOperands(); op != E; ++op) {
        		Value *Op = I->getOperand(op);
        		ValueToValueMapTy::iterator It = VMap.find(Op);
        		if (It != VMap.end())
        			I->setOperand(op, It->second);
        	}

        	if (PHINode *PN = dyn_cast<PHINode>(I)) {
        		for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) {
        			ValueToValueMapTy::iterator It = VMap.find(PN->getIncomingBlock(i));
        			if (It != VMap.end())
        				PN->setIncomingBlock(i, cast<BasicBlock>(It->second));
        		}
        	}
        }




        bool runOnFunction(Function &F) override {

        	//errs() << F.getName() << "\n";
        	if(F.getName() == "main")
        		return true;
        	if(F.hasLinkOnceLinkage() | F.hasLinkOnceODRLinkage())
        		return true;

            indexCount =0;
            branchCount = 0;
            realVars.clear();
//            index = nullptr;

            vector<bool> taintSourceEx;
            taintSourceEx.push_back(true);
            if(F.getName() == "mult8" || F.getName() == "exp8")
            	taintSourceEx.push_back(true);
            if(F.getName() == "blowfish_do_encrypt")
            {
            	taintSourceEx.push_back(true);
            	taintSourceEx.push_back(true);
            }

            taintSourceEx.push_back(false);
            taintSourceEx.push_back(false);
            taintSourceEx.push_back(false);
            taintSourceEx.push_back(false);
            taintSourceEx.push_back(false);
            taintSourceEx.push_back(false);
            taintSourceEx.push_back(false);
            
            taintAnalysis = new TaintAnalysis(F,taintSourceEx);
            taintAnalysis->visit(F);
            //DEBUG(dbgs() << "Check if GEP need mitigate: "; taintAnalysis->print(); dbgs() << "\n");
            //taintAnalysis->print();
            mitigateIndex(F);
            errs() << "we have mitigated "<< indexCount << " sensitive index in Function[" <<F.getName()<<"].\n";

            mitigateBranch(&F);
            errs() << "we have mitigated "<< branchCount << " sensitive branches in Function[" <<F.getName()<<"].\n";
            //errs() << "Now Function[" <<F.getName()<<"] is: \n";
            //F.print(errs());
            return true;
        }

        bool mitigateBranch(Function* F)
        {
        	DT.recalculate(*F);
        	SmallVector<BasicBlock*, 32> WL;
        	addDTNode(DT.getRootNode(), &WL);

        	for(SmallVector<BasicBlock*, 32>::iterator ni=WL.begin(), ne=WL.end(); ni!=ne; ni++)
        	{
        		BasicBlock* bb = *ni;
        		if (balanceBranch(bb, F, &DT))
        		{
        			branchCount ++;
        			DT.recalculate(*F);
        		}
        	}
        }
        bool isSensitive(BranchInst* BrInst)
        {
            if (BrInst->isConditional()) {
                if (CmpInst *C = dyn_cast<CmpInst>(BrInst->getCondition())) {
                    Value *anOp = 0;
                    for (unsigned i = 0; i < C->getNumOperands(); ++i) {
                        anOp = C->getOperand(i);
                        if (taintAnalysis->isValueTainted(anOp))
                            return true;
                    }
                }
            }
            return false;
        }
        
        int addDTNode(DomTreeNode *root, SmallVector<BasicBlock*, 32>* WL)
        {
        	for (DomTreeNode::iterator child = root->begin(); child != root->end(); ++child)
        	{
        		DomTreeNode *node = *child;
        		addDTNode(node, WL);
        	}
        	WL->push_back(root->getBlock());
        }

        bool IsBalanced(BasicBlock* left, BasicBlock* right)
        {
        	BasicBlock::iterator ifT = left->begin(), ifF = right->begin();

        	while(ifT!= left->end() && ifF!= right->end())
        	{
        		if( (*ifT).getType() != (*ifF).getType())
        		{
        			return false;
        		}
        		++ifT;
        		++ifF;
        	}

        	if(ifT != left->end() || ifF != right->end())
        	{
        		return false;
        	}

        	return true;
        }

        bool IsBalancedDomTree(DomTreeNode *left, DomTreeNode *right, DominatorTree* DT)
        {
        	if(left->getNumChildren() != right->getNumChildren())
        		return false;

        	BasicBlock* leftBB = left->getBlock();
        	BasicBlock* rightBB = right->getBlock();
        	if(!IsBalanced(leftBB, rightBB))
        		return false;

        	if(leftBB->getTerminator()->getNumSuccessors()!=rightBB->getTerminator()->getNumSuccessors())
        		return false;



        	for (DomTreeNode::iterator IL = left->begin(), IR = right->begin();
        			IL != left->end()&&IR != left->end(); ++IL, ++IR)
        	{
        		if(!IsBalancedDomTree(*IL, *IR, DT))
        			return false;
        	}

        	return true;
        }

        bool balanceBranch(BasicBlock* root, Function* F, DominatorTree* DT)
        {
        	BranchInst *BrInst = dyn_cast<BranchInst>(root->getTerminator());
        	if (!BrInst)
        		return false;  // reach return statement
        	if (!isSensitive(BrInst))
        		return false;

        	DomTreeNode *S0 = DT->getNode(root);
        	DomTreeNode *S1 = DT->getNode(BrInst->getSuccessor(0));
        	DomTreeNode *S2 = DT->getNode(BrInst->getSuccessor(1));
        	DomTreeNode *S3 = nullptr;
        	BasicBlock *EndBB = BrInst->getSuccessor(1);

        	bool hasElse = false; // (S1->getNumChildren() == 3);
        	for (DomTreeNode::iterator child = S0->begin(); child != S0->end(); ++child)
        	{
        		DomTreeNode *node = *child;
        		if (node == S1 || node == S2)
        			continue;
        		if (node->getIDom() == S0)
        		{
        			hasElse = true;
        			EndBB = node->getBlock();
        			break;
        		}
        	}
        	BasicBlock *IfTrue = S1->getBlock();
//        	BasicBlock *IfFalse = S2->getBlock();
          	// add the replace relation from end block to else block. So the dummy if blocks are insert in front of else blocks
			if (hasElse)
			{
				S3 = DT->getNode(EndBB);
//				if(IsBalancedDomTree(S1, S2, DT))
//					return false;

				errs() << "**Found sensitive branch with both if and else branches: \n\t";
				BrInst->print(errs()); errs() << "  !!\n";
				return false;
			}

			bool IfBeforeElse = false;
			for (auto it = pred_begin(EndBB), et = pred_end(EndBB); it != et; ++it)
			{
				BasicBlock* predecessor = *it;
				if((predecessor != root) && (DT->dominates(IfTrue,predecessor)))
					IfBeforeElse = true;
			}

			if(!IfBeforeElse)
			{
				IfTrue = S2->getBlock();
				EndBB = S1->getBlock();
			}

        	Value* cond = BrInst->getCondition();
        	BrInst->eraseFromParent();
        	BranchInst *j2If = BranchInst::Create(IfTrue, root);

        	SmallVector<BasicBlock*, 8> bl;
        	DT->getDescendants(IfTrue, bl);

        	for(auto &bb : bl)
        	{
        		for (BasicBlock::iterator i = bb->begin(), e = bb->end(); i != e; ++i)
        		{

        			if (StoreInst *storeI = dyn_cast<StoreInst>(i))
        			{
        				Instruction* loadI = new LoadInst(storeI->getPointerOperand(), "", storeI);
#ifdef USE_BITWISE
        				SExtInst *ext = new SExtInst(cond, loadI->getType(),"", storeI);
        				BinaryOperator *negext = BinaryOperator::CreateXor(ext,ConstantInt::get(loadI->getType(), -1),"", storeI);

        				BinaryOperator *andext, *andnegext;
        				if(IfBeforeElse)
        				{
        					andext = BinaryOperator::CreateAnd(ext,storeI->getValueOperand(),"", storeI);
        					andnegext = BinaryOperator::CreateAnd(negext,loadI,"", storeI);
        				}
        				else
        				{
        					andext = BinaryOperator::CreateAnd(negext,storeI->getValueOperand(),"", storeI);
        					andnegext = BinaryOperator::CreateAnd(ext,loadI,"", storeI);
        				}
        				Instruction *selectVal = BinaryOperator::CreateXor(andext, andnegext,"",storeI);
#endif

#ifdef USE_CMOV
        				unsigned int size = loadI->getType()->getPrimitiveSizeInBits();
        				IntegerType *i16 = IntegerType::get(F->getContext(), 16);
        				Value* valueOp = storeI->getValueOperand();

                		if(size < 16)
                		{
                			ZExtInst* zextPtr = new ZExtInst(loadI, i16,"", storeI);
                			ZExtInst* zextVal = new ZExtInst(valueOp, i16,"", storeI);
                			loadI = zextPtr;
                			valueOp = zextVal;
                		}


                		Instruction *selectVal = SelectInst::Create(cond,valueOp,loadI,"",storeI);

        	    		if(size < 16)
        	    		{
        	    			TruncInst* trunc = new TruncInst(selectVal, storeI->getValueOperand()->getType(),"", storeI);
        	    			selectVal = trunc;
        	    		}
#endif
        				storeI->setOperand(0, selectVal);
        			}
        			// replace use out of current block, even it's not store inst
        		}
        	}

        	for (BasicBlock::iterator i = EndBB->begin(), e = EndBB->end(); i != e; ++i)
        	{
        		if(PHINode* phi = dyn_cast<PHINode>(i))
        		{
        			Value* val = phi->removeIncomingValue(root, true);
        			Instruction* phiNext = phi->getNextNode();

#ifdef USE_BITWISE
        			SExtInst *ext = new SExtInst(cond, phi->getType(),"", phiNext);
        			BinaryOperator *negext = BinaryOperator::CreateXor(ext,ConstantInt::get(phi->getType(), -1),"", phiNext);

        			BinaryOperator *andext, *andnegext;
        			if(IfBeforeElse)
        			{
        				andext = BinaryOperator::CreateAnd(ext,phi,"", phiNext);
        				andnegext = BinaryOperator::CreateAnd(negext,val,"", phiNext);
        			}
        			else
        			{
        				andext = BinaryOperator::CreateAnd(negext,phi,"", phiNext);
        				andnegext = BinaryOperator::CreateAnd(ext,val,"", phiNext);
        			}

        			BinaryOperator *selectVal = BinaryOperator::CreateXor(andext, andnegext,"",phiNext);
        			for (auto &U : phi->uses()) {
        				User *user = U.getUser();  // A User is anything with operands.
        				if(user != andext)
        					user->setOperand(U.getOperandNo(), selectVal);
        			}
#endif

#ifdef USE_CMOV
        			Instruction* Phi = phi;
      				unsigned int size = val->getType()->getPrimitiveSizeInBits();
      				IntegerType *i16 = IntegerType::get(F->getContext(), 16);

      				if(size < 16)
      				{
      					ZExtInst* zextVal= new ZExtInst(val, i16,"", phiNext);
      					ZExtInst* zextPhi = new ZExtInst(Phi, i16,"", phiNext);
      					Phi = zextPhi;
      					val = zextVal;
      				}

      				Instruction *selectVal;
      				selectVal = SelectInst::Create(cond,Phi,val,"",phiNext);

      				if(size < 16)
      				{
      					TruncInst* trunc = new TruncInst(selectVal, val->getType(),"", phiNext);
      					selectVal = trunc;
      				}


        			for (auto &U : phi->uses()) {
        				User *user = U.getUser();  // A User is anything with operands.
        				if(user != Phi && user != selectVal)
        					user->setOperand(U.getOperandNo(), selectVal);
        			}
#endif
        		}
        		else
        		{
        			break;
        		}
        	}
        	return true;

        }
        bool balanceBranch_legacy(BasicBlock* root, Function* F, DominatorTree* DT)
        {
        	BranchInst *BrInst = dyn_cast<BranchInst>(root->getTerminator());
        	if (!BrInst)
        		return false;  // reach return statement
        	if (!isSensitive(BrInst))
        		return false;

        	DomTreeNode *S0 = DT->getNode(root);
        	DomTreeNode *S1 = DT->getNode(BrInst->getSuccessor(0));
        	DomTreeNode *S2 = DT->getNode(BrInst->getSuccessor(1));
        	DomTreeNode *S3 = nullptr;
        	BasicBlock *EndBB = BrInst->getSuccessor(1);

        	bool hasElse = false; // (S0->getNumChildren() == 3);
        	for (DomTreeNode::iterator child = S0->begin(); child != S0->end(); ++child)
        	{
        		DomTreeNode *node = *child;
        		if (node == S1 || node == S2)
        			continue;
        		if (node->getIDom() == S0)
        		{
        			hasElse = true;
        			EndBB = node->getBlock();
        			break;
        		}
        	}

        	BasicBlock *IfTrue = S1->getBlock();
        	BasicBlock *IfFalse = S2->getBlock();
        	ValueToValueMap DummyInstMap; //FIXME: do i need to track dummy inst across bb? or just inside bb?
        	ValueToValueMap DummyBBMap;

        	// add the replace relation from end block to else block. So the dummy if blocks are insert in front of else blocks
        	if (hasElse)
        	{
        		S3 = DT->getNode(EndBB);
        		DummyBBMap[EndBB] = IfFalse;

        		if(IsBalancedDomTree(S1, S2, DT))
        			return false;
        	}

        	DEBUG(dbgs() << "Try to mitigate this branch:"; BrInst->print(errs());; dbgs() << "\n");

        	PHINode* phi = dyn_cast<PHINode>(&EndBB->front());
        	SmallVector<BasicBlock*, 8> PhiBBIf;
        	SmallVector<BasicBlock*, 8> PhiBBElse;
        	if(phi)
        	{
        		for (auto it = pred_begin(EndBB), et = pred_end(EndBB); it != et; ++it)
        		{
        			BasicBlock* predecessor = *it;
        			if(DT->dominates(IfTrue,predecessor))
        			{
        				PhiBBIf.push_back(predecessor);
        			}
        			else if(hasElse)
        			{
        				if(DT->dominates(IfTrue,predecessor))
        				{
        					PhiBBElse.push_back(predecessor);
        				}
        				else
        				{
        					errs() << "Error: An invalid phi node with else branch: ";
        					phi->print(dbgs());
        				}

        			}
        			else
        			{
        				if(predecessor != root)
        				{
        					errs() << "Error: An invalid phi node without else branch: ";
        					phi->print(dbgs());
        				}
        				else
        					PhiBBElse.push_back(predecessor);
        			}
        		}
        	}


        	//clone the 1st block in if branch
        	std::vector<Instruction *> DupBBInsts = BasicBlockClone(*IfTrue, *F, DummyInstMap);
        	BasicBlock *DupIfTrue = BasicBlock::Create(F->getContext(), "", F, IfFalse);

        	for (auto i : DupBBInsts)
        	{
        		DupIfTrue->getInstList().push_back(i);
        	}
        	DummyBBMap[IfTrue] = DupIfTrue;



        	SmallVector<DomTreeNode*, 8> WL;
        	WL.push_back(S1);

        	while (!WL.empty()) {
        		DomTreeNode *N = WL.pop_back_val();
        		BasicBlock* DummyNBB = (BasicBlock *)DummyBBMap[N->getBlock()];
        		Instruction *termInst = DummyNBB->getTerminator();

        		for (DomTreeNode::iterator child = N->begin(); child != N->end(); ++child)
        		{
        			DomTreeNode *node = *child;
        			WL.push_back(node);

        			//create a new block
        			BasicBlock *DupBB = BasicBlock::Create(F->getContext(), "", F, IfFalse);
        			DupBBInsts = BasicBlockClone(*(node->getBlock()), *F, DummyInstMap);
        			for (auto i : DupBBInsts)
        			{
        				DupBB->getInstList().push_back(i);
        			}
        			DummyBBMap[node->getBlock()] = DupBB;
        		}

        		for (auto &mapI : DummyBBMap)
        		{
        			BasicBlock *oldBB = (BasicBlock *)(&(*mapI.first));
        			BasicBlock *newBB = (BasicBlock *)(&(*mapI.second));
        			termInst->replaceUsesOfWith(oldBB, newBB);
        		}
        	}

        	if(phi)
        	{
        		if(!hasElse)
        		{
        			Value* headVal = phi->getIncomingValueForBlock(root);
        			for(auto bb : PhiBBIf)
        			{
        				phi->addIncoming(headVal,  (BasicBlock *)DummyBBMap[&*bb]);
        			}
        			phi->removeIncomingValue(root);
        		}
        	}



        	if (hasElse)
        	{
        		DummyInstMap.clear();
        		DummyBBMap.clear();
        		WL.clear();

        		// add the replace relation from end block to if block. So the dummy else blocks are insert in front of if blocks
        		//DummyBBMap[S3->getBlock()] = S1->getBlock();

        		DupBBInsts = BasicBlockClone(*(S2->getBlock()), *F, DummyInstMap);
        		BasicBlock *DupElseBB = BasicBlock::Create(F->getContext(), "", F, DupIfTrue);

        		for (auto i : DupBBInsts)
        		{
        			DupElseBB->getInstList().push_back(i);
        		}
        		DummyBBMap[S2->getBlock()] = DupElseBB;


        		WL.push_back(S2);
        		while (!WL.empty()) {
        			DomTreeNode *N = WL.pop_back_val();
        			Instruction *termInst = ((BasicBlock *)DummyBBMap[N->getBlock()])->getTerminator();

        			for (DomTreeNode::iterator child = N->begin(); child != N->end(); ++child)
        			{
        				DomTreeNode *node = *child;
        				WL.push_back(node);

        				//create a new block
        				BasicBlock* DupBB = BasicBlock::Create(F->getContext(), "", F, BrInst->getSuccessor(0));
        				DupBBInsts = BasicBlockClone(*(node->getBlock()), *F, DummyInstMap);
        				for (auto i : DupBBInsts)
        				{
        					DupBB->getInstList().push_back(i);
        				}
        				DummyBBMap[node->getBlock()] = DupBB;
        			}

        			for (auto &mapI : DummyBBMap)
        			{
        				BasicBlock *oldBB = (BasicBlock *)(&(*mapI.first));
        				BasicBlock *newBB = (BasicBlock *)(&(*mapI.second));
        				termInst->replaceUsesOfWith(oldBB, newBB);
        			}

        		}

        		IfTrue->getTerminator()->replaceUsesOfWith(EndBB, DupElseBB);
        		for (DomTreeNode::iterator child = S1->begin(); child != S1->end(); ++child)
        		{
        			(*child)->getBlock()->getTerminator()->replaceUsesOfWith(EndBB, DupElseBB);
        		}


        		if(phi)
        		{
        			PHINode* dupPhi = (PHINode*)phi->clone();

        			for(auto bb : PhiBBElse)
        			{
        				if(dupPhi->getBasicBlockIndex(&*bb) >= 0)
        					dupPhi->removeIncomingValue(&*bb);
        				phi->addIncoming(dupPhi, (BasicBlock *)DummyBBMap[&*bb]);
        			}

        			DupElseBB->getInstList().push_front(dupPhi);

        			for(auto bb : PhiBBIf)
        			{
        				if(phi->getBasicBlockIndex(&*bb) >= 0)
        					phi->removeIncomingValue(&*bb);
        			}
        		}

        	}

        	//connect the dummy blocks only after all its done, to aviod change the DomTree
        	BrInst->setSuccessor(1, DupIfTrue);
        	return true;

        }



        
        std::vector<Instruction *> BasicBlockClone(BasicBlock &BB,Function &F, ValueToValueMap &DummyInstMap)
        {
            Instruction *Inst1 = &*inst_begin(F);
            std::vector<Instruction *> newInsts;
            
            for (BasicBlock::iterator i = BB.begin(), e = BB.end(); i != e; ++i)
            {
                Instruction *dummyInst;
                if (StoreInst *storeI = dyn_cast<StoreInst>(i))
                {
                    PointerType* PT = cast<PointerType>(storeI->getPointerOperand()->getType());
                    AllocaInst *dummyAssignVar = new AllocaInst(PT->getElementType(),"",Inst1); // create a var which is as the same type as ptr in store
                    dummyInst = new StoreInst(storeI->getValueOperand(),dummyAssignVar);
                }
                else
                {
                    Instruction *noneAssignInst = &*i;
                    dummyInst = noneAssignInst->clone();
                    DummyInstMap[noneAssignInst] = dummyInst;
                }
                
                for(auto &mapI:DummyInstMap)
                {
                    Instruction *oldInst = (Instruction *)(&(*mapI.first));
                    Instruction *newInst = (Instruction *)(&(*mapI.second));
                    
                    for(auto U : mapI.first->users())
                    {  // U is of type User*
                        if (auto I = dyn_cast<Instruction>(U))
                        {
                            // an instruction uses oldInst
                            if(I == dummyInst)
                            {
                                dummyInst->replaceUsesOfWith(oldInst, newInst);
                            }
                        }
                    }
                }
                newInsts.push_back(dummyInst);
            }
            return newInsts;
        }
        
        
        void getAnalysisUsage(AnalysisUsage &AU) const override {
            AU.addRequiredTransitive<AAResultsWrapperPass>();
            AU.addRequiredTransitive<AAResultsWrapperPass>();
            AU.addRequired<LoopInfoWrapperPass>();
            AU.addRequired<ScalarEvolutionWrapperPass>();
            AU.addRequired<AssumptionCacheTracker>();
        }
        
        
    };
}

char Branch::ID = 0;
static RegisterPass<Branch> X("branch", "Sensitive Branch Mitigation Pass");

