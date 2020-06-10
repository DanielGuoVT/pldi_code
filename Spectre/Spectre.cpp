//===- Spectre.cpp - Transform out leakage of Spectre attack ---------------===//
//   - 2/7/2018 Project init
//
//===---------------------------------------------------------------------------===//

#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Dominators.h"
#include "CacheSpecuAnalysis.h"
#include "llvm/Support/CommandLine.h"

using namespace std;
using namespace llvm;
using namespace spectre;
#define DEBUG_TYPE "spectre"

const char *AnnotationString = "specuAnaly";

static cl::opt<unsigned>
    SpecuDepth("specu", cl::init(0), cl::NotHidden,
                    cl::desc("The depth for speculative analysis, 0 for non-specu."));

static cl::opt<unsigned>
    Merge("merge", cl::init(0), cl::NotHidden,
                    cl::desc("The merge point for speculative execution, 0 for merge at the end of speculative execution; "
                    		"1 for merge early right at boundary."));

namespace {
    
    typedef DenseMap<const Value*, Value*> ValueToValueMap;
    // Hello - The first implementation, without getAnalysisUsage.
    struct Spectre : public FunctionPass {
        static char ID; // Pass identification, replacement for typeid
        Spectre() : FunctionPass(ID) {
        }
        DominatorTree DT;
        PostDominatorTree PDT;


        std::set<Function*> annotFuncs;

        virtual bool doInitialization(Module &M)override{
        	getAnnotatedFunctions(&M);
        	return false;
        }
        bool shouldAnalyFunc(Function &F){
        	return annotFuncs.find(&F)!=annotFuncs.end();
        }
        void getAnnotatedFunctions(Module *M){
        	for (Module::global_iterator I = M->global_begin(),
        			E = M->global_end();
        			I != E;
        			++I) {

        		if (I->getName() == "llvm.global.annotations") {
        			ConstantArray *CA = dyn_cast<ConstantArray>(I->getOperand(0));
        			for(auto OI = CA->op_begin(); OI != CA->op_end(); ++OI){
        				ConstantStruct *CS = dyn_cast<ConstantStruct>(OI->get());
        				Function *FUNC = dyn_cast<Function>(CS->getOperand(0)->getOperand(0));
        				GlobalVariable *AnnotationGL = dyn_cast<GlobalVariable>(CS->getOperand(1)->getOperand(0));
        				StringRef annotation = dyn_cast<ConstantDataArray>(AnnotationGL->getInitializer())->getAsCString();
        				if(annotation.compare(AnnotationString)==0){
        					annotFuncs.insert(FUNC);
        					//errs() << "Found annotated function " << FUNC->getName()<<"\n";
        				}
        			}
        		}
        	}
        }

        bool runOnFunction(Function &F) override {

//        	errs() << F.getName() << "\n";
        	if(shouldAnalyFunc(F) == false)
        		return true;

        	if(SpecuDepth > 0)
        	{
        		SpecuDepth = 20;
        		errs() << "\nSpeculatively Analyze function " << F.getName() << "\n";
        		if(Merge ==0)
        			errs() << "\twith Just-in-time merging.\n";
        		else
        			errs() << "\twith rollback merging.\n";

        	}
        	else
        	{
        		errs() << "Non-Speculatively Analyze function " << F.getName() << "\n";
        		if(Merge !=0)
        		{
        			errs()<<"Merge point used in non-speculative mod. Ignored!";
        			Merge =0;
        		}
        	}
        	DT.recalculate(F);
        	PDT.recalculate(F);

        	CacheSpecuAnalysis* cacheAnalysis = new CacheSpecuAnalysis(F, DT, PDT, nullptr, 64, 512, 1, SpecuDepth, Merge);
        	cacheAnalysis->InitModel();

        	cacheAnalysis->SpecuSim(&*F.begin(), &*F.end(), cacheAnalysis->model);
            return true;
        }
     
        void getAnalysisUsage(AnalysisUsage &AU) const override {
            AU.addRequiredTransitive<AAResultsWrapperPass>();
            AU.addRequiredTransitive<AAResultsWrapperPass>();
        }
        
        
    };
}

char Spectre::ID = 0;
static RegisterPass<Spectre> X("spectre", "Spectre attack mitigation Pass.");

