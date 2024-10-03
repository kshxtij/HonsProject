#include <llvm/IR/DebugInfo.h>
#include <llvm/Pass.h>
#include <llvm/IR/Instructions.h>
#include "llvm/IR/Instruction.h"
#include <llvm/Support/Debug.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Analysis/CallGraph.h>
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"  
#include "llvm/IR/InstrTypes.h" 
#include "llvm/IR/BasicBlock.h" 
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include <llvm/IR/LegacyPassManager.h>
#include <map> 
#include <vector> 
#include <stdlib.h>
#include <assert.h>
#include "llvm/IR/CFG.h" 
#include "llvm/Transforms/Utils/BasicBlockUtils.h" 
#include "llvm/IR/IRBuilder.h"

#include "CallGraph.h"
#include "../Config.h"
#include "../Common.h"


void CallGraphPass::findFuncArgStoredCall(CallInst *CI, Value *Arg, unsigned index){

    if (Function *F = dyn_cast<Function>(Arg)) {

        hash<string> str_hash;
        size_t callhash = callHash(CI);
        size_t callidhash = callhash + str_hash(to_string(index));
        argStoreFuncSet[callidhash].insert(F);
        return;
    }

    //Arg is not a functino, but has func type
    Type* ArgTy = Arg->getType();
    //This check is necessary because ArgTy is always a pointer type
    if(ArgTy->isPointerTy()){
        ArgTy = ArgTy->getPointerElementType();
    }

    if(!ArgTy->isFunctionTy()){
        return;
    }

    //OP<<"Call: "<<*CI<<"\n";
    //OP<<"has function arg\n";

    Function* CIParrentFunc = CI->getFunction();
    set<Value *>argset;
    argset.clear();
    if(CIParrentFunc) {
        for(auto it = CIParrentFunc->arg_begin(); it != CIParrentFunc->arg_end();it++){
            argset.insert(it);
        }
    }

    std::list<Value *> EV; //BFS record list
    std::set<Value *> PV; //Global value set to avoid loop
    EV.clear();
    PV.clear();
    EV.push_back(Arg);

    while (!EV.empty()) {
        Value *TV = EV.front(); //Current checking value
		EV.pop_front();
            
        if (PV.find(TV) != PV.end())
			continue;
        PV.insert(TV);

        auto globalvar = dyn_cast<GlobalValue>(TV);
        if(globalvar){

            continue;
        }

        //Current call comes from parrent function
        if(argset.count(TV) == 1){
            hash<string> str_hash;
            size_t callhash = callHash(CI);
            size_t callidhash = callhash + str_hash(to_string(index));
            //argStoreFuncTransitMap[].insert();
            continue;
        }

        LoadInst* LI = dyn_cast<LoadInst>(TV);
		if(LI){
			Value *LPO = LI->getPointerOperand();
            EV.push_back(LPO);

			//Get all stored values
            for(User *U : LPO->users()){
                StoreInst *STI = dyn_cast<StoreInst>(U);
                if(STI){
                    
                    Value* vop = STI->getValueOperand(); // store vop to pop
                    Value* pop = STI->getPointerOperand();
                    
                    if(ConstantData *Ct = dyn_cast<ConstantData>(vop))
                        continue;

					//There must be a path from the store to the load
                    if(pop == LPO && checkBlockPairConnectivity(STI->getParent(), LI->getParent())){
                        EV.push_back(vop);
                    }
                }
            }
			continue;
		}

        GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(TV);
        if(GEP){
			Value* vop = GEP->getPointerOperand();
            EV.push_back(vop);
            continue;
		}

        UnaryInstruction *UI = dyn_cast<UnaryInstruction>(TV);
		if(UI){
			EV.push_back(UI->getOperand(0));
			continue;
		}

        //The return value is a function pointer
        CallInst* CAI = dyn_cast<CallInst>(TV);
        if(CAI){
            OP<<"comes from call\n";
            continue;
        }
    
    }
}


void CallGraphPass::getICallSource(CallInst *CI, map<Value*, SourceFlag> &sourceMap){
    
    Function* F = CI->getFunction();
    set<Value *>argset;
    argset.clear();
    if(F) {
        for(auto it = F->arg_begin(); it != F->arg_end();it++){
            argset.insert(it);
        }
    }

    Value *CV = CI->getCalledOperand();

    std::list<Value *> EV; //BFS record list
    std::set<Value *> PV; //Global value set to avoid loop
    EV.clear();
    PV.clear();
    EV.push_back(CV);

    while (!EV.empty()) {
        Value *TV = EV.front(); //Current checking value
		EV.pop_front();
            
        if (PV.find(TV) != PV.end()) //Avoid loop
			continue;
        PV.insert(TV);

        //OP<<"TV: "<<*TV<<"\n";

        //CI comes from a global variable
        auto globalvar = dyn_cast<GlobalValue>(TV);
        if(globalvar){
            //OP<<"global: "<<*TV<<"\n";
            auto lkTy = globalvar->getLinkage();
            if(lkTy == llvm::GlobalValue::InternalLinkage || lkTy == llvm::GlobalValue::PrivateLinkage){
                //OP<<"internal\n";
                sourceMap[TV] = Internal_Global;
            }
            else{
                //OP<<"external\n";
                sourceMap[TV] = External_Global;
            }
            
            continue;
        }

        //CI comes from the arguments of its caller
        if(argset.count(TV) == 1){
            sourceMap[TV] = Argument;
            continue;
        }

        //CI comes from the return value of a callee
        CallInst *CAI = dyn_cast<CallInst>(TV);
        if(CAI){
            sourceMap[TV] = Return;
            continue;
        }

        //CI comes from a local value, we need to chech the use of this value
        AllocaInst *AI = dyn_cast<AllocaInst>(TV);
        if(AI){
            sourceMap[TV] = Local;
            continue;
        }

        //CI comes from a func, e.g., a func is stored in the icall value
        Function *innerF = dyn_cast<Function>(TV);
        if(innerF){
            sourceMap[TV] = InnerFunction;
            continue;
        }

        //Find what is stored 
        LoadInst* LI = dyn_cast<LoadInst>(TV);
		if(LI){
			Value *LPO = LI->getPointerOperand();
            /*AllocaInst *AI = dyn_cast<AllocaInst>(LPO);
            if(!AI){
                EV.push_back(LPO);
            }*/
            EV.push_back(LPO);

            //If TV comes from global, we will check it later
            auto globalvar = dyn_cast<GlobalValue>(LPO);
            if(globalvar)
                continue;
            
            GEPOperator *GEPO = dyn_cast<GEPOperator>(LPO);
            if(GEPO){
                Value* vop = GEPO->getPointerOperand();
                EV.push_back(vop);
                continue;
            }

			//Get all stored values
            for(User *U : LPO->users()){
                //OP<<"user: "<<*U<<"\n";
                StoreInst *STI = dyn_cast<StoreInst>(U);
                if(STI){
                    
                    Value* vop = STI->getValueOperand(); // store vop to pop
                    Value* pop = STI->getPointerOperand();
                    
					//Store constant is not considered
                    if(ConstantData *Ct = dyn_cast<ConstantData>(vop))
                        continue;

                    EV.push_back(vop);
                }
            }
			continue;
		}

        PHINode *PHI = dyn_cast<PHINode>(TV);
        if(PHI){
            for (unsigned i = 0, e = PHI->getNumIncomingValues(); i != e; ++i){
                Value *IV = PHI->getIncomingValue(i);
                if(ConstantData *Ct = dyn_cast<ConstantData>(IV))
                    continue;
                EV.push_back(IV);
            }
            continue;
        }

        IntToPtrInst *ITPI = dyn_cast<IntToPtrInst>(TV);
        if(ITPI){
            EV.push_back(ITPI->getOperand(0));
            continue;
        }

        //here we need more accurate method
        GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(TV);
        if(GEP){
            sourceMap[TV] = Invalid;
            continue;
		}

        GEPOperator *GEPO = dyn_cast<GEPOperator>(TV);
        if(GEPO){
            //Value* vop = GEPO->getPointerOperand();
            //EV.push_back(vop);
            sourceMap[TV] = Invalid;
            continue;
        }

        SelectInst *SLI = dyn_cast<SelectInst>(TV);
        if(SLI){
            auto TrueV = SLI->getTrueValue();
            auto FalseV = SLI->getFalseValue();
            EV.push_back(TrueV);
            EV.push_back(FalseV);
            continue;
        }

        if(ConstantData *Ct = dyn_cast<ConstantData>(TV))
            continue;


        BitCastOperator *CastArg = dyn_cast<BitCastOperator>(TV);
        if(CastArg){
            EV.push_back(CastArg->getOperand(0));
            continue;
        }

        sourceMap[TV] = Invalid;
        
    }
}
