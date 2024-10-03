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

string getGlobalMacrosource(GlobalVariable* GV){

    if(!GV)
        return "";
    
    MDNode *N = GV->getMetadata("dbg");
    if (!N)
        return "";
    
    DIGlobalVariableExpression *DLGVE = dyn_cast<DIGlobalVariableExpression>(N);
    if(!DLGVE)
        return "";

    DIGlobalVariable* DIGV = DLGVE->getVariable();
    if(!DIGV)
        return "";
    
    string fn_str = getFileName(NULL, NULL, DIGV);
    unsigned lineno = DIGV->getLine();
    string source_line = getSourceLine(fn_str, lineno);

    //OP<<"FN: "<<FN<<"\n";
    //OP<<"source_line: "<<source_line<<"\n";

    return source_line;
}

bool CallGraphPass::FuncSetHandler(FuncSet FSet, CallInstSet &callset){

    bool batch_result = true;
    set<size_t> hashSet;
    hashSet.clear();
    for(Function *F : FSet){
        hashSet.clear();

        //Ignore funcs with an unknown prelayer
        if(Ctx->Global_EmptyTy_Funcs[funcHash(F, false)].count(F))
            return false;

        batch_result = FindNextLayer(F, hashSet, callset);
        if(batch_result == false)
            return false; 
    }

    //Here all FuncHandler must have succeed
    //Use type propagate and type cast info to generate a conservative hashset

    return true;
}

bool CallGraphPass::FindNextLayer(Function* F, set<size_t> &HashSet, CallInstSet &callset){

    if(F->getName() != "delayed_work_timer_fn")
        return false;

    OP<<"\nCurrent func: "<<F->getName()<<"\n";

    map<Value*, Value*> PreMap; //Record user info
    list<Value *>LV;
    set<Value *> GV; //Global value set to avoid loop
	for(User *U : F->users()){
        //OP<<"U: "<<*U<<"\n";
		LV.push_back(U);
        PreMap[U] = F;
	}

    while (!LV.empty()) {
        Value *TV = LV.front();
        Value *PreV = PreMap[TV];
        
        LV.pop_front();

        if (GV.find(TV) != GV.end()){
            continue;
        }
        GV.insert(TV);

        OP<<"TV: "<<*TV<<"\n";

        
        CallInst *CAI = dyn_cast<CallInst>(TV);
        if(CAI){
            
            //Ignore llvm func
            StringRef FName = getCalledFuncName(CAI);
            if(Ctx->DebugFuncs.count(FName.str())){
                continue;
            }

            //Direct call
            if(FName == F->getName())
                continue;
            
            //Indirect call
            //TODO: what if TV is the icall's arg?
            if (CAI->isIndirectCall()){
                Value *CO = CAI->getCalledOperand();
                if(CO == PreV){
                    callset.insert(CAI);
                    continue;
                }
            }

            if(!Ctx->Callees.count(CAI))
                continue;
        
            //Use as a func arg
            unsigned argnum = CAI->arg_size();
            int arg_index = -1;
            for(unsigned i = 0; i < argnum; i++){
                Value* arg = CAI->getArgOperand(i);
                if(arg == PreV){
                    arg_index = i;
                    break;
                }
            }

            if(arg_index == -1)
                return false;

            for(Function *f : Ctx->Callees[CAI]){
                //auto Arg = f->getArg(argnum);
                //LU.push_back(Arg);
                for (Function::arg_iterator FI = f->arg_begin(), 
                    FE = f->arg_end(); FI != FE; ++FI) {
                    unsigned argno = FI->getArgNo();
                    if(argno == arg_index)
                        LV.push_back(FI);
                }
            }
            continue;
        }

        //Used in initing global variables
        GlobalVariable* GV = dyn_cast<GlobalVariable>(TV);
        if(GV){

            if(GV->getName().contains("__UNIQUE_ID___addressable")){
                //OP<<"contain target\n";
                //Find the macro
                string source = getGlobalMacrosource(GV);
                if(source.size() != 0){
                    for(string safe_macro : Ctx->SafeMacros){
                        //OP<<"safe_macro: "<<safe_macro<<"\n";
                        if(checkStringContainSubString(source, safe_macro)){
                            //Aliased with a safe macro, stop further analysis
                            OP<<"is a target macro"<<"\n";
                            continue;
                        }
                    }
                }
            }

            if(GV->getName() == "llvm.used" || GV->getName() == "llvm.compiler.used"
                || GV->getName().contains("__start_set")){
                return false;
            }

            //Check the field that F initialized
            Constant *Ini = GV->getInitializer();
            if(!Ini)
                continue;
            
            //If f is used to init GV, we should have analyzed it in InitinGlobal.cc
            if(Func_Init_Map.count(GV)){
                map<Function*, set<size_t>> Init_List = Func_Init_Map[GV];
                for(size_t hash : Init_List[F]){
                    HashSet.insert(hash);

                }
            }
            else{
                return false;
            }

            continue;
        }

        //F is stored into sth
        StoreInst *SI = dyn_cast<StoreInst>(TV);
        if(SI){
            Value *PO = SI->getPointerOperand();
            Value *VO = SI->getValueOperand();

            if (isa<ConstantData>(VO))
                continue;
            

            //Check prelayer info
            set<Value*> VisitedSet;
            list<CompositeType> TyList;
            if (nextLayerBaseType_new(PO, TyList, VisitedSet, Precise_Mode)) {

                for(CompositeType CT : TyList){

                    Type* STy = CT.first;
                    int Idx = CT.second;

                    //OP<<"STy: "<<*STy<<"\n";
                    //OP<<"Idx: "<<Idx<<"\n";

                    size_t typehash = typeHash(STy);
                    size_t typeidhash = typeIdxHash(STy,Idx);
                    hashTypeMap[typehash] = STy;
                    hashIDTypeMap[typeidhash] = make_pair(STy,Idx);
                    

                    if(STy->getStructName().size() != 0){
                        auto Ty_name = STy->getStructName();
                        if(Ty_name.contains("anon") || Ty_name.contains("union"))
                            return false;

                        string parsed_Ty_name = parseIdentifiedStructName(Ty_name);
                        HashSet.insert(typeNameIdxHash(parsed_Ty_name, Idx));
                        hashIDTypeMap[typeNameIdxHash(parsed_Ty_name,Idx)] = make_pair(STy,Idx);
                    }
                    else{
                        string Ty_name = Ctx->Global_Literal_Struct_Map[typeHash(STy)];
                        if(Ty_name.size() == 0)
                            return false;

                        HashSet.insert(typeNameIdxHash(Ty_name, Idx));
                        hashIDTypeMap[typeNameIdxHash(Ty_name,Idx)] = make_pair(STy,Idx);
                        
                    }
                    
                }
                continue;
            }

            LV.push_back(PO);
            continue;
        }

        AllocaInst* ALI = dyn_cast<AllocaInst>(TV);
        llvm::Argument *Arg = dyn_cast<llvm::Argument>(TV);
        LoadInst* LI = dyn_cast<LoadInst>(TV);
        BitCastOperator *CastO = dyn_cast<BitCastOperator>(TV);
        ConstantAggregate* CA = dyn_cast<ConstantAggregate>(TV); //Usually the initializer of a global variable
        if(ALI || Arg || LI || CastO || CA){
            for(User *u : TV->users()){
                LV.push_back(u);
                PreMap[u] = TV;
            }
            continue;
        }

        ICmpInst* CMPI = dyn_cast<ICmpInst>(TV);
        if(CMPI){
            continue;
        }

        //Unkown cases
        OP<<"Unsupported inst: "<<*TV<<"\n";
        return false;

    }
    return true;

}