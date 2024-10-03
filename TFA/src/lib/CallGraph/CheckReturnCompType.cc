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

DenseMap<size_t, set<CallGraphPass::CompositeType>> CallGraphPass::FuncTypesMap;

//Find and collect functions that may return a composite type
//This usually is missed due to type cast from composite type to a pointer
void CallGraphPass::findTypeStoreFunc(Function* F){

	for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
		ReturnInst *RI = dyn_cast<ReturnInst>(&*i);
		if(RI){
			findTypeStoreValueFlow(F, RI);
		}
	}
}

void CallGraphPass::findTypeStoreValueFlow(Function* F, ReturnInst *RI){
	
	Value *RV = RI->getReturnValue();
	if (!RV)
		return;

	Type *RTy = RV->getType();
	if(!RTy->isPointerTy())
		return;

	std::set<Value *> PV; //Global value set to avoid loop
	std::list<Value *> EV; //BFS record list

	PV.clear();
	EV.clear();
	EV.push_back(RV);

	while (!EV.empty()) {

		Value *TV = EV.front(); //Current checking value
		EV.pop_front();

		if (PV.find(TV) != PV.end())
			continue;
		PV.insert(TV);

		LoadInst* LI = dyn_cast<LoadInst>(TV);
		if(LI){
			Value *LPO = LI->getPointerOperand();
            EV.push_back(LPO);

			//Get all stored values
            for(User *U : LPO->users()){
                StoreInst *STI = dyn_cast<StoreInst>(U);
                if(STI){
                    //OP<<"STI: "<<*STI<<"\n";
                    Value* vop = STI->getValueOperand(); // store vop to pop
                    Value* pop = STI->getPointerOperand();

					//Store constant is not considered
					//FIXME: vop could be global value or func declare
					 if(ConstantData *Ct = dyn_cast<ConstantData>(vop))
						continue;

					//There must be a path from the store to the load
                    EV.push_back(vop);
                }
            }
			continue;
		}

		if(GEPOperator *GEP = dyn_cast<GEPOperator>(TV)){
			
			Type *PTy = GEP->getPointerOperand()->getType();
			Type *Ty = PTy->getPointerElementType();
			Type *sTy = GEP->getSourceElementType();

			//Expect the PointerOperand is a struct
			//if (isCompositeType(Ty) && GEP->hasAllConstantIndices()) {
			if (Ty->isStructTy() && GEP->hasAllConstantIndices()) {
				//BTy = Ty;
				User::op_iterator ie = GEP->idx_end();
				ConstantInt *ConstI = dyn_cast<ConstantInt>((--ie)->get());
				int Idx = ConstI->getSExtValue();
				if(Idx < 0)
					continue;

				unsigned indice_num = GEP->getNumIndices();

				ConstantInt *ConstI_first = dyn_cast<ConstantInt>(GEP->idx_begin()->get());
				int Idx_first = ConstI_first->getSExtValue();
				if(Idx_first != 0 && indice_num>=2){
					if(Ty->isStructTy()){
						continue;
					}
				}
				
				if(indice_num < 2)
					continue;

				if(indice_num > 2){
					//OP<<"\nGEP: "<<*GEP<<"\n";
					//OP<<"indice_num > 2\n";
					vector<int> id_vec;
					id_vec.clear();
					for(auto it = GEP->idx_begin() + 1; it != GEP->idx_end(); it++){

						ConstantInt *ConstI = dyn_cast<ConstantInt>(it->get());
						int Id = ConstI->getSExtValue();
						if(Id < 0){
							continue;
						}
						id_vec.push_back(Id);
						//OP<<"--idx: "<<Id<<"\n";
					}

					Type* result_ty = getLayerTwoType(Ty,id_vec);
					if(result_ty){
						//OP<<"result ty: "<<*result_ty<<"\n";
						Ty = result_ty;
					}
				}
				
				size_t funchash = funcHash(F,true);
				FuncTypesMap[funchash].insert(std::make_pair(Ty, Idx));
			}

			continue;
		}


	}
}

//Use this on failure of nextLayerBaseType
void CallGraphPass::checkTypeStoreFunc(Value *V, set<CompositeType> &CTSet){

	std::set<Value *> PV; //Global value set to avoid loop
	std::list<Value *> EV; //BFS record list

	PV.clear();
	EV.clear();
	EV.push_back(V);

	while (!EV.empty()) {

		Value *TV = EV.front(); //Current checking value
		EV.pop_front();

		if (PV.find(TV) != PV.end())
			continue;
		PV.insert(TV);

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

					//Store constant is not considered
					if(isConstant(vop))
						continue;

					//There must be a path from the store to the load
                    if(pop == LPO && checkBlockPairConnectivity(STI->getParent(), LI->getParent()))
                        EV.push_back(vop);
                }
            }
			continue;
		}

		UnaryInstruction *UI = dyn_cast<UnaryInstruction>(TV);
		if(UI){
			EV.push_back(UI->getOperand(0));
			continue;
		}

		CallInst *CAI = dyn_cast<CallInst>(TV);
		if(CAI){
			//OP<<"CAI: "<<*CAI<<"\n";
			Function *CF = CAI->getCalledFunction();
			if (!CF) {
				continue;
			}

			size_t funchash = funcHash(CF,true);
			
			if(FuncTypesMap.count(funchash)){
				CTSet = FuncTypesMap[funchash];
				return;
			}
			
			continue;
		}

		GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(TV);
        if(GEP){

			//The struct ptr
			Value *PO = GEP->getPointerOperand();

			Type *PTy = PO->getType();
			//OP<<"PTy: "<<*PTy<<"\n";
			Type *Ty = PTy->getPointerElementType();
			//OP<<"Ty: "<<*Ty<<"\n";
			Type *sTy = GEP->getSourceElementType();
			//OP<<"sTy: "<<*sTy<<"\n";


			//Expect the PointerOperand is a struct
			if (isCompositeType(Ty)	&& GEP->hasAllConstantIndices()) {
				//BTy = Ty;
				User::op_iterator ie = GEP->idx_end();
				ConstantInt *ConstI = dyn_cast<ConstantInt>((--ie)->get());
				int Idx = ConstI->getSExtValue();
				CTSet.insert(std::make_pair(Ty, Idx));
				return;
			}
			continue;
		}

	}
}