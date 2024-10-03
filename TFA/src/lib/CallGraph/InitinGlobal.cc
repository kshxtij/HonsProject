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

using namespace llvm;


void getLayeredDebugTypeName(User *Ini, User *Layer, vector<unsigned> &vec){
	
	list<User *>LU;
	LU.push_back(Ini);

	set<User *> PB; //Global value set to avoid loop
	PB.clear();

	while (!LU.empty()) {
		User *U = LU.front();
		LU.pop_front();

		if (PB.find(U) != PB.end()){
			continue;
		}
		PB.insert(U);

		for (auto oi = U->op_begin(), oe = U->op_end(); oi != oe; ++oi) {
			Value *O = *oi;
			Type *OTy = O->getType();

		}
	}
}

//Maybe we should use recursive method to do this
//TODO: record GV initialized which function
bool CallGraphPass::typeConfineInInitializer(GlobalVariable* GV) {

	Constant *Ini = GV->getInitializer();
	if (!isa<ConstantAggregate>(Ini))
		return false;

	list<User *>LU;
	LU.push_back(Ini);

	if(GV->getName() == "llvm.used")
		return false;
	
	if(GV->getName() == "llvm.compiler.used") //llvm 15
		return false;

	//maybe should consider deadloop
	set<User *> PB; //Global value set to avoid loop
	PB.clear();

	//should consider global struct array
	while (!LU.empty()) {
		User *U = LU.front();
		LU.pop_front();

		if (PB.find(U) != PB.end()){
			continue;
		}
		PB.insert(U);

		//OP<<"\nCurrent U: "<<*U<<"\n\n";
		//OP<<"UTYpe: "<<*U->getType()<<"\n";
		for (auto oi = U->op_begin(), oe = U->op_end(); oi != oe; ++oi) {
			Value *O = *oi;
			Type *OTy = O->getType();
			//OP<<"--O: "<<*O<<"\n";
			// Case 1: function address is assigned to a type
			// FIXME: it seems this cannot get declared func
			if (Function *F = dyn_cast<Function>(O)) {

				Type *ITy = U->getType();
				// TODO: use offset?
				unsigned ONo = oi->getOperandNo();
				//OP<<"F: "<<F->getName()<<"\n";
				//OP<<"Type: "<<*ITy<<" offset: "<<ONo<<"\n\n";

				FuncSet FSet;
				FSet.clear();

				if(F->isDeclaration()){
					getGlobalFuncs(F,FSet);
				}
				else{
					FSet.insert(F);
				}

				for(auto it = FSet.begin(); it != FSet.end(); it++){
				
					F = *it;

					typeFuncsMap[typeIdxHash(ITy, ONo)].insert(F);
					
					Ctx->sigFuncsMap[funcHash(F, false)].insert(F); //only single type info
					
					if(Ctx->Global_Arg_Cast_Func_Map.count(F)){
						set<size_t> hashset = Ctx->Global_Arg_Cast_Func_Map[F];
						for(auto i = hashset.begin(); i!= hashset.end(); i++){
							Ctx->sigFuncsMap[*i].insert(F);
						}
					}

					//Use the new type to store
					size_t typehash = typeHash(ITy);
					size_t typeidhash = typeIdxHash(ITy,ONo);
					hashTypeMap[typehash] = ITy;
					hashIDTypeMap[typeidhash] = make_pair(ITy,ONo);

					updateStructInfo(F, ITy, ONo, GV);
					
				}
			}
			
			// Case 2: a composite-type object (value) is assigned to a
			// field of another composite-type object
			// A type is confined by another type
			else if (isCompositeType(OTy)) {
				//OP<<"--O2: "<<*O<<"\n";
				//OP<<" Case2: "<<*O<<"\n";
				// confine composite types
				Type *ITy = U->getType();
				unsigned ONo = oi->getOperandNo();
				//OP<<"ONo: "<<ONo<<"\n";


				// recognize nested composite types
				User *OU = dyn_cast<User>(O);
				LU.push_back(OU);
			}
			// Case 3: a reference (i.e., pointer) of a composite-type
			// object is assigned to a field of another composite-type
			// object
			else if (PointerType *POTy = dyn_cast<PointerType>(OTy)) {
				//OP<<"--O3: "<<*O<<"\n";
				if (isa<ConstantPointerNull>(O))
					continue;


				Type *eleType = POTy->getPointerElementType();
				if(isCompositeType(eleType)){
					Type *ITy = U->getType();
					unsigned ONo = oi->getOperandNo();


					// recognize nested composite types
					User *OU = dyn_cast<User>(O);
					LU.push_back(OU);
				}
				

				if (BitCastOperator *CO = dyn_cast<BitCastOperator>(O)) {

					Type *ToTy = CO->getDestTy(), *FromTy = CO->getSrcTy();
					Value *Operand = CO->getOperand(0);
					//Do we need typeConfineInCast?

					if(ToTy->isPointerTy() && FromTy->isPointerTy()){
						Type *ToeleType = ToTy->getPointerElementType();
						Type *FromeleType = FromTy->getPointerElementType();
						if(ToeleType->isFunctionTy() && FromeleType->isFunctionTy()){
							funcTypeCastMap[typeHash(ToeleType)].insert(typeHash(FromeleType));
							hashTypeMap[typeHash(ToeleType)] = ToeleType;
							hashTypeMap[typeHash(FromeleType)] = FromeleType;
						}

						//Todo Sometimes a function pointer type is casted to i8*
						string to_ty_str = getTypeStr(ToTy);
						string from_ty_str = getTypeStr(FromTy);
						if(FromeleType->isFunctionTy() && to_ty_str == "i8*"){
							//funcTypeCastToVoidSet.insert(typeHash(FromeleType));
						}

					}
					
					if(Function *F = dyn_cast<Function>(Operand)){
						//OP<<"from a function\n";
						Type *ITy = U->getType();
						unsigned ONo = oi->getOperandNo();

						FuncSet FSet;
						FSet.clear();

						if(F->isDeclaration()){
							getGlobalFuncs(F,FSet);
						}
						else{
							FSet.insert(F);
						}

						for(auto it = FSet.begin(); it != FSet.end(); it++){
				
							F = *it;

							typeFuncsMap[typeIdxHash(ITy, ONo)].insert(F);

							Ctx->sigFuncsMap[funcHash(F, false)].insert(F);
							if(Ctx->Global_Arg_Cast_Func_Map.count(F)){
								set<size_t> hashset = Ctx->Global_Arg_Cast_Func_Map[F];
								for(auto i = hashset.begin(); i!= hashset.end(); i++){
									Ctx->sigFuncsMap[*i].insert(F);
								}
							}

							//Use the new type to store
							size_t typehash = typeHash(ITy);
							size_t typeidhash = typeIdxHash(ITy,ONo);
							hashTypeMap[typehash] = ITy;
							hashIDTypeMap[typeidhash] = make_pair(ITy,ONo);

							updateStructInfo(F, ITy, ONo, GV);
						}

					}

				}
			}
			else{
				//OP<<"--O4: "<<*O<<"\n";
			}
		}
	}

	return true;
}