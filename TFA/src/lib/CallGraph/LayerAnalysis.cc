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

Value *CallGraphPass::nextLayerBaseType(Value *V, Type * &BTy, int &Idx) {

	set<Value *>Visited;

	// Two ways to get the next layer type: GetElementPtrInst and
	// LoadInst
	// Case 1: GetElementPtrInst / GEPOperator
	if(GEPOperator *GEP = dyn_cast<GEPOperator>(V)){
		Type *PTy = GEP->getPointerOperand()->getType();
		//OP<<"PTy: "<<*PTy<<"\n";
		Type *Ty = PTy->getPointerElementType();
		//OP<<"Ty: "<<*Ty<<"\n";
		Type *sTy = GEP->getSourceElementType();
		//OP<<"sTy: "<<*sTy<<"\n";

		//Expect the PointerOperand is a struct
		if (Ty->isStructTy() && GEP->hasAllConstantIndices()) {
			BTy = Ty;
			User::op_iterator ie = GEP->idx_end();
			ConstantInt *ConstI = dyn_cast<ConstantInt>((--ie)->get());
			Idx = ConstI->getSExtValue();
			if(Idx < 0)
				return NULL;
			
			unsigned indice_num = GEP->getNumIndices();

			//Filter GEP that has invalid indice
			ConstantInt *ConstI_first = dyn_cast<ConstantInt>(GEP->idx_begin()->get());
			int Idx_first = ConstI_first->getSExtValue();
			if(Idx_first != 0 && indice_num>=2){
				if(Ty->isStructTy()){
					return NULL;
				}
			}
			
			if(indice_num < 2)
				return NULL;

			if(indice_num > 2){

				vector<int> id_vec;
				id_vec.clear();
				for(auto it = GEP->idx_begin() + 1; it != GEP->idx_end(); it++){

					ConstantInt *ConstI = dyn_cast<ConstantInt>(it->get());
					int Id = ConstI->getSExtValue();
					if(Id < 0){
						return NULL;
					}
					id_vec.push_back(Id);
					//OP<<"--idx: "<<Id<<"\n";
				}

				Type* result_ty = getLayerTwoType(BTy,id_vec);
				if(result_ty){
					//OP<<"result ty: "<<*result_ty<<"\n";
					BTy = result_ty;
				}
			}

			return GEP->getPointerOperand();
		}
		else
			return NULL;
	}

	// Case 2: LoadInst
	// Maybe we should also consider the store inst here
	else if (LoadInst *LI = dyn_cast<LoadInst>(V)) {
		//OP<<"in Load\n";
		//The load target could be a bitcast, which will influence our analysis
		return nextLayerBaseType(LI->getOperand(0), BTy, Idx);
	}

#if 1
	// Other instructions such as CastInst
	// FIXME: may introduce false positives
	//UnaryInstruction includes castinst, load, etc, resolve this in the last step
	else if (UnaryInstruction *UI = dyn_cast<UnaryInstruction>(V)) {
		//OP<<"in unaryInst\n";
		return nextLayerBaseType(UI->getOperand(0), BTy, Idx);
	}
#endif
	
	else {
		//OP<<"unknown inst: "<<*V<<"\n";
		return NULL;
	}
}


//Note: 
//In Precise_Mode,
//when nextLayerBaseType_new returns true, V must have all 2-layer info;
//when nextLayerBaseType_new returns false, TyList is not necessary empty.
//In Recall_Mode,
//All type info will be analyzed.
bool CallGraphPass::nextLayerBaseType_new(Value *V, list<CompositeType> &TyList, 
    set<Value*> &VisitedSet, LayerFlag Mode) {

	//if(!isa<Function>(V))
		//OP<<"V: "<<*V<<"\n";

    //For only type analysis, we will lose V's further info if V is an argument, 
    //a return value of a call, or a global value
    if (!V || isa<llvm::Argument>(V) || isa<CallInst>(V) || isa<GlobalValue>(V)) {
        return false;
    }

    Type* BTy;
    int Idx;

    //Loop handler
    if(VisitedSet.count(V)){
        return true;
    }

    VisitedSet.insert(V);

	//OP<<"V: "<<*V<<"\n";

	// Two ways to get the next layer type: GetElementPtrInst and
	// LoadInst
	// Case 1: GetElementPtrInst / GEPOperator
	if(GEPOperator *GEP = dyn_cast<GEPOperator>(V)){
		return getGEPLayerTypes(GEP, TyList);
	}

    else if (BitCastOperator *BCI = dyn_cast<BitCastOperator>(V)){
        //OP<<"BCI: "<<*BCI<<"\n";
        Type *ToTy = BCI->getDestTy(), *FromTy = BCI->getSrcTy();
        if(FromTy->isPointerTy()){
            FromTy = FromTy->getPointerElementType();
        }
        if(FromTy->isStructTy()){
            if(FromTy->getStructName().contains(".union")){
                return false;
            }
            if(FromTy->getStructName().contains(".anon")){
                return false;
            }
        }
		return nextLayerBaseType_new(BCI->getOperand(0), TyList, VisitedSet, Mode);
	}

	// Case 2: LoadInst
	else if (LoadInst *LI = dyn_cast<LoadInst>(V)) {
		//OP<<"in Load\n";
		Value *LPO = LI->getPointerOperand();
        bool LI_result = nextLayerBaseType_new(LPO, TyList, VisitedSet, Mode);
        
        //Only check in Precise_Mode
        if(Mode == Precise_Mode && LI_result == false){
            return false;
        }

        //This update does not influence the 0-target icall num,
        //but the total icall target num increases 35k
        int fail_tag = 0;
        for(User *U : LPO->users()){
            //OP<<"user: "<<*U<<"\n";
            StoreInst *STI = dyn_cast<StoreInst>(U);
            if(STI){
                
                Value* vop = STI->getValueOperand(); // store vop to pop
                Value* pop = STI->getPointerOperand();
                
                if(LPO != pop)
                    continue;

                //Store constant data is not considered
                if(ConstantData *Ct = dyn_cast<ConstantData>(vop))
                    continue;

                LI_result = nextLayerBaseType_new(vop, TyList, VisitedSet, Mode);
                if(LI_result == false){
                    fail_tag = 1;
                    if(Mode == Precise_Mode)
                        return false;
                }
            }
        }

        if(fail_tag == 0)
            return true;
        else
            return false;
	}

	//Case 3: PHI
    //For PHI, we require all incoming values have 2-layer info.
    //Otherwise, we regard the analysis result as FAIL.
	else if(PHINode *PN = dyn_cast<PHINode>(V)){
        
        bool PH_result;
        int fail_tag = 0;
		for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) {

			Value *IV = PN->getIncomingValue(i);
            PH_result = nextLayerBaseType_new(IV, TyList, VisitedSet, Mode);
            if(PH_result == false){
                fail_tag = 1;
                if(Mode == Precise_Mode)
                    return false;
            }
		}

        if(fail_tag == 0)
            return true;
        else
            return false;
	}
	

    else if (SelectInst *SLI = dyn_cast<SelectInst>(V)) {
		
        bool SLI_result = true;
        int fail_tag = 0;
		SLI_result = nextLayerBaseType_new(SLI->getTrueValue(), TyList, VisitedSet, Mode);
        if(SLI_result == false){
            fail_tag = 1;
            if(Mode == Precise_Mode)
                return false;
        }
        SLI_result = nextLayerBaseType_new(SLI->getFalseValue(), TyList, VisitedSet, Mode);
        if(SLI_result == false)
            return false;

        if(fail_tag == 0)
            return true;
        else
            return false;
	}

	// Other instructions such as CastInst
	//UnaryInstruction includes castinst, load, etc, resolve this in the last step
	else if (UnaryInstruction *UI = dyn_cast<UnaryInstruction>(V)) {
		//OP<<"in unaryInst\n";
		return nextLayerBaseType_new(UI->getOperand(0), TyList, VisitedSet, Mode);
	}
	
	else {
		return false;
	}
}

Value *CallGraphPass::recoverBaseType(Value *V) {
	if (Instruction *I = dyn_cast<Instruction>(V)) {
		map<Value *, Value *> &AliasMap 
			= Ctx->AliasStructPtrMap[I->getFunction()];
		if (AliasMap.find(V) != AliasMap.end()) {
			return AliasMap[V];
		}
	}
	return NULL;
}

//Return true if we successfully find the layered type
bool CallGraphPass::getGEPLayerTypes(GEPOperator *GEP, list<CompositeType> &TyList) {


    Type *PTy = GEP->getPointerOperand()->getType();
	if(!PTy->isPointerTy())
		return false;
    Type *Ty = PTy->getPointerElementType();
    Type *sTy = GEP->getSourceElementType();

    Type* BTy;
    int Idx;
    //Expect the PointerOperand is an identified struct
    if (Ty->isStructTy() && GEP->hasAllConstantIndices()) {
        BTy = Ty;
        User::op_iterator ie = GEP->idx_end();
        ConstantInt *ConstI = dyn_cast<ConstantInt>((--ie)->get());
        Idx = ConstI->getSExtValue(); //Idx is the last indice
        if(Idx < 0)
            return false;
        
        if(!checkValidStructName(Ty))
			return false;

        unsigned indice_num = GEP->getNumIndices();

        //Filter GEP that has invalid indice
        ConstantInt *ConstI_first = dyn_cast<ConstantInt>(GEP->idx_begin()->get());
        int Idx_first = ConstI_first->getSExtValue();
        if(Idx_first != 0 && indice_num>=2){
            if(Ty->isStructTy()){
                return false;
            }
        }
        
        if(indice_num < 2)
            return false;

        if(indice_num > 2){
            vector<int> id_vec;
            id_vec.clear();
            //Ignore the first and the last indice
            for(auto it = GEP->idx_begin() + 1; it != GEP->idx_end() - 1; it++){

                ConstantInt *ConstI = dyn_cast<ConstantInt>(it->get());
                int Id = ConstI->getSExtValue();
                if(Id < 0){
                    return false;
                }
                id_vec.push_back(Id);
            }

            Type* result_ty = getLayerTwoType(BTy, id_vec);
            if(result_ty){
				if(!checkValidStructName(result_ty))
					return false;
                BTy = result_ty;
            }else{
                return false;
            }
        }

		

        TyList.push_back(make_pair(BTy, Idx));

        return true;
    }
	
	// Usually Ty is i8
	else if (Ty->isIntegerTy() && GEP->hasAllConstantIndices()){
		//OP<<"here\n";
		return false;

		//a case:  %71 = getelementptr inbounds i8, i8* %7, i64 2000, !dbg !5286
		unsigned indice_num = GEP->getNumIndices();
		if(indice_num != 1)
			return false;

		//First, get the real base type
		set<Type*> baseRySet;
		Value* PO = GEP->getPointerOperand();
		Type* baseTy = NULL;

		if(TypeHandlerMap.count(PO)){
			baseTy = TypeHandlerMap[PO];
			if(baseTy){
				goto analysis;
			}
			else
				return false;
		}

		//Usually call inst
		if(Instruction* I = dyn_cast<Instruction>(PO)){
			BasicBlock* BB = I->getParent();
			for (auto User : PO->users()) {

				if (BitCastInst *BCI = dyn_cast<BitCastInst>(User)) {
					if(BCI->getParent() != BB)
						continue;

					Type * BCTy = BCI->getType()->getPointerElementType();
					if (BCTy->isStructTy()) {
						baseTy = BCTy;
						break;
					}
				}
			}
		}

		if(baseTy){
			goto analysis;
		}
		
		baseTy = getRealType(PO);
		if(baseTy){
			TypeHandlerMap[PO] = baseTy;
			//OP<<"success\n";
		}
		else {
			TypeHandlerMap[PO] = NULL;
			return false;
		}


analysis:
		ConstantInt *ConstI = dyn_cast<ConstantInt>(GEP->idx_begin()->get());
        int offset = ConstI->getSExtValue();
		if(offset < 0)
			return false;

		auto typeallocsize = DL->getTypeAllocSize(baseTy);
		//OP<<"--size: "<<typeallocsize<<"\n";

		//TODO: fix this case
		if(typeallocsize < offset)
			return false;

		Type* resultTy;
		int Idx;
		if (getGEPIndex(baseTy, offset, resultTy, Idx)){
			TyList.push_back(make_pair(resultTy, Idx));
			return true;
		}


		return false;
	}
    else
        return false;
	
}


//under testing
bool CallGraphPass::getGEPIndex(Type* baseTy, int offset, Type * &resultTy, int &Idx){
	
	if(!DL)
		return false;

	Type* nextTy = baseTy;
	resultTy = baseTy;
	int currentOffset = 0;
	int idx = 0;

	while(offset > 0){
		
		if (auto *STy = dyn_cast<StructType>(resultTy)) {
			const StructLayout *SL = DL->getStructLayout(STy);
			Idx = SL->getElementContainingOffset(offset);
			unsigned eleoffset = SL->getElementOffset(Idx);
			
			offset -= eleoffset;
			if(offset == 0)
				break;

			resultTy = STy->getElementType(Idx);
			
			continue;
		}

		return false;

	}

	if(offset != 0)
		return false;

	return true;
}

// This function is to get the base type in the current layer.
// To get the type of next layer (with GEP and Load), use
// nextLayerBaseType() instead.
// This function will only return NULL or a composite type.
Type *CallGraphPass::getBaseType(Value *V, set<Value *> &Visited) {

	if (!V)
		return NULL;

	if (Visited.count(V))
		return NULL;

	Visited.insert(V);

	Type *Ty = V->getType();

	if (isCompositeType(Ty)) {
		return Ty;
	}
	// The value itself is a pointer to a composite type
	else if (Ty->isPointerTy()) {

		Type *ETy = Ty->getPointerElementType();
		if (isCompositeType(ETy)) {
			return ETy;
		}
	}

	if (BitCastOperator *BCO = dyn_cast<BitCastOperator>(V)) {
		return getBaseType(BCO->getOperand(0), Visited);
	}
	else if (SelectInst *SelI = dyn_cast<SelectInst>(V)) {
		// Assuming both operands have same type, so pick the first operand
		return getBaseType(SelI->getTrueValue(), Visited);
	}
	else if (PHINode *PN = dyn_cast<PHINode>(V)) {
		// TODO: tracking incoming values
		return getPhiBaseType(PN, Visited);
	}
	else if (LoadInst *LI = dyn_cast<LoadInst>(V)) {
		return getBaseType(LI->getPointerOperand(), Visited);
	}

	else {
	}

	return NULL;
}

Type *CallGraphPass::getPhiBaseType(PHINode *PN, set<Value *> &Visited) {

	for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) {
		Value *IV = PN->getIncomingValue(i);

		Type *BTy = getBaseType(IV, Visited);
		if (BTy)
			return BTy;
	}

	return NULL;
}

Type *CallGraphPass::getFuncPtrType(Value *V){
    Type *Ty = V->getType();
	if (PointerType *PTy = dyn_cast<PointerType>(Ty)) {
		Type *ETy = PTy->getPointerElementType();
		if (ETy->isFunctionTy())
			return ETy;
	}

	return NULL;
}


Function *CallGraphPass::getBaseFunction(Value *V) {

	if (Function *F = dyn_cast<Function>(V))
		if (!F->isIntrinsic())
			return F;

	Value *CV = V;
	while (BitCastOperator *BCO = dyn_cast<BitCastOperator>(CV)) {
		Value *O = BCO->getOperand(0);
		if (Function *F = dyn_cast<Function>(O))
			if (!F->isIntrinsic())
				return F;
		CV = O;
	}
	return NULL;
}

void CallGraphPass::propagateType(Value *ToV, Type *FromTy, int FromIdx, StoreInst* SI) {


    set<Value*> VisitedSet;
	list<CompositeType> TyList;
	bool next_result = nextLayerBaseType_new(ToV, TyList, VisitedSet, Recall_Mode);
    
    for (CompositeType CT : TyList) {
        Type* ToSTy = CT.first;
		int ToIdx = CT.second;

        if(ToSTy == FromTy && ToIdx == FromIdx)
            continue;
		
		string To_Type_name = "";
		string From_Type_name = "";
		
		if(ToSTy->isStructTy()){

			if(ToSTy->getStructName().size() == 0){
				//OP<<"\nliteral struct: "<<*Hty<<"\n";
				To_Type_name = Ctx->Global_Literal_Struct_Map[typeHash(ToSTy)];
			}
			else{
				StringRef Ty_name = ToSTy->getStructName();
				To_Type_name = parseIdentifiedStructName(Ty_name);
			}
		}

		if(FromTy->isStructTy()){

			if(FromTy->getStructName().size() == 0){
				//OP<<"\nliteral struct: "<<*Hty<<"\n";
				From_Type_name = Ctx->Global_Literal_Struct_Map[typeHash(FromTy)];
			}
			else{
				StringRef Ty_name = FromTy->getStructName();
				From_Type_name = parseIdentifiedStructName(Ty_name);
			}
		}

		typeConfineMap[typeNameIdxHash(To_Type_name, ToIdx)].insert(typeNameIdxHash(From_Type_name, FromIdx));
		hashIDTypeMap[typeNameIdxHash(To_Type_name, ToIdx)] = make_pair(ToSTy, ToIdx);
		hashIDTypeMap[typeNameIdxHash(From_Type_name, FromIdx)] = make_pair(FromTy, FromIdx);
		
    }
}

bool CallGraphPass::trackFuncPointer(Value* VO, Value* PO, StoreInst* SI){
	
	Type* Ty = VO->getType();
	if(!Ty->isPointerTy())
		return false;

	Type *ETy = Ty->getPointerElementType();
	if(!ETy->isFunctionTy())
		return false;
	
	//Check the source of VO
    std::list<Value *> EV; //BFS record list
    std::set<Value *> PV; //Global value set to avoid loop
    EV.clear();
    PV.clear();
    EV.push_back(VO);

    while (!EV.empty()) {
        Value *TV = EV.front(); //Current checking value
		EV.pop_front();
            
        if (PV.find(TV) != PV.end()) //Avoid loop
			continue;
        PV.insert(TV);

		if(ConstantData *Ct = dyn_cast<ConstantData>(TV))
            continue;
		
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
		
		Function *F = getBaseFunction(TV->stripPointerCasts());
		if(F){
			if (F->isIntrinsic())
				continue;

			FuncSet FSet;
			FSet.clear();

			if(F->isDeclaration()){
				getGlobalFuncs(F,FSet);
			}
			else{
				FSet.insert(F);
			}

			set<Value*> VisitedSet;
			list<CompositeType> TyList;
			if (nextLayerBaseType_new(PO, TyList, VisitedSet, Precise_Mode)) {

				for(CompositeType CT : TyList){

					Type* STy = CT.first;
					int Idx = CT.second;

					size_t typehash = typeHash(STy);
					size_t typeidhash = typeIdxHash(STy,Idx);
					hashTypeMap[typehash] = STy;
					hashIDTypeMap[typeidhash] = make_pair(STy,Idx);

					for(auto it = FSet.begin(); it != FSet.end(); it++){					
						F = *it;

						typeFuncsMap[typeIdxHash(STy, Idx)].insert(F);
						Ctx->sigFuncsMap[funcHash(F, false)].insert(F);

						if(Ctx->Global_Arg_Cast_Func_Map.count(F)){
							set<size_t> hashset = Ctx->Global_Arg_Cast_Func_Map[F];
							for(auto i = hashset.begin(); i!= hashset.end(); i++){
								Ctx->sigFuncsMap[*i].insert(F);
							}
						}
						
						//If STy is an invalid struct (e.g., union), F will be marked escape
						updateStructInfo(F, STy, Idx, SI);
					}
				}
			}
			else {
				//A function is (possiblely) stored to an unknown one-layer value, 
				//we cannot track this case.
				//So we mark this func as escape (record in Global_EmptyTy_Funcs).
				for(auto it = FSet.begin(); it != FSet.end(); it++){	
					F = *it;
					Ctx->sigFuncsMap[funcHash(F, false)].insert(F);
					Ctx->Global_EmptyTy_Funcs[funcHash(F, false)].insert(F);
				}
			}

			continue;
		}
		return false;
	
	}


	return true;
}
