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
#include <deque>
#include <queue>
#include "llvm/IR/CFG.h" 
#include "llvm/Transforms/Utils/BasicBlockUtils.h" 
#include "llvm/IR/IRBuilder.h"

#include "CallGraph.h"
#include "../Config.h"
#include "../Common.h"

//This function could speed up
void CallGraphPass::funcSetIntersection(FuncSet &FS1, FuncSet &FS2, 
		FuncSet &FS) {
	FS.clear();
	
	for (auto F : FS1) {
		//Do not use pointer, use name, or we will miss function delcare
		if (FS2.find(F) != FS2.end())
			FS.insert(F);
	}

	//Use string match, 
	map<string, Function *> FS1_name_set, FS2_name_set;
	FS1_name_set.clear();
	FS2_name_set.clear();

	for (auto F : FS1) {
		string f_name = F->getName().str();
		if(f_name.size()>0)
			FS1_name_set.insert(make_pair(f_name,F));
	}

	for (auto F : FS2) {
		string f_name = F->getName().str();
		if(f_name.size()>0)
			FS2_name_set.insert(make_pair(f_name,F));
	}

	for (auto FName : FS1_name_set) {
		//Do not use pointer, use name, or we will miss function delcare
		if (FS2_name_set.find(FName.first) != FS2_name_set.end())
			FS.insert(FName.second);
	}
}	

//This function could speed up
//Merge FS2 into FS1
void CallGraphPass::funcSetMerge(FuncSet &FS1, FuncSet &FS2){
	for(auto F : FS2)
		FS1.insert(F);
}

Type *CallGraphPass::getLayerTwoType(Type* baseTy, vector<int> ids){

	StructType *sty = dyn_cast<StructType>(baseTy);
	if(!sty)
		return NULL;
	
	for(auto it = ids.begin(); it!=ids.end(); it++){
		int idx = *it;
		//OP<<"idx: "<<idx<<"\n";
		Type* subTy = sty->getElementType(idx);
		//OP<<"subTy: "<<*subTy<<"\n";
		StructType *substy = dyn_cast<StructType>(subTy);
		if(!substy)
			return NULL;
		
		//OP<<"subtype: "<<*substy<<"\n";
		
		sty = substy;
	}

	return sty;
}

unsigned CallGraphPass::getTypeEleNum(Type* Ty){
	
	unsigned num = 0;
	queue<Type*> Ty_queue;
	Ty_queue.push(Ty);

	while (!Ty_queue.empty()){
		Type* type = Ty_queue.front();
		Ty_queue.pop();

		if(type->isVoidTy() || type->isDoubleTy() || type->isFloatTy()
		|| type->isFunctionTy()){
			num += 1;
			continue;
		}

		if(type->isPointerTy()){
			static Type* preptrty;			
			PointerType* pyp = dyn_cast<PointerType>(type);
			
			preptrty = type;
			num += 1;
			continue;
		}
		
		if(type->isIntegerTy()){
			//OP<<"integer: "<<*type<<"\n";
			IntegerType* inty = dyn_cast<IntegerType>(type);
			unsigned bitwidth = inty->getBitWidth();
			//OP<<"bitwidth: "<<bitwidth<<"\n";
			num += (bitwidth/8);
			if(bitwidth/8 < 1){
				OP<<"WARNING: integer type with too small length!\n";
			}
			continue;
		}

		if(type->isArrayTy()){
			ArrayType* arrty = dyn_cast<ArrayType>(type);
			unsigned subnum = arrty->getNumElements();
			Type* subtype = arrty->getElementType();
			//TODO: what if subnum == 0?
			if(subnum == 0){
				//OP<<"WARNING: 0 array size!\n";
			}
			for(auto it = 0; it < subnum; it++){
				Ty_queue.push(subtype);
			}
			
			continue;
		}

		if(type->isStructTy()){
			unsigned subnum = type->getNumContainedTypes();
			for(auto it = 0; it < subnum; it++){
				Type* subtype = type->getContainedType(it);
				Ty_queue.push(subtype);
			}
			continue;
		}

		//TODO: what if opaque?
		//We may need to record all type definition to fix this
		//opaque is uaually related to pointer types
		if(type->isVectorTy()){
			//OP<<"is vector: "<<*type<<"\n";
			//OP<<"Ty: "<<*Ty<<"\n";
			//VectorType* vty = dyn_cast<VectorType>(type);
			//auto elecount = vty->getElementCount();
			auto psize = type->getPrimitiveSizeInBits();
			//OP<<"PrimitiveSizeInBits: "<<psize<<"\n";
			auto scalarsize = type->getScalarSizeInBits();
			//OP<<"ScalarSizeInBits: "<<scalarsize<<"\n";
			int subnum = psize/scalarsize;
			Type* subtype = type->getScalarType();
			//OP<<"subtype: " <<*subtype<<"\n";
			for(auto it = 0; it < subnum; it++){	
				Ty_queue.push(subtype);
			}

			continue;
		}
		
		OP<<"WARNING: unsupported type:" <<*type<<"\n";

	}
	return num;
}


void CallGraphPass::updateStructInfo(Function *F, Type* Ty, int idx, Value* context){

	//Union prelayer is regarded as escape
	if(Ctx->Globa_Union_Set.count(typeHash(Ty))){
		//OP<<"union: "<<F->getName()<<"\n";
		Ctx->num_local_info_name++;
		Ctx->Global_EmptyTy_Funcs[funcHash(F, false)].insert(F);
		return;
	}

	//Pre layer is struct without name
	if(Ty->isStructTy() && Ty->getStructName().size() == 0){
		string Funcname = F->getName().str();

		if(Ctx->Global_Literal_Struct_Map.count(typeHash(Ty))){
			//OP<<"empty struct name but have debug info\n";
			Ctx->num_emptyNameWithDebuginfo++;
			string TyName = Ctx->Global_Literal_Struct_Map[typeHash(Ty)];
			if(checkStringContainSubString(TyName, "union.")){
				Ctx->num_local_info_name++;
				if(Funcname.size() != 0)
					Ctx->Global_EmptyTy_Funcs[funcHash(F, false)].insert(F);
				return;
			}

			if(checkStringContainSubString(TyName, ".anon")){
				Ctx->num_local_info_name++;
				if(Funcname.size() != 0)
					Ctx->Global_EmptyTy_Funcs[funcHash(F, false)].insert(F);
				return;
			}

			//OP<<"updateStructInfo typename: "<<TyName<<"\n";
			typeFuncsMap[typeNameIdxHash(TyName, idx)].insert(F);
			hashIDTypeMap[typeNameIdxHash(TyName,idx)] = make_pair(Ty,idx);
			if(context){
				Func_Init_Map[context][F].insert(typeNameIdxHash(TyName, idx));
			}
		}
		else{

			//TODO: trace the typename in debuginfo
			Ctx->num_emptyNameWithoutDebuginfo++;
			
			if(Funcname.size() != 0)
				Ctx->Global_EmptyTy_Funcs[funcHash(F, false)].insert(F);
		}
	}
	
	//Pre layer is struct with name
	else if(Ty->isStructTy()){
		Ctx->num_haveLayerStructName++;
		auto TyName = Ty->getStructName().str();
		if(checkStringContainSubString(TyName, "union.")){
			Ctx->Globa_Union_Set.insert(typeHash(Ty));
			Ctx->num_local_info_name++;
			string Funcname = F->getName().str();
			if(Funcname.size() != 0){
				Ctx->Global_EmptyTy_Funcs[funcHash(F, false)].insert(F);
			}
			return;
		}

		if(checkStringContainSubString(TyName, ".anon")){
			Ctx->num_local_info_name++;
			string Funcname = F->getName().str();
			if(Funcname.size() != 0){
				Ctx->Global_EmptyTy_Funcs[funcHash(F, false)].insert(F);
			}
			return;
		}

		string parsed_TyName = parseIdentifiedStructName(TyName);
		typeFuncsMap[typeNameIdxHash(parsed_TyName, idx)].insert(F);
		hashIDTypeMap[typeNameIdxHash(parsed_TyName,idx)] = make_pair(Ty,idx);
		if(context){
			Func_Init_Map[context][F].insert(typeNameIdxHash(parsed_TyName, idx));
		}
	}
	
	//Prelayer is array
	else if(Ty->isArrayTy()){
		//OP<<"array\n";
		Ctx->num_array_prelayer++;
		Ctx->num_local_info_name++;

		Ctx->Global_EmptyTy_Funcs[funcHash(F, false)].insert(F);
	}
	else{
		//OP<<"here\n";
		Ctx->num_local_info_name++;
		Ctx->Global_EmptyTy_Funcs[funcHash(F, false)].insert(F);
	}
}

string CallGraphPass::parseIdentifiedStructName(StringRef str_name){

    if(str_name.size() == 0)
        return "";

    if(str_name.contains("struct.")){
        string substr = str_name.str();
        substr = substr.substr(7, substr.size()-1); //remove "struct." in name
        return substr;
    }
    else if(str_name.contains("union.")){
        string substr = str_name.str();
        substr = substr.substr(6, substr.size()-1); //remove "union." in name
        return substr;
    }

    return "";
}

void CallGraphPass::resolveNonStructLayer(GlobalVariable* GV, Type* Ty, User* U){
	
	bool valid = false;
	if(Ty->isArrayTy())
		valid = true;
	else if (Ctx->Global_Literal_Struct_Map.count(typeHash(Ty))){
		if(Ctx->Global_Literal_Struct_Map[typeHash(Ty)] == "Array")
			valid = true;
	}
	else if (Ctx->Globa_Union_Set.count(typeHash(Ty))){
		valid = true;
	}

	if (valid == false)
		return;
	
	OP<<"here\n";
	OP<<"Ty: "<<*Ty<<"\n";
	OP<<"U: "<<*U<<"\n";
	Constant *Ini = GV->getInitializer();
	list<User *>LU;
	LU.push_back(Ini);

	//maybe should consider deadloop
	set<User *> PB; //Global value set to avoid loop
	PB.clear();

	//should consider global struct array
	while (!LU.empty()) {
		User *CU = LU.front();
		LU.pop_front();

		if (PB.find(CU) != PB.end()){
			continue;
		}
		PB.insert(CU);

		Type *UTy = CU->getType();
		OP<<"CU: "<<*CU<<"\n";

		//OP<<"\nCurrent U: 
		for (auto oi = CU->op_begin(), oe = CU->op_end(); oi != oe; ++oi) {
			Value *O = *oi;
			Type *OTy = O->getType();
			unsigned ONo = oi->getOperandNo();
			OP<<"O: "<<*O<<"\n";
			if(O == U){
				OP<<"find the prelayer\n";
				OP<<"UTy: "<<*UTy<<"\n";
				OP<<"ONo: "<<ONo<<"\n";
			}

			if (isCompositeType(OTy)) {
				User *OU = dyn_cast<User>(O);
				LU.push_back(OU);
			}
			else if (PointerType *POTy = dyn_cast<PointerType>(OTy)) {
				if (isa<ConstantPointerNull>(O))
					continue;
				
				Type *eleType = POTy->getPointerElementType();
				if(isCompositeType(eleType)){

					// recognize nested composite types
					User *OU = dyn_cast<User>(O);
					LU.push_back(OU);
				}
			}
		}

	}
}

size_t CallGraphPass::callInfoHash(CallInst* CI, Function *Caller, int index){
    
    hash<string> str_hash;
	string output;
    output = getInstFilename(CI);

	string sig;
	raw_string_ostream rso(sig);
	Type *FTy = Caller->getFunctionType();
	FTy->print(rso);
	output += rso.str();
	output += Caller->getName();

	string::iterator end_pos = remove(output.begin(), 
			output.end(), ' ');
	output.erase(end_pos, output.end());
	
    stringstream ss;
    unsigned linenum = getInstLineNo(CI);
    ss<<linenum;
	ss<<index;
	output += ss.str();

	//OP<<"output: "<<output<<"\n";

	return str_hash(output);

}

//Given a func declarition, find its global definition
void CallGraphPass::getGlobalFuncs(Function *F, FuncSet &FSet){


    StringRef FName = F->getName();

    if(Ctx->GlobalFuncs.count(FName.str())){
        set<size_t> hashSet = Ctx->GlobalFuncs[FName.str()];
        for(auto it = hashSet.begin(); it != hashSet.end(); it++){
            Function *f = Ctx->Global_Unique_Func_Map[*it];
			FSet.insert(f);
        }
    }

	if(FSet.empty()){
		size_t funchash = funcInfoHash(F);
		if(Ctx->Global_Unique_Func_Map.count(funchash)){
			Function *f = Ctx->Global_Unique_Func_Map[funchash];
			FSet.insert(f);
		}
	}
}

bool CallGraphPass::checkValidStructName(Type *Ty){

	if(Ty->getStructName().size() != 0){

		auto TyName = Ty->getStructName();
		if(TyName.contains(".union")){
			return false;
		}

		if(TyName.contains(".anon")){
			return false;
		}

		return true;
	}
	else{
		if(Ctx->Global_Literal_Struct_Map.count(typeHash(Ty))){

			string TyName = Ctx->Global_Literal_Struct_Map[typeHash(Ty)];
			if(checkStringContainSubString(TyName, ".union")){
				return false;
			}

			if(checkStringContainSubString(TyName, ".anon")){
				return false;
			}

			return true;
		}
		else{
			return false;
		}
	}
}