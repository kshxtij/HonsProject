#include <llvm/IR/Instructions.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/LegacyPassManager.h>

#include "AliasAnalysis.h"

using namespace llvm;

//#define TEST_ONE_FUNC "wake_up_klogd_work_func"
//#define PRINT_ALIAS_RESULT
#define ENAMBE_OMP

void FuncAliasAnalysis(GlobalContext *Ctx){

    OP<<"\n Start Func Alias Analysis\n";

    //Record F could influence which icall
    map<Function*, CallInstSet> FuncInfluenceMap;
    FuncInfluenceMap.clear();
    FuncSet SucceedFuncSet;

	vector<Function*> TargetVec;
	TargetVec.clear();
	for(auto it = Ctx->Global_AddressTaken_Func_Set.begin(); 
        it != Ctx->Global_AddressTaken_Func_Set.end(); it++){

        TargetVec.push_back(*it);
    }
    size_t Func_num = TargetVec.size();

    //Record funcs that failed in FuncAliasAnalysis
    //set<size_t> Global_failed_Func_Set;
    Ctx->Global_failed_Func_Set.clear();

    omp_lock_t lock;
	omp_init_lock(&lock);

    //Analysis every address-taken function
#ifdef ENAMBE_OMP
	#pragma omp parallel for schedule(dynamic,1)
#endif
    for(auto i = 0; i < Func_num; i++){
        
        Function* F = TargetVec[i];
        if(!F)
            continue;
        
#ifdef TEST_ONE_FUNC
        if(F->getName()!=TEST_ONE_FUNC){
            continue;
        }
#endif

        //F has failed in other analysis
        if(Ctx->Global_failed_Func_Set.count(F->getGUID())){
#ifdef ENAMBE_OMP
            omp_set_lock(&lock);
            Ctx->Global_Func_Alias_Result_Map[F] = ignore_analysis;
            omp_unset_lock(&lock);
#else
            Ctx->Global_Func_Alias_Result_Map[F] = ignore_analysis;
#endif
            continue;
        }
        
        //TODO: analyze them in use-chain
        if(Ctx->Global_symbol_get_funcSet.count(F->getName().str())){
#ifdef ENAMBE_OMP
            omp_set_lock(&lock);
            Ctx->Global_Func_Alias_Result_Map[F] = ignore_analysis;
            omp_unset_lock(&lock);
#else
            Ctx->Global_Func_Alias_Result_Map[F] = ignore_analysis;
#endif
            continue;
        }

        AliasContext* aliasCtx = new AliasContext();
        CallInstSet aliased_callset;
        aliased_callset.clear();

        HandleFunc(F, aliasCtx, Ctx, aliased_callset, &lock);

#ifdef ENAMBE_OMP
        omp_set_lock(&lock);
        if(aliasCtx->Global_symbol_get_funcSet.size() != 0){
            for(auto func : aliasCtx->Global_symbol_get_funcSet)
                Ctx->Global_symbol_get_funcSet.insert(func);
        }
        omp_unset_lock(&lock);
#else
        if(aliasCtx->Global_symbol_get_funcSet.size() != 0){
            for(auto func : aliasCtx->Global_symbol_get_funcSet)
                Ctx->Global_symbol_get_funcSet.insert(func);
        }
#endif

        FuncSet DefinitionFuncSet;
        DefinitionFuncSet.clear();
        getGlobalFuncs(F, DefinitionFuncSet, Ctx);

        if(aliasCtx->Is_Analyze_Success == false){
            //OP<<"failed\n";

#ifdef ENAMBE_OMP
			omp_set_lock(&lock);
            OP<< "     Top func: "<<F->getName()<< " Failed" <<"\n";
			Ctx->failure_reasons[aliasCtx->failreason]++;
            Ctx->Global_failed_Func_Set.insert(F->getGUID());
            Ctx->Global_Func_Alias_Result_Map[F] = aliasCtx->failreason;
            /*for(Function* f : DefinitionFuncSet){
                FailedFuncSet.insert(f);
                if(FuncInfluenceMap.count(f))
                    FuncInfluenceMap.erase(f); //This will cause datarace!
            }*/

			omp_unset_lock(&lock);
#else
			OP<< "     Top func: "<<F->getName()<< " Failed" <<"\n";
            Ctx->failure_reasons[aliasCtx->failreason]++;
            Ctx->Global_failed_Func_Set.insert(F->getGUID());
            Ctx->Global_Func_Alias_Result_Map[F] = aliasCtx->failreason;
            /*for(Function* f : DefinitionFuncSet){
                FailedFuncSet.insert(f);
                if(FuncInfluenceMap.count(f))
                    FuncInfluenceMap.erase(f);
            }*/
#endif

            delete aliasCtx;
			continue;
		}

#ifdef ENAMBE_OMP
		omp_set_lock(&lock);
#endif

        OP<<"\nAnalyzed func: "<<F->getName()<<"\n";
        OP<<"DefinitionFuncSet size: "<<DefinitionFuncSet.size()<<"\n";
        OP<<"aliased_callset size: "<<aliased_callset.size()<<"\n";

        SucceedFuncSet.insert(F);
        Ctx->Global_Func_Alias_Result_Map[F] = success;

        //Make sure the key of FuncInfluenceMap is function definition
        for(Function* f : DefinitionFuncSet){
            for(CallInst* CAI : aliased_callset){
                FuncInfluenceMap[f].insert(CAI);
            }
        }
        delete aliasCtx;

#ifdef ENAMBE_OMP
		omp_unset_lock(&lock);
#endif
        
    }

    Ctx->func_support_dataflow_Number = FuncInfluenceMap.size();
    
    //Update Global Info
    OP<<"\nUpdate global ICallees info\n";
    vector<pair<CallInst*, FuncSet>> UpdateVec;
	UpdateVec.clear();
	for(auto i = Ctx->ICallees.begin(); i!= Ctx->ICallees.end(); i++){
		UpdateVec.push_back(make_pair(i->first, i->second));
	}
	size_t ICall_num = UpdateVec.size();
    static size_t update_num = 0;

#ifdef ENAMBE_OMP
	#pragma omp parallel for schedule(dynamic,1)
#endif
	for(auto i = 0; i < ICall_num; i++){
        //OP<<"begin\n";
        CallInst* ICall = UpdateVec[i].first;
        FuncSet ICall_Targets = UpdateVec[i].second;

#ifdef ENAMBE_OMP
        omp_set_lock(&lock);
        OP<< "\n"<< update_num++<< " Update icall: "<<*ICall<<"\n";
        omp_unset_lock(&lock);
#else
        OP<< "\n"<< update_num++<< " Update icall: "<<*ICall<<"\n";
#endif

        for(Function* f : SucceedFuncSet){
            if(Ctx->Global_failed_Func_Set.count(f->getGUID()))
                continue;

            CallInstSet callset;
            //callset.clear();
            if(FuncInfluenceMap.count(f)){
                callset = FuncInfluenceMap[f];
            }

            if(ICall_Targets.count(f)){

                if(callset.count(ICall) == 0){

#ifdef ENAMBE_OMP
                    omp_set_lock(&lock);
                    Ctx->ICallees[ICall].erase(f);
                    omp_unset_lock(&lock);
#else
                    Ctx->ICallees[ICall].erase(f);
#endif
                }
            }
        }

    }

    update_num = 0;

    //Update analysis results
	Ctx->icallTargets = 0;
	for(auto i = Ctx->ICallees.begin(); i!= Ctx->ICallees.end(); i++){
		FuncSet fset = i->second;
		Ctx->icallTargets+=fset.size();
	}

    omp_destroy_lock(&lock);
}

void HandleFunc(Function* F, AliasContext *aliasCtx, 
    GlobalContext *Ctx, CallInstSet &callset, omp_lock_t *lock){

    static size_t num = 0;

#ifdef ENAMBE_OMP
	omp_set_lock(lock);
	OP<< "\n"<< num++<< " Top func: "<<F->getName()<<"\n";
	omp_unset_lock(lock);
#else
	OP<< "\n"<< num++<< " Top func: "<<F->getName()<<"\n";
#endif

    list<User *>LU;
    set<User *> GU; //Global value set to avoid loop
	for(User *U : F->users()){
        //OP<<"U: "<<*U<<"\n";
		LU.push_back(U);
	}

    list<Value *>AnalysisList;
	set<Value *> AnalyzedList; //Global value set to avoid loop
	AnalysisList.clear();
	AnalyzedList.clear();

    while (!LU.empty()) {
        Value *V = LU.front();
        User *U = dyn_cast<User>(V);
        LU.pop_front();

        if (GU.find(U) != GU.end()){
            continue;
        }
        GU.insert(U);

        //Use as a func arg
        CallInst *CAI = dyn_cast<CallInst>(U);
        if(CAI){
            
            Function* icaller = CAI->getFunction();
            analyzeFunction(icaller, aliasCtx, Ctx);

            if(!Ctx->Callees.count(CAI)){
                continue;
            }

            //OP<<"used in: "<<*CAI<<"\n";
            
            unsigned argnum = CAI->arg_size();

            for(Function *f : Ctx->Callees[CAI]){
                //OP<<"f: "<<*f<<"\n"; 
                HandleReturn(f, CAI, aliasCtx);

                analyzeFunction(f, aliasCtx, Ctx);

                //f's caller is CAI, so we do not need to analysis its args in the futhure
                vector<Value *>f_arg_vec;
                f_arg_vec.clear();
                for(auto it = f->arg_begin(); it != f->arg_end(); it++){
                    f_arg_vec.push_back(it);
                    AnalyzedList.insert(it);
                }

                auto f_arg_size = f->arg_size();
                unsigned min_num = getMin(f_arg_size, argnum);
                for(unsigned j = 0; j < min_num; j++){
                    Value* CAI_arg = CAI->getArgOperand(j);
                    HandleMove(CAI_arg, f_arg_vec[j], aliasCtx);
                }

                //Now the graph has been extened, update analysis targets
                set<Value*> Covered_value_Set;
                Covered_value_Set.clear();
                valueSetMerge(Covered_value_Set, AnalyzedList);
                for(auto it = AnalysisList.begin(); it != AnalysisList.end(); it++){
                    Covered_value_Set.insert(*it);
                }

                set<Value*> targetValueSet;
                getClusterValues(U, targetValueSet, aliasCtx);
                for(auto it = targetValueSet.begin(); it != targetValueSet.end(); it++){
                    Value* target_v = *it;
                    if(Covered_value_Set.count(target_v))
                        continue;
                    
                    AnalysisList.push_back(target_v);
                }

                if(AnalysisList.size() > MAX_ANALYSIS_NUM){
                    aliasCtx->Is_Analyze_Success = false;
                    break;
                }

            }
            continue;
        }

        //Usually store inst
        Instruction *iInst = dyn_cast<Instruction>(U);
        if(iInst){
            //OP<<"is instruction\n";
            //OP<<*iInst<<"\n";
            Function* icaller = iInst->getFunction();
            analyzeFunction(icaller, aliasCtx, Ctx);
            continue;
        }

        GEPOperator *GEPO = dyn_cast<GEPOperator>(U);
        BitCastOperator *CastO = dyn_cast<BitCastOperator>(U);
        PtrToIntOperator *PTIO = dyn_cast<PtrToIntOperator>(U);
        ConstantAggregate *CA = dyn_cast<ConstantAggregate>(U);
        GlobalAlias* Ga = dyn_cast<GlobalAlias>(U);
        
        if(GEPO || CastO || PTIO || CA || Ga){
            for(User *u : U->users()){
                LU.push_back(u);
            }
            continue;
        }

        GlobalVariable* Gv = dyn_cast<GlobalVariable>(U);
        //GlobalAlias* Ga = dyn_cast<GlobalAlias>(U);
        if(Gv){
            AnalysisList.push_back(U);
            continue;
        }
#ifdef ENAMBE_OMP
        omp_set_lock(lock);
        OP<<"WARNNING: unsupported user: "<<*U<<"\n";
        omp_unset_lock(lock);
#else
        OP<<"WARNNING: unsupported user: "<<*U<<"\n";
#endif
        
    }

    set<Value*> targetValueSet;
    getClusterValues(F, targetValueSet, aliasCtx);
    for(auto it = targetValueSet.begin(); it != targetValueSet.end(); it++){
        Value* target_v = *it;
        if(target_v == F)
            continue;
        //OP<<"target_v: "<<*target_v<<"\n";
        AnalysisList.push_back(target_v);
    }

    if(AnalysisList.size() > MAX_ANALYSIS_NUM){
        aliasCtx->Is_Analyze_Success = false;
        return;
    }


    while (!AnalysisList.empty()) {
		Value *CV = AnalysisList.front();
		AnalysisList.pop_front();

		if (AnalyzedList.find(CV) != AnalyzedList.end()){
			continue;
		}
		AnalyzedList.insert(CV);

		if(aliasCtx->Is_Analyze_Success == false)
			break;

		//Too complex, stop analysis
		if(AnalysisList.size() > MAX_ANALYSIS_NUM){
			aliasCtx->Is_Analyze_Success = false;
			break;
		}

		interCaseHandler(CV, AnalysisList, AnalyzedList, aliasCtx, Ctx);
	}

    if(aliasCtx->Is_Analyze_Success == false)
		return;

    getClusterValues(F, targetValueSet, aliasCtx);

#ifdef PRINT_ALIAS_RESULT
	OP<<"\n func aliased v: \n";
#endif
	for(auto it = targetValueSet.begin(); it != targetValueSet.end(); it++){
		Value* aliased_v = *it;
        //OP<<*aliased_v<<"\n";
        bool found = false;
        for(User *U : aliased_v->users()){
            CallInst* CAI = dyn_cast<CallInst>(U);
            if(CAI){
                Value *CalledOperand = CAI->getCalledOperand();
                if(CalledOperand == aliased_v){
                    found = true;
#ifdef PRINT_ALIAS_RESULT
		            OP<<"aliased_v: "<<*CAI<<"\n";
#endif	
                    callset.insert(CAI);
                }
            }
        }

	

	}


}