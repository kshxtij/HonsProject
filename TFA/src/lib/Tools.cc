#include "Tools.h"

//Used for debug
unsigned getInstLineNo(Instruction *I){

    begin:

    if(!I){
        return 0;
    }
        
    //DILocation *Loc = dyn_cast<DILocation>(N);
    DILocation *Loc = I->getDebugLoc();
    if (!Loc ){
        //OP << "No such DILocation\n";
        auto nextinst = I->getNextNonDebugInstruction();
        I = nextinst;
		//return 0;
        goto begin;
    }

    unsigned Number = Loc->getLine();
    //Loc->getFilename();
    //Loc->getDirectory();

    if(Number < 1){
        //OP << "Number < 1\n";
        auto nextinst = I->getNextNonDebugInstruction();
        I = nextinst;
        goto begin;
    }

    return Number;
}

//Used for debug
unsigned getInstLineNo(Function *F){

    if(!F){
        return 0;
    }
        
    //DILocation *Loc = dyn_cast<DILocation>(N);
    MDNode *N = F->getMetadata("dbg");
    if (!N)
        return 0;

    //DILocation *Loc = F->getDebugLoc();
    DISubprogram *Loc = dyn_cast<DISubprogram>(N);
    if (!Loc ){
		return 0;
    }

    unsigned Number = Loc->getLine();

    return Number;
}


//Used for debug
std::string getInstFilename(Instruction *I){
    begin:

    if(!I){
        return "";
    }
        
    //DILocation *Loc = dyn_cast<DILocation>(N);
    DILocation *Loc = I->getDebugLoc();
    if (!Loc ){
        auto nextinst = I->getNextNonDebugInstruction();
        I = nextinst;
		//return 0;
        goto begin;
    }

    string Filename = Loc->getFilename().str();

    if(Filename.length() == 0){
        auto nextinst = I->getNextNonDebugInstruction();
        I = nextinst;
        goto begin;
    }

    return Filename;
}

//Used for debug
string getBlockName(BasicBlock *bb){
    if(bb == NULL)
        return "NULL block";
    std::string Str;
    raw_string_ostream OS(Str);
    bb->printAsOperand(OS,false);
    return OS.str();
}

//Used for debug
string getValueName(Value* V){
    std::string Str;
    raw_string_ostream OS(Str);
    V->printAsOperand(OS,false);
    return OS.str();
}

//Used for debug
std::string getValueContent(Value* V){
    std::string Str;
    raw_string_ostream OS(Str);
    V->print(OS,false);
    return OS.str();
}

//Used for debug
void printInstMessage(Instruction *inst){
    if(!inst){
        OP << "No such instruction";
        return;
    }
        
    MDNode *N = inst->getMetadata("dbg");

    if (!N)
        return;
    
    DILocation *Loc = dyn_cast<DILocation>(N);
    string SCheckFileName = Loc->getFilename().str();
    unsigned SCheckLineNo = Loc->getLine();
    //OP << "Filename: "<<SCheckFileName<<"\n";
    OP << "LineNo: " << SCheckLineNo<<"\n";

}

//Used for debug
void printBlockMessage(BasicBlock *bb){

    if(!bb){
        OP << "No such block";
        return;
    }
    
    auto begininst = dyn_cast<Instruction>(bb->begin());
    auto endinst = bb->getTerminator();

    OP << "\nBegin at --- ";
    printInstMessage(begininst);
    OP << "End   at --- ";
    printInstMessage(endinst);

    /* for(BasicBlock::iterator i = bb->begin(); 
        i != bb->end(); i++){

        auto midinst = dyn_cast<Instruction>(i);
        printInstMessage(midinst);        
    } */

}

//Used for debug
void printBlockLineNoRange(BasicBlock *bb){
    if(!bb){
        OP << "No such block";
        return;
    }
    
    auto begininst = dyn_cast<Instruction>(bb->begin());
    auto endinst = bb->getTerminator();

    OP << "("<<getInstLineNo(begininst)<<"-"<<getInstLineNo(endinst)<<")";

}

//Used for debug
void printFunctionMessage(Function *F){

    if(!F)
        return;
    
    for(Function::iterator b = F->begin(); 
        b != F->end(); b++){
        
        BasicBlock * bb = &*b;
        OP << "\nCurrent block: block-"<<getBlockName(bb)<<"\n";
        //printBlockMessage(bb);

        OP << "Succ block: \n";
        for (BasicBlock *Succ : successors(bb)) {
			//printBlockMessage(Succ);
            OP << " block-"<<getBlockName(Succ)<<" ";
		}

        OP<< "\n";
    }
}

//Check if there exits common element of two sets
bool findCommonOfSet(set<Value *> setA, set<Value *> setB){
    if(setA.empty() || setB.empty())
        return false;
    
    bool foundtag = false;
    for(auto i = setA.begin(); i != setA.end(); i++){
        Value * vi = *i;
        for(auto j = setB.begin(); j != setB.end(); j++){
            Value * vj = *j;
            if(vi == vj){
                foundtag = true;
                return foundtag;
            }
        }
    }

    return foundtag;
}

bool findCommonOfSet(set<std::string> setA, set<std::string> setB){
    if(setA.empty() || setB.empty())
        return false;
    
    bool foundtag = false;
    for(auto i = setA.begin(); i != setA.end(); i++){
        string vi = *i;
        for(auto j = setB.begin(); j != setB.end(); j++){
            string vj = *j;
            if(vi == vj){
                foundtag = true;
                return foundtag;
            }
        }
    }

    return foundtag;
}


/// Check alias result of two values.
/// True: alias, False: not alias.
bool checkAlias(Value *Addr1, Value *Addr2,
		PointerAnalysisMap &aliasPtrs) {

	if (Addr1 == Addr2)
		return true;

	auto it = aliasPtrs.find(Addr1);
	if (it != aliasPtrs.end()) {
		if (it->second.count(Addr2) != 0)
			return true;
	}

	// May not need to do this further check.
	it = aliasPtrs.find(Addr2);
	if (it != aliasPtrs.end()) {
		if (it->second.count(Addr1) != 0)
			return true;
	}

	return false;
}


bool checkStringContainSubString(string origstr, string targetsubstr){
    
    if(origstr.length() == 0 || targetsubstr.length() == 0)
        return false;
    
    string::size_type idx;
    idx = origstr.find(targetsubstr);
    if(idx == string::npos)
        return false;
    else
        return true;
}

//Check if there is a path from fromBB to toBB 
bool checkBlockPairConnectivity(
    BasicBlock* fromBB, 
    BasicBlock* toBB){

    if(fromBB == NULL || toBB == NULL)
        return false;
    
    //Use BFS to detect if there is a path from fromBB to toBB
    std::list<BasicBlock *> EB; //BFS record list
    std::set<BasicBlock *> PB; //Global value set to avoid loop
    EB.push_back(fromBB);

    while (!EB.empty()) {

        BasicBlock *TB = EB.front(); //Current checking block
		EB.pop_front();

		if (PB.find(TB) != PB.end())
			continue;
		PB.insert(TB);

        //Found a path
        if(TB == toBB)
            return true;

        auto TI = TB->getTerminator();

        for(BasicBlock *Succ: successors(TB)){

            EB.push_back(Succ);
        }

    }//end while

    return false;
}

//Used for data recording
void pairFuncDataRecord(GlobalContext *Ctx){

    if(Ctx->Global_Func_Pair_Set.empty())
        return;

    ofstream oFile;
    oFile.open("Pair_func_sheet.csv", ios::out | ios::trunc);

    oFile << "Number"<<","<<"init function"<< ","<<"fini function"<< "," << "pair type" <<"\n";
    int count = 1;
    for(auto it = Ctx->Global_Func_Pair_Set.begin(); it != Ctx->Global_Func_Pair_Set.end(); it++){

        PairInfo funcpair = *it;
        Function* initfunc = funcpair.initfunc;
        Function* finifunc = funcpair.finifunc;
        int pairtype = funcpair.type;

        switch(pairtype){
            case MODULE_FUNC:
                oFile << count <<"," << initfunc->getName().str() << "," << finifunc->getName().str() << "," << "module func" <<"\n";
                break;
            case MODULE_FUNC_WRAPPER:
                oFile << count <<"," << initfunc->getName().str() << "," << finifunc->getName().str() << "," << "module func wrapper" <<"\n";
                break;
            default:
                oFile << count <<"," << initfunc->getName().str() << "," << finifunc->getName().str() << "," << "unknown" <<"\n";
                break;
        }

        count++;
    }
        
    oFile.close();

}

//Used for debug
void messageRecord(GlobalContext *Ctx){

    if(Ctx->Global_Debug_Message_Set.empty())
        return;

    ofstream oFile;
    oFile.open("Other_source.csv", ios::out | ios::trunc);

    //oFile << "name"<<","<<"age"<< ","<<"class"<<","<<"people"<<"\n";
    //oFile << "zhangsan"<<","<<"22"<< ","<<"1"<<","<<"JIM"<<"\n";
    //oFile << "lish"<<","<<"23"<< ","<<"3"<<","<<"TOM"<<"\n";
    oFile << "Number"<<","<<"source line"<<"\n";
    int count = 1;
    for(auto it = Ctx->Global_Debug_Message_Set.begin(); it != Ctx->Global_Debug_Message_Set.end(); it++){

        string func = *it;
        oFile << count <<"," << func << "\n";

        count++;
    }
        
    oFile.close();
}

//Used for data recording of structure keywords
void keywordsRecord(GlobalContext *Ctx){

    if(Ctx->Global_Keywords_Map.empty())
        return;

    ofstream oFile;
    oFile.open("Keywords_sheet.csv", ios::out | ios::trunc);
    oFile << "Number"<<","<<"keywords"<< ","<<"quantity" <<"\n";
    int count = 1;

    for(auto it = Ctx->Global_Keywords_Map.begin(); it != Ctx->Global_Keywords_Map.end(); it++){

        pair<string, int> pair = *it;
        string keywords = pair.first;
        int num = pair.second;
        oFile << count <<"," << keywords << "," << num << "\n";

        count++;
    }

    oFile.close();
}

//Used for global call graph debug
void icallTargetResult(GlobalContext *Ctx){

    if(Ctx->Callers.empty())
        return;

    unsigned long long NumCallee = 0;

    /*for(auto i = Ctx->Callers.begin(); i!= Ctx->Callers.end(); i++){
        Function* F = i->first;
        CallInstSet callset = i->second;
        if(F->getName() != "dptf_power_add")
            continue;
        OP<<"F: "<<F->getName()<<"\n";
        for(auto j = callset.begin(); j!= callset.end(); j++){
            NumCallee++;
            CallInst* callinst = *j;
            //OP<<" --callinst: "<<*callinst<<"\n";
            Function* parrent = callinst->getFunction();
            OP<<" --caller: "<<parrent->getName()<< " " << *callinst<< "\n";
        }
    }*/

    //Test callee set
    if(Ctx->Callees.empty())
        return;
    unsigned long long maxicall = 0;
    unsigned long long icallnum = Ctx->IndirectCallInsts.size();
    unsigned long long total_icall_targets = 0;

    std::vector<std::pair<unsigned long long, CallInst*>> icall_vec;
    icall_vec.clear();

    ofstream oFile;
    oFile.open("ICall_analysis_sheet.csv", ios::out | ios::trunc);
    oFile << "ID"<<","<<"icall target num"<< "," << "caller" << ",";
    oFile << "line number" << "," << "location" << "," << "MLTA result" <<"\n";

    for(auto i = Ctx->ICallees.begin(); i!= Ctx->ICallees.end(); i++){
        CallInst* cai = i->first;
        FuncSet fset = i->second;
        unsigned long long num = fset.size();
        icall_vec.push_back(make_pair(num,cai));
        total_icall_targets+=num;
        if(num>maxicall)
            maxicall = num;
    }
    unsigned long long id = 1;
    std::sort(icall_vec.begin(), icall_vec.end());
    for(auto i = icall_vec.begin(); i != icall_vec.end(); i++){
        
        CallInst* cai = i->second;
        Function* caller = cai->getFunction();

        oFile << id << "," << i->first << "," << caller->getName().str() << ",";
        //oFile << Ctx->ValidICalls.count(cai);
        unsigned lineNo = getInstLineNo(cai);
        oFile<< lineNo <<",";

        Module* M = caller->getParent();
        oFile << M->getName().str() <<",";

        switch(Ctx->Global_MLTA_Reualt_Map[cai]){
            case TypeEscape:
                oFile << "TypeEscape";
                break;
            case OneLayer:
                oFile << "OneLayer";
                break;
            case TwoLayer:
                oFile << "TwoLayer";
                break;
            case ThreeLayer:
                oFile << "ThreeLayer";
                break;
            case NoTwoLayerInfo:
                oFile << "NoTwoLayerInfo";
                break;
            default:
                oFile << "unknown";
                break;
        }

        oFile << "\n";
        id++;
    }

    oFile.close();

    OP<<"Max callee num: "<<maxicall<<"\n";
    OP<<"Total icall targets num: "<<total_icall_targets<<"\n";

}

bool isCompositeType(Type *Ty) {
	if (Ty->isStructTy() 
			|| Ty->isArrayTy() 
			|| Ty->isVectorTy())
		return true;
	else 
		return false;
}

bool isStructorArrayType(Type *Ty) {
	if (Ty->isStructTy() || Ty->isArrayTy() )
		return true;
	else 
		return false;
}

size_t funcInfoHash(Function *F){
    
    hash<string> str_hash;
	string output;
    
    DISubprogram *SP = F->getSubprogram();

	if (SP) {
		output = SP->getFilename().str();
        stringstream ss;
        unsigned linenum = SP->getLine();
        ss<<linenum;
		output += ss.str();
	}

	output += F->getName();

	string::iterator end_pos = remove(output.begin(), 
			output.end(), ' ');
	output.erase(end_pos, output.end());
	
	//OP<<"output: "<<output<<"\n";

	return str_hash(output);

}

//Get the target string of __symbol_get()
string symbol_get_hander(CallInst* CAI){

    if(!CAI)
        return "";

    Value* __symbol_get_arg = CAI->getArgOperand(0);
    //OP<<"__symbol_get_arg: "<<*__symbol_get_arg<<"\n";
    if(GEPOperator *GEP = dyn_cast<GEPOperator>(__symbol_get_arg)){
        if(!GEP->hasAllConstantIndices())
            return "";
        
        for(auto it = GEP->idx_begin() + 1; it != GEP->idx_end(); it++){
            ConstantInt *ConstI = dyn_cast<ConstantInt>(it->get());
            int Id = ConstI->getSExtValue();
            if(Id != 0)
                return "";
        }

        Value *PO = GEP->getPointerOperand();
        //OP<<"PO: "<<*PO<<"\n";
        GlobalVariable* globalvar = dyn_cast<GlobalVariable>(PO);
        if(!globalvar)
            return "";
        
        Constant *Ini = globalvar->getInitializer();
        //OP<<"Ini: "<<*Ini<<"\n";
        ConstantDataArray* CDA = dyn_cast<ConstantDataArray>(Ini);
        if(!CDA)
            return "";

        StringRef name = CDA->getAsString();
        if(name.size() == 0)
            return "";

        //NOTE: we need to filter the last char in the string
        return name.str().substr(0, name.str().length()-1);
    
    }

    return "";
}