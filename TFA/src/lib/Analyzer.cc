#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/Path.h"

#include <memory>
#include <vector>
#include <sstream>
#include <sys/resource.h>

#include "Analyzer.h"
#include "TypeBuilder/TypeBuilder.h"
#include "CallGraph/CallGraph.h"
#include "Config.h"
#include "AliasAnalysis/AliasAnalysis.h"

#if _OPENMP
#include <omp.h>
#endif
#include <iostream>
#include <sys/time.h>

using namespace llvm;

// Command line parameters.
cl::list<std::string> InputFilenames(
	cl::Positional, cl::OneOrMore, cl::desc("<input bitcode files>"));

cl::opt<unsigned> VerboseLevel(
	"verbose-level", cl::desc("Print information at which verbose level"),
	cl::init(0));

cl::opt<bool> CriticalVar(
	"krc",
	cl::desc("Identify compiler-introduced TOCTTOU bugs"),
	cl::NotHidden, cl::init(false));

GlobalContext GlobalCtx;

void IterativeModulePass::run(ModuleList &modules)
{

	ModuleList::iterator i, e;
	OP << "[" << ID << "] Initializing " << modules.size() << " modules ";
	bool again = true;

	// Initialize
	while (again)
	{
		again = false;
		for (i = modules.begin(), e = modules.end(); i != e; ++i)
		{
			again |= doInitialization(i->first);
			OP << ".";
		}
	}
	OP << "\n";

	// Execute main analysis pass
	unsigned iter = 0, changed = 1;
	while (changed)
	{
		++iter;
		changed = 0;
		unsigned counter_modules = 0;
		unsigned total_modules = modules.size();

		// #pragma omp parallel for
		for (int it = 0; it < total_modules; ++it)
		{
			OP << "[" << ID << " / " << iter << "] ";
			OP << "[" << ++counter_modules << " / " << total_modules << "] ";
			OP << "[" << modules[it].second << "]\n";

			bool ret = doModulePass(modules[it].first);
			if (ret)
			{
				++changed;
				OP << "\t [CHANGED]\n";
			}
			else
				OP << "\n";
		}
		OP << "[" << ID << "] Updated in " << changed << " modules.\n";
	}

	// Postprocessing
	OP << "[" << ID << "] Postprocessing ...\n";
	again = true;
	while (again)
	{
		again = false;
		for (i = modules.begin(), e = modules.end(); i != e; ++i)
		{
			// TODO: Dump the results.
			again |= doFinalization(i->first);
		}
	}

	OP << "[" << ID << "] Done!\n\n";
}

void LoadStaticData(GlobalContext *GCtx)
{

	// Set safe macros (macros that have nothing to do with func pointer init)
	SetSafeMacros(GCtx->SafeMacros);

	// Load member get functions
	SetMemberGetFuncs(GCtx->MemberGetFuncs);

	// Load error-handling functions
	SetErrorHandleFuncs(GCtx->ErrorHandleFuncs);

	// load functions that copy/move values
	SetCopyFuncs(GCtx->CopyFuncs);

	// load llvm debug functions
	SetDebugFuncs(GCtx->DebugFuncs);

	// load heap alloc functions
	SetHeapAllocFuncs(GCtx->HeapAllocFuncs);

	// load ignore instructions
	SetBinaryOperandInsts(GCtx->BinaryOperandInsts);

	// load ignore instructions
	SetSingleOperandInsts(GCtx->SingleOperandInsts);

	// Load test functions
	SetTestFuncs(GCtx->TestFuncs);
}

vector<long long> reduce_num_total;
vector<long long> reduce_num_icall;
vector<long long> reduce_num_func;
vector<long long> reduce_num_onelayer;
vector<long long> reduce_num_escape;

void PrintResults(GlobalContext *GCtx)
{

	size_t two_layer_icall_num = 0;
	size_t one_layer_icall_num = 0;
	size_t mix_layer_icall_num = 0;
	size_t escape_icall_num = 0;
	for (auto it = GCtx->Global_MLTA_Reualt_Map.begin(); it != GCtx->Global_MLTA_Reualt_Map.end(); it++)
	{
		TypeAnalyzeResult type_result = it->second;
		if (type_result == TwoLayer)
			two_layer_icall_num++;
		else if (type_result == OneLayer)
			one_layer_icall_num++;
		else if (type_result == MixedLayer)
			mix_layer_icall_num++;
		else if (type_result == TypeEscape)
			escape_icall_num++;
	}

	OP << "############## Result Statistics ##############\n";
	OP << "# Number total icall targets   \t\t\t" << GCtx->icallTargets << "\n";
	OP << "# Number 1-layer icall targets \t\t\t" << GCtx->icallTargets_OneLayer << "\n";
	OP << "# Number 2-layer icall targets \t\t\t" << GCtx->valied_icallTargets << "\n";
	OP << "# Number icalls \t\t\t\t" << GCtx->IndirectCallInsts.size() << "\n";
	OP << "# Number 2-layer icalls \t\t\t" << two_layer_icall_num << "\n";
	OP << "# Number 1-layer icalls \t\t\t" << one_layer_icall_num << "\n";
	OP << "# Number mixed layer icalls \t\t\t" << mix_layer_icall_num << "\n";
	OP << "# Number escaped icalls \t\t\t" << escape_icall_num << "\n";
	OP << "# Number escaped stores \t\t\t" << GCtx->num_escape_store << "\n";
	OP << "# Number escaped struct def \t\t\t" << GCtx->Global_missing_type_def_struct_num << "\n";
	OP << "# Number anon pre layer \t\t\t" << GCtx->Global_pre_anon_icall_num << "\n";
	OP << "# Number 1-layer set size\t\t\t" << GCtx->sigFuncsMap.size() << "\n";
	OP << "\n";

	OP << "############## Type Info Statistics ##############\n";
	OP << "# Number Global_SGV_with_name   \t\t" << GCtx->num_typebuilder_haveStructName << "\n";
	OP << "# Number Global_SGV_without_name\t\t" << GCtx->num_typebuilder_haveNoStructName << "\n";
	OP << "# Number emptyNameWithDebuginfo \t\t" << GCtx->num_emptyNameWithDebuginfo << "\n";
	OP << "# Number emptyNameWithoutDebuginfo \t\t" << GCtx->num_emptyNameWithoutDebuginfo << "\n";
	OP << "# Number num_haveLayerStructName \t\t" << GCtx->num_haveLayerStructName << "\n";
	OP << "# Number num_local_info_name     \t\t" << GCtx->num_local_info_name << "\n";
	OP << "# Number Global_EmptyTy_Funcs    \t\t" << GCtx->Global_EmptyTy_Funcs.size() << "\n";
	OP << "# Number Globa_Union_Set         \t\t" << GCtx->Globa_Union_Set.size() << "\n";
	OP << "# Number num_array_prelayer      \t\t" << GCtx->num_array_prelayer << "\n";
	OP << "\n";

	OP << "############## Alias Info Statistics ##############\n";
	OP << "# Number succeed alias icall \t\t\t" << GCtx->icall_support_dataflow_Number << "\n";
	OP << "# Number succeed func icall  \t\t\t" << GCtx->func_support_dataflow_Number << "\n";
	OP << "\n  Failed reasons:\n";
	OP << "# Number F has no global definition  \t\t" << GCtx->failure_reasons[F_has_no_global_definition] << "\n";
	OP << "# Number binary_operation    \t\t\t" << GCtx->failure_reasons[binary_operation] << "\n";
	OP << "# Number llvm_used           \t\t\t" << GCtx->failure_reasons[llvm_used] << "\n";
	OP << "# Number exceed_max          \t\t\t" << GCtx->failure_reasons[exceed_max] << "\n";

	OP << "\n";
	std::cout.precision(8);

	OP << "############## Time Statistics ##############\n";
	std::cout << "# Load time            \t\t" << GCtx->Load_time << "\n";
	std::cout << "# Typebuilder time     \t\t" << GCtx->Typebuilder_time << "\n";
	std::cout << "# MLTA time            \t\t" << GCtx->MLTA_time << "\n";
	std::cout << "# Icall alias time     \t\t" << GCtx->Icall_alias_time << "\n";
	std::cout << "# Func alias time      \t\t" << GCtx->Func_alias_time << "\n";
	std::cout << "# One layer alias time \t\t" << GCtx->Onelayer_alias_time << "\n";
	std::cout << "# Escape alias time    \t\t" << GCtx->Escape_alias_time << "\n";
	std::cout << "# DB time              \t\t" << GCtx->Database_time << "\n";
	OP << "\n";

	OP << "############## Round Statistics ##############\n";
	for (auto it = 0; it < reduce_num_total.size(); it++)
	{
		OP << "Round: " << it << "\n";
		OP << "reduce_num_icall: " << reduce_num_icall[it] << "\n";
		OP << "reduce_num_func: " << reduce_num_func[it] << "\n";
		OP << "reduce_num_onelayer: " << reduce_num_onelayer[it] << "\n";
		OP << "reduce_num_escape: " << reduce_num_escape[it] << "\n";
		OP << "reduce_num_total: " << reduce_num_total[it] << "\n";
		OP << "\n";
	}

	OP << "\n";
}

int main(int argc, char **argv)
{
	// Print a stack trace if we signal out.
	sys::PrintStackTraceOnErrorSignal(argv[0]);
	PrettyStackTraceProgram X(argc, argv);

	timeval start_time, end_time;

	llvm_shutdown_obj Y; // Call llvm_shutdown() on exit.

	cl::ParseCommandLineOptions(argc, argv, "global analysis\n");
	SMDiagnostic Err;

	// Loading modules
	OP << "Total " << InputFilenames.size() << " file(s)\n";

#if _OPENMP
	OP << "Openmp enabled\n";
#else
	OP << "Openmp is not supported\n";
#endif

	// Use omp to speed up bitcode loading
	gettimeofday(&start_time, 0);
	// start_time = time();
	omp_lock_t lock;
	omp_init_lock(&lock);

#pragma omp parallel for num_threads(32)
	for (unsigned i = 0; i < InputFilenames.size(); ++i)
	{

		LLVMContext *LLVMCtx = new LLVMContext();
		std::unique_ptr<Module> M = parseIRFile(InputFilenames[i], Err, *LLVMCtx);

		if (M == NULL)
		{
			OP << argv[0] << ": error loading file '"
			   << InputFilenames[i] << "'\n";
			continue;
		}
		StringRef MName = StringRef(strdup(InputFilenames[i].data()));

		omp_set_lock(&lock);
		Module *Module = M.release();
		// OP<<"load module: "<<MName<<"\n";
		GlobalCtx.Modules.push_back(std::make_pair(Module, MName));
		GlobalCtx.ModuleMaps[Module] = InputFilenames[i];
		omp_unset_lock(&lock);
	}

	// Main workflow
	LoadStaticData(&GlobalCtx);
	gettimeofday(&end_time, 0);
	GlobalCtx.Load_time = (end_time.tv_sec - start_time.tv_sec) + (double)(end_time.tv_usec - start_time.tv_usec) / 1000000.0;

	// Type builder
	gettimeofday(&start_time, 0);
	TypeBuilderPass TBPass(&GlobalCtx);
	TBPass.run(GlobalCtx.Modules);
	gettimeofday(&end_time, 0);
	GlobalCtx.Typebuilder_time = (end_time.tv_sec - start_time.tv_sec) + (double)(end_time.tv_usec - start_time.tv_usec) / 1000000.0;

	// Build global callgraph.
	gettimeofday(&start_time, 0);
	CallGraphPass CGPass(&GlobalCtx);
	CGPass.run(GlobalCtx.Modules);
	gettimeofday(&end_time, 0);
	GlobalCtx.MLTA_time = (end_time.tv_sec - start_time.tv_sec) + (double)(end_time.tv_usec - start_time.tv_usec) / 1000000.0;

	if (CriticalVar)
	{

		long long pre_num, cur_num, loop_num;
		long long pre_num_round, cur_num_round;
		loop_num = 0;

		while (true)
		{
			pre_num = GlobalCtx.icallTargets;
			pre_num_round = GlobalCtx.icallTargets;

			gettimeofday(&start_time, 0);
			FuncAliasAnalysis(&GlobalCtx);
			gettimeofday(&end_time, 0);
			GlobalCtx.Func_alias_time += (end_time.tv_sec - start_time.tv_sec) + (double)(end_time.tv_usec - start_time.tv_usec) / 1000000.0;

			cur_num = GlobalCtx.icallTargets;
			reduce_num_func.push_back(pre_num - cur_num);
			pre_num = GlobalCtx.icallTargets;

			gettimeofday(&start_time, 0);
			ICallAliasAnalysis(&GlobalCtx);
			gettimeofday(&end_time, 0);
			GlobalCtx.Icall_alias_time += (end_time.tv_sec - start_time.tv_sec) + (double)(end_time.tv_usec - start_time.tv_usec) / 1000000.0;

			cur_num = GlobalCtx.icallTargets;
			reduce_num_icall.push_back(pre_num - cur_num);
			pre_num = GlobalCtx.icallTargets;

			gettimeofday(&start_time, 0);
			oneLayerHandler(&GlobalCtx);
			gettimeofday(&end_time, 0);
			GlobalCtx.Onelayer_alias_time += (end_time.tv_sec - start_time.tv_sec) + (double)(end_time.tv_usec - start_time.tv_usec) / 1000000.0;

			cur_num = GlobalCtx.icallTargets;
			reduce_num_onelayer.push_back(pre_num - cur_num);
			pre_num = GlobalCtx.icallTargets;

			gettimeofday(&start_time, 0);
			CGPass.escapeHandler();
			gettimeofday(&end_time, 0);
			GlobalCtx.Escape_alias_time += (end_time.tv_sec - start_time.tv_sec) + (double)(end_time.tv_usec - start_time.tv_usec) / 1000000.0;

			cur_num = GlobalCtx.icallTargets;
			reduce_num_escape.push_back(pre_num - cur_num);
			pre_num = GlobalCtx.icallTargets;

			cur_num_round = GlobalCtx.icallTargets;

			reduce_num_total.push_back(pre_num_round - cur_num_round);

			loop_num++;

			if ((pre_num_round - cur_num_round) < 10000)
			{
				break;
			}
		}

		OP << "loop num: " << loop_num << "\n";
	}

	PrintResults(&GlobalCtx);

	omp_destroy_lock(&lock);
	return 0;
}
