#include "llvm/Support/Signals.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/IRReader/IRReader.h"

#include <omp.h>
#include <iostream>
#include <sys/time.h>

using namespace llvm;

cl::list<std::string> InputFilenames(
    cl::Positional, cl::OneOrMore, cl::desc("<input bitcode files>"));

int main(int argc, char **argv) {

	// Print a stack trace if we signal out.
	sys::PrintStackTraceOnErrorSignal(argv[0]);
	PrettyStackTraceProgram X(argc, argv);

	llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.

    cl::ParseCommandLineOptions(argc, argv, "global analysis\n");
	SMDiagnostic Err;

	// Loading modules
	llvm::errs() << "Total " << InputFilenames.size() << " file(s)\n";

    #if _OPENMP
	    llvm::errs() << "Openmp enabled\n";
    #else
        llvm::errs() << "Openmp is not supported\n";
    #endif

	struct timeval start, end;
	gettimeofday(&start, NULL);
	omp_lock_t lock;
	omp_init_lock(&lock);

	int failed = 0;
	#pragma omp parallel for num_threads(32)
	for (int i = 0; i < InputFilenames.size(); i++) {
		LLVMContext *LLVMCtx = new LLVMContext();
		std::unique_ptr<Module> M = parseIRFile(InputFilenames[i], Err, *LLVMCtx);
		if (!M) {
			llvm::errs() << "Error reading bitcode file: " << InputFilenames[i] << "\n";
			llvm::errs() << Err.getMessage() << "\n";
			omp_set_lock(&lock);
			failed++;
			omp_unset_lock(&lock);
		}
	}
    
	gettimeofday(&end, NULL);
	omp_destroy_lock(&lock);

	llvm::errs() << "Loaded " << (InputFilenames.size() - failed) << " file(s) in " << (end.tv_sec - start.tv_sec) << " seconds\n";
    return 0;
}