#ifndef _SACONFIG_H
#define _SACONFIG_H

#include "llvm/Support/FileSystem.h"

#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <fstream>

//
// Configurations for compilation.
//
//#define VERBOSE_SA 1
//#define DEBUG_SA 1
#define SOUND_MODE 1

// Skip functions with more blocks to avoid scalability issues
#define MAX_BLOCKS_SUPPORT 500

//#define RESULTS_FILE "/tmp/Result.txt"

// magic code for identifying error codes
//#define ERRNO_PREFIX 0x4cedb000
//#define ERRNO_MASK   0xfffff000
//#define is_errno(x) (((x) & ERRNO_MASK) == ERRNO_PREFIX)

static void SetSafeMacros(set<string> &SafeMacros) {

  string exepath = sys::fs::getMainExecutable(NULL, NULL);
	string exedir = exepath.substr(0, exepath.find_last_of('/'));
  string srcdir = exedir.substr(0, exedir.find_last_of('/'));
  srcdir = srcdir.substr(0, srcdir.find_last_of('/'));
  srcdir = srcdir + "/src/lib";
	string line;
  ifstream errfile(srcdir	+ "/configs/safe-macro-list");
  if (errfile.is_open()) {
		while (!errfile.eof()) {
			getline (errfile, line);
			if (line.length() > 1) {
				SafeMacros.insert(line);
			}
		}
    errfile.close();
  }

}

//Used for debug
static void SetSkipFuncs(set<string> &SkipFuncs) {

  string exepath = sys::fs::getMainExecutable(NULL, NULL);
	string exedir = exepath.substr(0, exepath.find_last_of('/'));
  string srcdir = exedir.substr(0, exedir.find_last_of('/'));
  srcdir = srcdir.substr(0, srcdir.find_last_of('/'));
  srcdir = srcdir + "/src/lib";
	string line;
  ifstream errfile(srcdir	+ "/configs/krace-skip-funcs");
  if (errfile.is_open()) {
		while (!errfile.eof()) {
			getline (errfile, line);
			if (line.length() > 1) {
				SkipFuncs.insert(line);
			}
		}
    errfile.close();
  }

}

//Used for debug
static void SetTestFuncs(set<string> &TestFuncs) {

  string exepath = sys::fs::getMainExecutable(NULL, NULL);
	string exedir = exepath.substr(0, exepath.find_last_of('/'));
  string srcdir = exedir.substr(0, exedir.find_last_of('/'));
  srcdir = srcdir.substr(0, srcdir.find_last_of('/'));
  srcdir = srcdir + "/src/lib";
	string line;
  ifstream errfile(srcdir	+ "/configs/test-funcs");
  if (errfile.is_open()) {
		while (!errfile.eof()) {
			getline (errfile, line);
			if (line.length() > 1) {
				TestFuncs.insert(line);
			}
		}
    errfile.close();
  }

}

//Used for debug
static void SetAutoFreedFuncs(set<string> &AutoFreedFuncs) {

  string exepath = sys::fs::getMainExecutable(NULL, NULL);
	string exedir = exepath.substr(0, exepath.find_last_of('/'));
  string srcdir = exedir.substr(0, exedir.find_last_of('/'));
  srcdir = srcdir.substr(0, srcdir.find_last_of('/'));
  srcdir = srcdir + "/src/lib";
	string line;
  ifstream errfile(srcdir	+ "/configs/auto-freed-alloc-funcs");
  if (errfile.is_open()) {
		while (!errfile.eof()) {
			getline (errfile, line);
			if (line.length() > 1) {
				AutoFreedFuncs.insert(line);
			}
		}
    errfile.close();
  }

}

//Used for debug
static void SetEscapeFuncs(set<string> &EscapeFuncs) {

  string exepath = sys::fs::getMainExecutable(NULL, NULL);
	string exedir = exepath.substr(0, exepath.find_last_of('/'));
  string srcdir = exedir.substr(0, exedir.find_last_of('/'));
  srcdir = srcdir.substr(0, srcdir.find_last_of('/'));
  srcdir = srcdir + "/src/lib";
	string line;
  ifstream errfile(srcdir	+ "/configs/escape-funcs");
  if (errfile.is_open()) {
		while (!errfile.eof()) {
			getline (errfile, line);
			if (line.length() > 1) {
				EscapeFuncs.insert(line);
			}
		}
    errfile.close();
  }

}

static void SetMemberGetFuncs(set<string> &MemberGetFuncs) {

  string exepath = sys::fs::getMainExecutable(NULL, NULL);
	string exedir = exepath.substr(0, exepath.find_last_of('/'));
  string srcdir = exedir.substr(0, exedir.find_last_of('/'));
  srcdir = srcdir.substr(0, srcdir.find_last_of('/'));
  srcdir = srcdir + "/src/lib";
	string line;
  ifstream errfile(srcdir	+ "/configs/member-get-funcs");
  if (errfile.is_open()) {
		while (!errfile.eof()) {
			getline (errfile, line);
			if (line.length() > 1) {
				MemberGetFuncs.insert(line);
			}
		}
    errfile.close();
  }

}

// Setup functions that handle errors
static void SetErrorHandleFuncs(set<string> &ErrorHandleFuncs) {

	string exepath = sys::fs::getMainExecutable(NULL, NULL);
	string exedir = exepath.substr(0, exepath.find_last_of('/'));
  string srcdir = exedir.substr(0, exedir.find_last_of('/'));
  srcdir = srcdir.substr(0, srcdir.find_last_of('/'));
  srcdir = srcdir + "/src/lib";
	string line;
  ifstream errfile(srcdir	+ "/configs/err-funcs");
  if (errfile.is_open()) {
		while (!errfile.eof()) {
			getline (errfile, line);
			if (line.length() > 1) {
				ErrorHandleFuncs.insert(line);
			}
		}
    errfile.close();
  }

	string ErrorHandleFN[] = {
		"BUG",
		"BUG_ON",
		"ASM_BUG",
		"panic",
		"ASSERT",
		"assert",
		"dump_stack",
		"__warn_printk",
		"usercopy_warn",
		"signal_fault",
		"pr_err",
		"pr_warn",
		"pr_warning",
		"pr_alert",
		"pr_emerg",
		"pr_crit",
	};
	for (auto F : ErrorHandleFN) {
		ErrorHandleFuncs.insert(F);
	}
}

// Setup sinking functions here.
static void SetSinkFuncs(
		std::unordered_map<std::string, std::set<int>> &SinkFuncs) {

	SinkFuncs["copy_to_user"].insert(1);
	SinkFuncs["__copy_to_user"].insert(1);
	SinkFuncs["nla_put"].insert(3);
	SinkFuncs["put_user"].insert(0);
	SinkFuncs["send_signal"].insert(1);
	SinkFuncs["__send_signal"].insert(1);
	SinkFuncs["vfs_write"].insert(1);
	SinkFuncs["sock_sendmsg"].insert(1);
}

// Setup debug functions here.
static void SetDebugFuncs(
  std::set<std::string> &DebugFuncs){

  std::string DebugFN[] = {
    "llvm.dbg.declare",
    "llvm.dbg.value",
    "llvm.dbg.label",
    "llvm.lifetime.start",
	"llvm.lifetime.end",
    "llvm.lifetime.start.p0i8",
    "llvm.lifetime.end.p0i8",
    "arch_static_branch",
	"printk",
  };

  for (auto F : DebugFN){
    DebugFuncs.insert(F);
  }

}

// Setup Binary Operand instructions here.
static void SetBinaryOperandInsts(
  std::set<std::string> &BinaryOperandInsts){

  std::string BinaryInst[] = {
    "and",
    "or",
    "xor",
    "shl",
    "lshr",
    "ashr",
    "add",
	"fadd",
    "sub",
	"fsub",
    "mul",
	"fmul",
    "sdiv",
    "udiv",
	"fdiv",
    "urem",
    "srem",
	"frem",
    //"alloca",
  };

  for (auto I : BinaryInst){
    BinaryOperandInsts.insert(I);
  }

}

// Setup ignore instructions here.
static void SetSingleOperandInsts(
  std::set<std::string> &SingleOperandInsts){

  std::string SingleOperandInst[] = {
    "bitcast",
    "trunc",
    "sext",
    "zext",
    "inttoptr",
    "ptrtoint",
    "extractvalue",
    "extractelement",

  };

  for (auto I : SingleOperandInst){
    SingleOperandInsts.insert(I);
  }

}

// Setup functions that nerver sink.
static void SetNonSinkFuncs(
		std::set<std::string> &NonSinkFuncs) {

	std::string NonSinkFN[] = {
		"set_bit",
		"clear_bit",
		"__copy_from_user",
		"memset",
		"llvm.memset.p0i8.i64",
		"fpsimd_load_state",
		"get_user_pages_fast",
		"probe_kernel_read",
		"save_stack_trace_regs",
		"ce_aes_ccm_auth_data",
		"llvm.lifetime.start",
		"llvm.lifetime.end",
		"vsscanf",
		"test_and_set_bit",
		"llvm.cttz.i64",
		"__cpu_flush_user_tlb_range",
		"__local_cpu_flush_user_tlb_range",
		"strchr",
		"memchr",
		"strrchr",
		"llvm.ctlz.i64",
		"llvm.ctlz.i32",
		"llvm.uadd.with.overflow.i64",
		"llvm.uadd.with.overflow.i32",
		"llvm.bswap.i32",
		"llvm.bswap.i64",
		"ce_aes_ctr_encrypt",
		"ce_aes_ccm_final",
		"ce_aes_ccm_decrypt",
		"llvm.va_start",
		"llvm.va_end",
		"llvm.va_copy",
		"nl80211_parse_mesh_config",
		"test_and_clear_bit",
		"kfree",
	};

	for (auto F : NonSinkFN) {
		NonSinkFuncs.insert(F);
	}
}

// Setup functions that write memory.
static void SetMemWriteFuncs(
		std::map<std::string, uint8_t> &MemWriteFuncs) {

	MemWriteFuncs["memcpy"] = 0;
	MemWriteFuncs["__memcpy"] = 0;
	MemWriteFuncs["llvm.memcpy.p0i8.p0i8.i32"] = 0;
	MemWriteFuncs["llvm.memcpy.p0i8.p0i8.i64"] = 0;
	MemWriteFuncs["memmove"] = 0;
	MemWriteFuncs["llvm.memmove.p0i8.p0i8.i32"] = 0;
	MemWriteFuncs["llvm.memmove.p0i8.p0i8.i32"] = 0;
//	MemWriteFuncs["memset"] = 0;
//	MemWriteFuncs["llvm.memset.p0i8.i32"] = 0;
//	MemWriteFuncs["llvm.memset.p0i8.i64"] = 0;
	MemWriteFuncs["strncpy"] = 0;
	MemWriteFuncs["strncpy_from_user"] = 0;
    MemWriteFuncs["_strncpy_from_user"] = 0;
	MemWriteFuncs["__strncpy_from_user"] = 0;
	MemWriteFuncs["copy_from_user"] = 0;
    MemWriteFuncs["_copy_from_user"] = 0;
	MemWriteFuncs["__copy_from_user"] = 0;
	MemWriteFuncs["strcpy"] = 0;
	MemWriteFuncs["strlcpy"] = 0;
	MemWriteFuncs["strlcat"] = 0;
	MemWriteFuncs["strcat"] = 0;
	MemWriteFuncs["strncat"] = 0;
	MemWriteFuncs["bcopy"] = 1;
//	MemWriteFuncs["strsep"] = 0;
//	MemWriteFuncs["vsnprintf"] = 0;
//	MemWriteFuncs["snprintf"] = 0;
//	MemWriteFuncs["vsprintf"] = 0;
//	MemWriteFuncs["sprintf"] = 0;
//	MemWriteFuncs["vsscanf"] = 0;
//	MemWriteFuncs["sscanf"] = 0;
	MemWriteFuncs["get_user"] = 0;
    MemWriteFuncs["_get_user"] = 0;
	MemWriteFuncs["__get_user"] = 0;
}

// Setup functions that copy/move values.
static void SetCopyFuncs(
		// <src, dst, size>
		map<string, tuple<int8_t, int8_t, int8_t>> &CopyFuncs) {

	CopyFuncs["memcpy"] = make_tuple(1, 0, 2);
	CopyFuncs["__memcpy"] = make_tuple(1, 0, 2);
	CopyFuncs["llvm.memcpy.p0i8.p0i8.i32"] = make_tuple(1, 0, 2);
	CopyFuncs["llvm.memcpy.p0i8.p0i8.i64"] = make_tuple(1, 0, 2);
	CopyFuncs["strncpy"] = make_tuple(1, 0, 2);
	CopyFuncs["memmove"] = make_tuple(1, 0, 2);
	CopyFuncs["__memmove"] = make_tuple(1, 0, 2);
	CopyFuncs["llvm.memmove.p0i8.p0i8.i32"] = make_tuple(1, 0, 2);
	CopyFuncs["llvm.memmove.p0i8.p0i8.i64"] = make_tuple(1, 0, 2);
}

// Setup functions for heap allocations.
static void SetHeapAllocFuncs(
		std::set<std::string> &HeapAllocFuncs){

	std::string HeapAllocFN[] = {
		"__kmalloc",
		"__vmalloc",
		"vmalloc",
		"krealloc",
		"devm_kzalloc",
		"vzalloc",
		"malloc",
		"kmem_cache_alloc",
		"__alloc_skb",
		"kzalloc", //New added
		"kmalloc", //New added
		"kmalloc_array", //New added

	};

	for (auto F : HeapAllocFN) {
		HeapAllocFuncs.insert(F);
	}
}

#endif
