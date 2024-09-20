#!/bin/bash
set -e -x

ROOT=$(pwd)

# sudo apt update
# sudo apt install -y flex bison clang libelf-dev libssl-dev lld python3-pip cmake

# Check argument 1
if [ -z "$1" ]; then
  echo "Usage: $0 <kernel_version> <config_name>"
  exit 1
fi

# Check if argument is a valid kernel version
if ! echo "$1" | grep -qP 'v\d+\.\d+'; then
  echo "Invalid kernel version: $1"
  exit 1
fi

echo "Valid kernel version detected: $1"

echo "Cloning latest commit on branch $1"

# git clone --depth 1 --branch $1 https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git kernels/linux-$1
KERNEL_LOCATION=kernels/linux-$1

# Check if llvm-project directory exists
if [ ! -d "$ROOT/llvm-project" ]; then
	echo "Cloning LLVM"
	git clone https://github.com/llvm/llvm-project
	cd llvm-project
	git checkout e758b77161a7
	cd ..
fi
LLVM_LOCATION=llvm-project

echo "Building LLVM"
cd $LLVM_LOCATION

mkdir -p build
cd build

# cmake -DLLVM_TARGET_ARCH="X86" -DLLVM_TARGETS_TO_BUILD="ARM;X86;AArch64" -DLLVM_EXPERIMENTAL_TARGETS_TO_BUILD=WebAssembly -DCMAKE_BUILD_TYPE=Release -DLLVM_ENABLE_PROJECTS="clang;lldb" -G "Unix Makefiles" ../llvm

# make -j$(nproc)

if [ ! -d "$ROOT/llvm-project/prefix" ]; then
  mkdir $ROOT/llvm-project/prefix
fi

# cmake -DCMAKE_INSTALL_PREFIX=$ROOT/llvm-project/prefix -P cmake_install.cmake

echo "LLVM built and installed"

echo "Building Bitcode Dumping Tool"
cd $ROOT/IRDumper
# make clean
# make

DUMPER_LOCATION=$ROOT/IRDumper/build
IRDUMPER=$DUMPER_LOCATION/lib/libDumper.so
cd $ROOT

CLANG_BIN=$ROOT/llvm-project/prefix/bin/clang

# Check argument 2
if [ -z "$2" ]; then
  echo "Usage: $0 <kernel_version> <config_name>"
  exit 1
fi

# Check if argument is either defconfig or allyesconfig
if [ "$2" != "defconfig" ] && [ "$2" != "allyesconfig" ]; then
  echo "Invalid config name: $2"
  exit 1
fi
CONFIG_NAME=$2

echo "Valid config name detected: $2"

NEW_CMD="\n\n\
KBUILD_USERCFLAGS += -Wno-everything -Wno-address-of-packed-member -g -Xclang -no-opaque-pointers -Xclang -flegacy-pass-manager -Xclang -load -Xclang $IRDUMPER\nKBUILD_CFLAGS += -Wno-everything -g -Wno-address-of-packed-member -Xclang -no-opaque-pointers -Xclang -flegacy-pass-manager -Xclang -load -Xclang $IRDUMPER"

if [ ! -f "$KERNEL_LOCATION/Makefile.bak" ]; then
	cp $KERNEL_LOCATION/Makefile $KERNEL_LOCATION/Makefile.bak
	echo "Backed up Makefile"
fi

echo -e $NEW_CMD >$KERNEL_LOCATION/IRDumper.cmd
cat $KERNEL_LOCATION/Makefile.bak $KERNEL_LOCATION/IRDumper.cmd >$KERNEL_LOCATION/Makefile

cd $KERNEL_LOCATION

echo "Clearing old build"
make clean

make $CONFIG_NAME
echo "1" | make CC=$CLANG_BIN CFLAGS_KERNEL="-Wno-everything" -j$(nproc) -k -i

echo "Kernel built with IR Dumper"

cd $ROOT

echo "Restoring Makefile"
cp $KERNEL_LOCATION/Makefile.bak $KERNEL_LOCATION/Makefile
rm $KERNEL_LOCATION/Makefile.bak

echo $(find $KERNEL_LOCATION -name "*.bc" | wc -l) "LLVM bitcode files generated"

echo "Done"
