#!/bin/bash
set -e -x

ROOT=$(pwd)

sudo apt update
sudo apt install -y flex bison clang libelf-dev libssl-dev lld python3-pip cmake zip

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
KERNEL_VERSION=$1
echo "Valid kernel version detected: $KERNEL_VERSION"


echo "Cloning latest commit on branch $KERNEL_VERSION"
if [ -d "kernels/linux-$KERNEL_VERSION" ]; then
  echo "Kernel directory already exists"
  echo "Skipping cloning"
else
  echo "Cloning kernel"
  git clone --depth 1 --branch $KERNEL_VERSION https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git kernels/linux-$KERNEL_VERSION
fi
KERNEL_LOCATION=kernels/linux-$KERNEL_VERSION

# Check if llvm-project directory exists
if [ ! -d "$ROOT/llvm-project" ]; then
	echo "Cloning LLVM"
	git clone https://github.com/llvm/llvm-project
	cd llvm-project
	git checkout e758b77161a7
	cd ..
fi
LLVM_LOCATION=llvm-project

# if llvm-project/prefix/bin/clang does not exist, build LLVM
if [ ! -f "$ROOT/llvm-project/prefix/bin/clang" ]; then
  echo "Building LLVM"
  cd $LLVM_LOCATION

  mkdir -p build
  cd build

  cmake -DLLVM_TARGET_ARCH="X86" -DLLVM_TARGETS_TO_BUILD="ARM;X86;AArch64" -DLLVM_EXPERIMENTAL_TARGETS_TO_BUILD=WebAssembly -DCMAKE_BUILD_TYPE=Release -DLLVM_ENABLE_PROJECTS="clang;lldb" -G "Unix Makefiles" ../llvm

  make -j$(nproc)

  if [ ! -d "$ROOT/llvm-project/prefix" ]; then
    mkdir $ROOT/llvm-project/prefix
  fi

  cmake -DCMAKE_INSTALL_PREFIX=$ROOT/llvm-project/prefix -P cmake_install.cmake

  echo "LLVM built and installed"
fi
CLANG_BIN=$ROOT/llvm-project/prefix/bin/clang

if [ ! -f "$ROOT/IRDumper/build/lib/libDumper.so" ]; then
  echo "Building Bitcode Dumping Tool"
  cd $ROOT/IRDumper
  make clean
  make
fi
DUMPER_LOCATION=$ROOT/IRDumper/build
IRDUMPER=$DUMPER_LOCATION/lib/libDumper.so

build () {
  cd $ROOT

  CONFIG_NAME=$1
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
  find . -name '*.bc' -delete

  make $CONFIG_NAME
  echo "1" | make CC=$CLANG_BIN CFLAGS_KERNEL="-Wno-everything" -j$(nproc) -k -i

  echo "Kernel built with IR Dumper"

  echo "Restoring Makefile"
  cp Makefile.bak Makefile
  rm Makefile.bak

  echo $(find . -name "*.bc" | wc -l) "LLVM bitcode files generated"

  mkdir $ROOT/bitcode/$KERNEL_VERSION-$CONFIG_NAME
  find . -name '*.bc' | cpio -pdVmu $ROOT/bitcode/$KERNEL_VERSION-$CONFIG_NAME/
  echo "Bitcode files copied to $ROOT/bitcode/$KERNEL_VERSION-$CONFIG_NAME"
  return 0
}

build "allyesconfig"
echo "Done building allyesconfig"

build "defconfig"
echo "Done building defconfig"

echo "Done"
exit 0