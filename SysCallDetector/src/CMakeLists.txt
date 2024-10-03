cmake_minimum_required(VERSION 3.5.1)
project(SysCallDetector)

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

# Set your project compile flags.
# E.g. if using the C++ header files
# you will need to enable C++14 support
# for your compiler.
# Check for C++14 support and set the compilation flag
include(CheckCXXCompilerFlag)

# set(OMP_INCLUDE_DRIS "/usr/lib/llvm-14/include/openmp")
# set(OMP_LIB_DRIS "/usr/lib/llvm-14/lib")

# include_directories(${OMP_INCLUDE_DRIS})
include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})

add_subdirectory (lib)
