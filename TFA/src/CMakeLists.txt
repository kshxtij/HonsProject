cmake_minimum_required(VERSION 3.5.1)
project(ANALYZER)

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

# Set your project compile flags.
# E.g. if using the C++ header files
# you will need to enable C++14 support
# for your compiler.
# Check for C++14 support and set the compilation flag
include(CheckCXXCompilerFlag)
#CHECK_CXX_COMPILER_FLAG("-std=c++14" COMPILER_SUPPORTS_CXX14)
#if(COMPILER_SUPPORTS_CXX14)
#	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++14 -fno-rtti -fPIC -Wall")
#else()
#	message(STATUS "The compiler ${CMAKE_CXX_COMPILER} has no C++14 support. Please use a different C++ compiler.")
#endif()

set(OMP_INCLUDE_DRIS "/usr/lib/llvm-10/include/openmp")
set(OMP_LIB_DRIS "/usr/lib/llvm-10/lib")

include_directories(${LLVM_INCLUDE_DIRS})
# include_directories(${MYSQL_INCLUDE_DIRS})

include_directories(${OMP_INCLUDE_DRIS})
link_directories(${OMP_LIB_DRIS})
link_libraries(${OMP_LIB_DRIS})

message("OPENMP: ${OMP_INCLUDE_DRIS}")

add_definitions(${LLVM_DEFINITIONS})

add_subdirectory(lib)

