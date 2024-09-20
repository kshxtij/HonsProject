### Linux Kernel Static Analyser

## Usage


```sh
./run.sh v6.11 defconfig
```

`run.sh` is designed to setup the environment on a fresh machine and install/clone all required packages. The scripts are currently agnostic to linux version and configuration (passed as command line arguments to the script) however the llvm commit is pinned due to the deprecation of the legacy pass manager and out of tree passes.

