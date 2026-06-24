# haloumi-llzk

This crate is the Haloumi backend for generating [LLZK](https://project-llzk.github.io/llzk-lib/main/). LLZK is a family of 
[MLIR](https://mlir.llvm.org/) dialects designed specifically for ZK use cases.

The backend generates IR that represents the constraint system of the circuit that can be used with tools compatible with LLZK,
and lowered further to other targets that are compatible with the IR.
