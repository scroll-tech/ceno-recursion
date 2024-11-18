# CirC Blocks
This document covers the basics of `circ_blocks` as well as how to use it.

## Overview
`circ_blocks` converts a program code of a high-level language into circuits used by SNARK codes. In particular, it performs the following conversion:
```
ZoKrates -> Basic Blocks -> Optimized Blocks -> CirC IR -> R1CS
```

## Basic Blocks
`circ_blocks` takes in ZoKrates as its front-end language. See `zok_format` for detailed format of ZoKrates. The first [transformation](https://github.com/Jiangkm3/circ_blocks/blob/master/src/front/zsharp/blocks.rs#L568) converts zok programs into [blocks](https://github.com/Jiangkm3/circ_blocks/blob/master/src/front/zsharp/blocks.rs#L219) strictly following its control flow. As such, one should expect the emitted blocks to be the exact basic blocks of the program.

## Optimizing Blocks
To emit more efficient constraints, `circ_blocks` performs the following [optimizations](https://github.com/Jiangkm3/circ_blocks/blob/master/src/front/zsharp/blocks_optimization.rs#L1656) upon the basic blocks:
- Liveness Analysis / Dead Code Elimination
- Function Merge
- Block Merge
- Spilling
- Register Allocation
- Memory Allocation

See [writeups](https://github.com/Jiangkm3/circ_blocks/blob/master/writeups) of `circ_blocks` for details of some of the implementations.

## Lowering Blocks into Circuits
`circ_blocks` repackages each block as standalone programs and lowers them into CirC IR and R1CS through the same functionality as CirC. See [bls_to_circ](https://github.com/Jiangkm3/circ_blocks/blob/master/src/front/zsharp/blocks.rs#L2173).

## Interpreting Blocks
The Prover generates witnesses through an [interpreter](https://github.com/Jiangkm3/circ_blocks/blob/master/src/front/zsharp/prover.rs#L200). It executes the program through the trace of blocks and records all intermediate program states. It terminates the interpretation once it reaches the exit block, or encounters an unsatisfiable assertion.

## Running `circ_blocks`
Build and run `circ_blocks` by:
1. Navigate to `circ_blocks`
2. Run `cargo build --release --example zxc --no-default-features --features r1cs,smt,zok` to build
3. Run `target/release/examples/zxc <flags> <benchmark>`
  - For ceno, use `ceno_demo/tower_verifier` for benchmark
  - Flags include:
    * `--no_opt`: disables most of the block optimizations
    * `--verbose_opt`: emits new blocks after each optimization pass
    * `--inline_spartan`: verifies ciruits automatically using `spartan_parallel`

### Output Format
`circ_blocks` prints out block representation of the program, where
- without `--verbose_opt`, it prints out all basic blocks of the program and all optimized blocks
- with `--verbose_opt`, it prints out all blocks after each optimization pass

A block is of the following format:
```
Block 5:  <-- block label
Func: main, Scope: 2  <-- the function and scope of the block (for optimization)
Exec Bound: 1600, While Loop: false  <-- static upper bound on number of executions (to estimate circuit size)
RO Ops: 0, VM Ops: 2  <-- number of memory operations within the block (read-only and RAM)
Num Cons: 190  <-- estimated number of constraints
Inputs:
    %i1(BN): field  <-- block inputs
    %i3(TS): field      should match outputs of the previous block
    %i7: field
    %i8: u32
    ...
Outputs:
    %o1(BN): field  <-- block outputs
    %o3(TS): field      should match inputs of the next block
    %o7: field
    %o8: u32
    ...
Instructions:
    assert %i1(BN) == 5 <Field>
    field %w1(TS) = %i3(TS)
    field %w12 = %i7
    u32 %w7 = %i8  <-- instructions:
    u32 %w8 = %i9      assertion, assignment, conditional, and mem_ops
    ...
    if %w5 < %w19 && %w19 < %w8 && %w20 < %w17:
        u32 %w21 = %w12[%w19]
        %w17 = %w21
        %w18 = %w19
    else:
        Dummy Load
    ...
    field %o1(BN) = %w19 != 1600 <U32> ? 5 <Field> : 6 <Field>
Transition:
    %w19 != 1600 <U32> ? -> 5 : -> 6  <-- transition marks the label of the next block
```