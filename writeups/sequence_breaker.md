# Sequence Breaker Analysis

## Overview
This document depicts ideas for a compiler pass, which reorganizes the entire block structure of a CFG disregarding any data dependency. The goal of which is to minimize the number of blocks and registers used within the computation, assuming that the value of every intermediate computation can be obtained through (untrusted) oracle accesses. We expect the compiler pass to reorder existing blocks, group all loops of similar number of iterations together, and automatically deduce and insert all oracle accesses. We expect such an analysis to be a major speed up for CoBBl.

## Motivation

### Block Number Reduction
CoBBl is a compiler that generates SNARK circuits, which are used to verify the correct execution of a program in sublinear time. To achieve optimal runtime, CoBBl breaks down a program into a sequence of blocks according to its control flow, converts each block into circuits, and sets up a proof system that can verify all blocks in parallel.

The block-based nature of CoBBl requires most (if not all) proof systems based on CoBBl to incur some form of runtime linear to the number of blocks, including but not limited to:
* Commitment of circuits are performed per block. This implies that both circuit commitment (by the prover) and opening (by the verifier) are linear to the number of blocks.
* Similarly, commitment of witnesses are also done by block, so witness commitment and opening are also linear to the number of blocks.

In our current Hyrax-based commitment scheme, commits and openings dominate the cost of both the prover and the verifier, making the number of blocks an even more crucial factor on proof performance.

### Trace Size Reduction
Fewer unique blocks often corresponds to fewer number of _total blocks_ executed by the prover. This leads to fewer consistency checks in-between executed blocks, fewer transition registers, and a smaller permutation check. These reductions can often lead to substantial improvements in proof performance.

### Register Number Reduction
Apart from the reduction of transition registers in-between blocks, block merges can also eliminate registers and computations within the blocks. For instance, if we merge two loops into a single loop (see example below), then we avoid keeping track of two iterators. These small improvements can make a difference over time.

## Details
We introduce the sequence breaker through an example. In this example, we generate a random hash sequence, and use it to achieve some transformation.
```rust
fn main(u32 len, u32 init) -> field:
    // Generate a hash sequence
    array_decl u32[len] hash_seq
    hash_seq[0] = 0
    // LOOP 1
    for u32 i1 in 1..len {
        hash_seq[i1] = hash(hash_seq[i1 - 1])
    }
    // Perform some transformation using the hash
    // LOOP 2
    for u32 i2 in 0..len {
        init = transform(init, hash_seq)
    }
    return init
```
Traditional compilers cannot combine `LOOP 1` and `LOOP 2` into a single loop with `len` iterations, as contents in `LOOP 2` may require the entirety of `hash_seq`, which is only computed after the entirety of `LOOP 1`. In a SNARK context, however, such loop combination is feasible, since all entries of `hash_seq` are already known before hand. Thus the sequence breaker analysis can convert the program into:
```rust
fn main(u32 len, u32 init, u32[len] hash_seq) -> field:
    // LOOP 1 & 2
    for u32 i in 0..len {
        assert_eq!(hash_seq[i], i == 0 ? 0 : hash(hash_seq[i - 1]))
        init = transform(init, hash_seq)
    }
    return init
```
where `hash_seq` is supplied by the prover as witnesses.

We note that the original code needs to be expressed using at least 5 blocks (2 for instructions of the two loop, 3 for instructions before, between, and after the loops), the optimized code only needs 2 (1 for the loop, 1 for the return). We also note that the optimized code eliminates the iterator `i2`, although it does introduce additional constraints through the ternary.

## Preliminary Results
Currently all sequence breaking analyses are performed by hand. It is unclear whether there exist any similar implementations (due to its peculiar application) or what extent we can push on the automation process. Existing empirical evidence suggests up to ~75% reduction in compiler and prover time for complex programs.

## Other Potential Uses of the Analysis
Sequence breaker analyses are particularly useful for block-based SNARK systems (as far as we know, CoBBl is the only one). It might be applicable to certain SAT / SMT solving problems, although it is unclear whether the analyses would achieve any substantial speedup. Apart from the above, such analysis seems only useful on computers where registers and memory can time travel to the past.