# Merge and Split Basic Blocks

Below are collections of random thoughts on splitting & merging basic blocks, with the eventual hope of drafting a functioning system & report

## Motivation

The motivation for merging & splitting basic blocks originates from the observation that length of basic block varies. However, the backend requires the size of the instance for each block to be fixed. Since the runtime of the sumcheck protocol is proportional to the size of the largest instance, any gap between block size & instance size constitutes a "waste" in computation. There are two ways to reduce this gap:
1. Splitting basic blocks: Split the largest blocks into multiple chunks, reducing the size of the largest instance. This is the unpreferred method since the addition of each block adds a new transition state and thus adds to the cost of consistency check & permutation. Furthermore, splitting a block might result in previously intermediate witnesses being added to transition states, further add to cost of consistency & permutation.
2. Merging basic blocks: Merge smaller blocks to increase their size. This is the more difficult approach but is more effective. If done correctly, block merges can reduce the number of transition states without modifying the contents within each one. However, merging basic blocks requires knowledge on structure and potentially semantics of the whole program.

## Merging Basic Blocks
Due to the reasons listed above, we first focus on basic block merges.

### Preliminaries & Assumptions
We base the investigation on a few assumptions:
1. The number of constraints corresponding to each block can be easily obtained. At worst case we translate blocks into constraints and count, so this assumption is reasonable.
2. The program has limited structure: i.e., no pointer, jumps, or recursion. This assumption is already employed by other analyses.

### Where should we do the analysis?
The most natural placement should be after every analyses that perform scans within blocks, since after merging we no longer have traditional basic blocks. One solution is to do it after liveness & before spilling & DBE.

### Guidelines on Block Merging
A set of blocks can only be merged if:
1. In forward direction, there exists a block in the set that dominates all other blocks
2. In reverse direction, there exists a block in the set that dominates all other blocks
3. The two dominators must be in the same scope
4. What about function returns? (Returns within a different scope)
5. It seems like a new liveness / alias analysis needs to be performed after block merge?
6. What is left is how to correctly estimate the number of constraints after each merge
7. What about partial unroll of loops? Inline function calls?

### Observations
1. Every time an execution enters from scope 1 to scope 2, it will either exit the function before reaching scope 1, or always exits back to the same block in scope 1
2. Thus, if we were to merge blocks starting from a specific block, there is either one way to do it, or no way at all
3. Block merges do not increase the number of transition states / memory operations, so we only need to consider the number of constraints in the block itself