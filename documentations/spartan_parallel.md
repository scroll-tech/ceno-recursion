# Spartan Parallel

## Overview
`spartan_parallel` takes in circuits and witnesses of the blocks produced by `circ_blocks`, and generates and verifies a SNARK proof on the correct execution of the program code. One can treat `spartan_parallel` as a two-step process: first it emits 5 different (groups of, should really be number of blocks + 4) circuits based on the blocks and an execution trace, then it evokes a data-parallel proving process on those 5 circuits.

## High-Level Idea
The program is executed correctly iff all of the following holds:
1. All blocks of the program are executed correctly
2. All registers (including the label of the next block) are passed correctly between blocks.
3. The memory state (read-only and RAM) stays coherent throughout the execution.

Statement 1 can be checked directly through the block-specific circuits emitted by `circ_blocks`, while statement 2 and 3 can be checked by "extracting" inputs, outputs, and memory accesses out of block witnesses and check that they are pairwise consistent. `spartan_parallel` achieves so by generating "extraction circuits" and "consistency check circuits" based on compile-time metadata (number of inputs, outputs, and number of memory accesses per block). Furthermore, all three statements require witnesses to be arranged in different orders (statement 1 by block type, statement 2 by execution time, statement 3 by memory address), `spartan_parallel` inserts "permutation circuits" to verify the permutation between all three ordering: construct three univariate polynomials and test their equivalence by evaluating on a random point. [Let me know if this does not make sense!]

Please refer to [instance.rs](https://github.com/Jiangkm3/spartan_parallel/blob/master/src/instance.rs) for details of the circuits.

## Inputs and Circuit Generation
At preprocessing stage, `spartan_parallel` reads in the following [inputs](https://github.com/Jiangkm3/spartan_parallel/blob/master/examples/interface.rs#L45):
- Circuits of each basic block
- Number of inputs, outputs, and memory operations of each block, as well as where these values are stored within the witnesses.
- Max number of registers that need to be passed from one block to another
- Max number of read-only memory accesses within a block
- Max number of RAM accesses within a block

Through the above inputs, `spartan_parallel` emits the following circuits during the preprocessing stage:
1. `BLOCK_CORRECTNESS` ([link](https://github.com/Jiangkm3/spartan_parallel/blob/master/src/instance.rs#L246)): verifies the correct execution of every block and "extracts" (constructs the polynomials) inputs, outputs, and all memory values out of each block.
2. `CONSIS_CHECK` ([link](https://github.com/Jiangkm3/spartan_parallel/blob/master/src/instance.rs#L545)): checks that when sorted in execution order, the output of the previous block matches with the input of the next block. This is performed similarly to an offline memory check.
3. `PHY_MEM_COHERE` ([link](https://github.com/Jiangkm3/spartan_parallel/blob/master/src/instance.rs#L545)): checks that the read-only memory accesses are coherent via an offline memory check.
4. `VIR_MEM_COHERE` ([link](https://github.com/Jiangkm3/spartan_parallel/blob/master/src/instance.rs#L545)): checks that all RAM accesses are coherent via an offline memory check.
5. `PERM_ROOT` ([link](https://github.com/Jiangkm3/spartan_parallel/blob/master/src/instance.rs#L761)): performs permutation check by constructing the polynomials of inputs and memory entries in execution / address order (block type order is handled in `BLOCK CORRECTNESS`)

## Verify Sumcheck in Parallel
The main idea behind Spartan is to use _two sumcheck protocols_ to assert the correctness of an R1CS equation: `Az * Bz - Cz = 0`. Let `A`, `B`, `C` be circuits of size `x * y`, and subsequently `z` be a satisfying assignment of length `y`. Sumcheck 1 invokes `log(x)` rounds to prove that given `Az`, `Bz`, `Cz` supplied by the prover, the equation `Az * Bz - Cz = 0` holds. Sumcheck 2 then uses `log(y)` rounds to prove that `Az`, `Bz`, and `Cz` are computed correctly. 

We expand Spartan to support `p` circuits, each with `q_i` satisfying assignments (equivalent to `p` blocks, each executed `q_i` times). Let `q_max = max_i q_i`, [sumcheck 1](https://github.com/Jiangkm3/spartan_parallel/blob/master/src/r1csproof.rs#L320) now requires `log(p) + log(q_max) + log(x)` rounds to prove every row of every circuit evaluates to 0, and [sumcheck 2](https://github.com/Jiangkm3/spartan_parallel/blob/master/src/r1csproof.rs#L462) now requires `log(p) + log(y)` rounds to check `Az`, `Bz`, and `Cz` for every `A`, `B`, and `C`. (Note: sumcheck 2 requires another `log(p)` rounds because `p` is a parameter to both the number of circuits and the number of witnesses. Without the extra `log(p)` rounds for flattening, the multiplication would be quadratic to `p`). The above protocol translates to `O(log(p) + 2 * log(q_max) + log(x))` work for the verifier. To bound prover work to `sum_i q_i` (as opposed to `p * q_i`), we use special [data structure](https://github.com/Jiangkm3/spartan_parallel/blob/master/src/custom_dense_mlpoly.rs#L22) to skip the unused "zero" entries within the dense polynomial.

## Batched Commitments
Spartan currently uses Hyrax for polynomial commitment, which is easily data-parallelizable. `spartan_parallel` commits to each circuit separately (but in batch), and commits witnesses by the type of circuit (block) they are being applied to. This allows the size and number of execution of each block to be different, but at the cost of having commitment size linear to number of circuits (blocks). Thus it is of top priority to try to reduce the number of blocks emitted.