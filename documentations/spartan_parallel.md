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
### Spartan Overview
The main idea behind Spartan is to use _two sumcheck protocols_ to assert the correctness of an R1CS equation: `Az * Bz - Cz = 0`. Let `A`, `B`, `C` be circuits of size `M * N`, and subsequently `z` be a satisfying assignment of length `N`. The goal is to prove
$$
\forall_{x, y}, A(x, y)z(y) \cdot B(x, y)z(y) - C(x, y)z(y) = 0
$$

Sumcheck 1 invokes `m = log(M)` rounds to prove that given `Az`, `Bz`, `Cz` supplied by the prover, 
$$
\sum_{x\in \{0, 1\}^m} \tilde{eq}(\tau, x)(\tilde{Az}(x)\cdot \tilde{Bz}(x) - \tilde{Cz}(x)) = 0
$$
Sumcheck 1 reduces the above equation down to three claims: $v_a = \tilde{Az}(r_x)$, $v_b = \tilde{Bz}(r_x)$, $v_c = \tilde{Cz}(r_x)$. Sumcheck 2 then uses `n = log(N)` rounds to prove that `Az`, `Bz`, and `Cz` are computed correctly:
$$
r_a v_a + r_b v_b + r_c v_c = \sum_{y\in \{0, 1\}^n} (r_a\cdot \tilde{A}(r_x, y) + r_b\cdot \tilde{B}(r_x, y) + r_c\cdot \tilde{C}(r_x, y))\cdot \tilde{z}(y)
$$
where $r_a$, $r_b$, and $r_c$ are challenges provided by the verifier. Finally, prover opens $\tilde{A}(r_x, r_y)$, $\tilde{B}(r_x, r_y)$, $\tilde{C}(r_x, r_y)$, and $\tilde{z}(r_y)$ through polynomial commitment.

### Expanding Spartan to `spartan_parallel`
We expand Spartan to support `P` circuits, each with `Q_i` satisfying assignments (equivalent to `P` blocks, each executed `Q_i` times). The goal is now to prove
$$
\forall_{i, j, x, y}, A_i(x, y)z_{i, j}(y) \cdot B_i(x, y)z_{i, j}(y) - C_i(x, y)z_{i, j}(y) = 0
$$

Let `Q_max = max_i Q_i`, prover provides `Az`, `Bz`, `Cz` as $P \times Q_i \times X$ tensors. Note that they are conceptually equivalent to vectors of length $P \cdot Q_{\text{max}} \cdot X$, but the special [tensor data structure](https://github.com/Jiangkm3/spartan_parallel/blob/master/src/custom_dense_mlpoly.rs#L22) allows the prover to skip evaluations on the $Q_{\text{max}} - Q_i$ unused "zero" entries within the dense polynomial. [Sumcheck 1](https://github.com/Jiangkm3/spartan_parallel/blob/master/src/r1csproof.rs#L320) now requires `log(P) + log(Q_max) + log(X) = p + q_max + x` rounds to prove that
$$
\sum_{i\in \{0, 1\}^p, j\in \{0, 1\}^{q_\text{max}}, x\in \{0, 1\}^m} \tilde{eq}(\tau, i || j || x)(\tilde{Az}(i, j, x)\cdot \tilde{Bz}(i, j, x) - \tilde{Cz}(i, j, x)) = 0
$$
Note that to fully utilize the tensor structure and avoid the prover paying for $P\times Q_\text{max}\times X$ evaluations, this sumcheck is performed in the following order:
1. First on bits of $X$ (most significant to least significant)
2. Then on bits of $Q$ in _reverse order_ (from least significant to most significant)
3. Finally on bits of $P$ (most significant to least significant)

This is necessary because if the evaluation begins with bits of $P$ or the most significant bit of $Q$, then the $Q_{\text{max}} - Q_i$ unused entries are no longer zero in the next round. To accomodate for the reverse evaluation in $Q$, entries $\tilde{Az}$, $\tilde{Bz}$, and $\tilde{Cz}$ are also stored in reverse-bits-of-$Q$ order. This allows the final claims to be in the correct order: $v_a = \tilde{Az}(r_i, r_j, r_x)$, $v_b = \tilde{Bz}(r_i, r_j, r_x)$, $v_c = \tilde{Cz}(r_i, r_j, r_x)$. 


[Sumcheck 2](https://github.com/Jiangkm3/spartan_parallel/blob/master/src/r1csproof.rs#L462) now requires `log(P) + log(Y) = p + y` rounds to check `Az`, `Bz`, and `Cz` for every `A`, `B`, and `C`. To do so, the prover first computes $\tilde{z}_{r_j}(i, y) = \tilde{z}(i, r_j, y)$, then proves:
$$
r_a v_a + r_b v_b + r_c v_c = \sum_{i\in \{0, 1\}^p, y\in \{0, 1\}^n} \tilde{eq}(r_i, i)\cdot (r_a\cdot \tilde{A}(i, y) + r_b\cdot \tilde{B}(i, y) + r_c\cdot \tilde{C}(i, y))\cdot \tilde{z}_{r_j}(i, y)
$$
Note that we cannot directly evaluate $\tilde{A}(r_p, y)$, etc. as that results in the equation becoming quadratic in terms of $r_p$. Thus an additional `p` rounds are introduced to flatten $r_p$. This introduces `p` new challenges. We denote the challenges generated in sumcheck 2 ($r_i', r_y$).

Finally, prover opens $\tilde{A}(r_i', r_x, r_y)$, $\tilde{B}(r_i', r_x, r_y)$, $\tilde{C}(r_i', r_x, r_y)$, and $\tilde{z}(r_i', r_j, r_y)$ through polynomial commitment.

## Batched Commitments
Spartan currently uses Hyrax for polynomial commitment, which is easily data-parallelizable. `spartan_parallel` commits to each circuit separately (but in batch), and commits witnesses by the type of circuit (block) they are being applied to. This allows the size and number of execution of each block to be different, but at the cost of having commitment size linear to number of circuits (blocks). Thus it is of top priority to try to reduce the number of blocks emitted.