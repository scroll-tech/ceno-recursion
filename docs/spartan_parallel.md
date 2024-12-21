# Spartan Parallel

## Overview
`spartan_parallel` takes in circuits and witnesses of the blocks produced by `circ_blocks`, and generates and verifies a SNARK proof on the correct execution of the program code. The process of `spartan_parallel` can be divided into the following stages:
- (Compile Time) Circuit preprocessing and commitment
- (Runtime) Witness preprocessing and commitment
- (Runtime) Sumcheck on all circuits and all instances
- (Runtime) Opening on circuit and witness commitments
- (Runtime) Shift and program IO proofs

## High-Level Idea
The program is executed correctly iff all of the following holds:
1. All blocks of the program are executed correctly
2. All registers (including the label of the next block) are passed correctly between blocks.
3. The memory state (read-only and RAM) stays coherent throughout the execution.

Statement 1 can be checked directly through the block-specific circuits emitted by `circ_blocks`, while statement 2 and 3 can be checked by "extracting" inputs, outputs, and memory accesses out of block witnesses and check that they are pairwise consistent. `spartan_parallel` achieves so by generating "extraction circuits" and "consistency check circuits" based on compile-time metadata (number of inputs, outputs, and number of memory accesses per block). Furthermore, all three statements require witnesses to be arranged in different orders (statement 1 by block type, statement 2 by execution time, statement 3 by memory address), `spartan_parallel` inserts "permutation circuits" to verify the permutation between all three ordering: construct three univariate polynomials and test their equivalence by evaluating on a random point. However, to ensure that the same set of witnesses are used by both block correctness check and permutation check, the prover needs to use the same commitment for both proofs. To prevent excessive commitment opening, `spartan_parallel` commits the overlapping witnesses of block correctness and permutation separately.

## Instance Preprocessing and Commitment (Compile Time)
Relevant files: `examples/interface.rs`, `src/instance.rs`, and `src/r1csinstance.rs`

### Inputs from `circ_blocks`
Relevant struct: `CompileTimeKnowledge` in `examples/interface.rs`

At compile time, `spartan_parallel` reads in from `circ_blocks` through the struct `CompileTimeKnowledge`, including the R1CS circuit for each block (`args`) and all relevant metadata (number of inputs, witnesses, memory operations, etc. per block).

The circuit of each block $\mathcal{C}_i = (A, B, C)_i$ is designed to be satisfied by a witness $z_i$ of the following form:
$$
z_i = i_i || o_i || p_i || v_i || w_i
$$
where
* $i_i$ and $o_i$ are the inputs and outputs of the block, and should match with the outputs and inputs of the previous and next block. $i_i$ and $o_i$ also contain the block label for the current and next block to check that the prover always executes the correct block.
* $p_i$ records all stack accesses of the block through a list of $(addr_j, data_j)$. All $(addr_j, data_j)$ of all blocks are used to verify the coherence of a write-once memory. 
* $v_i$ records all heap accesses of the block through a list of $(addr_j, data_j, ts_j, ls_j)$. All entries of all blocks are used to verify the coherence of a regular (write-many) memory. 
* $w_i$ contains all other intermediate computations used by the block.

### Expanding and Generating Circuits
Relevant struct: `Instance` in `src/instance.rs`

A prover of `spartan_parallel` needs to show the following:
1. For every block $i$, the witness generated from every execution $j$ of that block $z_{i, j}$ satisfies $\mathcal{C}_i$. (_block correctness_)
2. After permutating $(i_{i, j}, o_{i, j})$ into execution order $(i'_k, o'_k)$, we have $i'_k = o'_{k-1}$ for all $k \neq 0$. (_consistency_)
3. After permutating $p_{i, j} = \{(addr_{i, j, 0}, data_{i, j, 0}), (addr_{i, j, 1}, data_{i, j, 1}), \dots\}$ by address into $p'_k = (addr'_k, data'_k)$, $p'_k$ satisfies (_physical mem coherence_)
$$addr'_{k - 1} + 1 = addr'_k \vee (addr'_{k - 1} = addr'_k \wedge val'_{k - 1} = val'_k)$$
4. After permutating $v_{i, j}$ into $v'_k$, $v'_k$ satisfies memory coherence (_virtual mem coherence_)

We note that the above steps imply the following additional procedures:

5. Every $(i_{i, j}, o_{i, j}, p_{i, j}, v_{i, j})$ is correctly extracted from $z_{i, j}$
6. The sets of $\{i_{i, j}, o_{i, j}\}$, $\{p_{i, j}\}$, $\{v_{i, j}\}$ are permutations of $\{i'_k, o'_k\}$, $\{p'_k\}$, and $\{v'_k\}$

Permutations are checked via univariate polynomial evaluations. Thus step 6 can be further divided into

* (6a) $RLC_{i, o} = \prod_{i, j} (\tau - f(i_{i, j}) - r\cdot f(o_{i, j}))$, where $\tau$ and $r$ are random numbers and $f$ is a random linear combination (see consistency below). Compute $RLC_p$, $RLC_v$ as well.
* (6b) $RLC'_{i, o} = \prod_k (\tau - f(i'_k) - r\cdot f(o'_k))$. Compute $RLC'_p$, $RLC'_v$ as well.
* (6c) Assert that $RLC_{i, o} = RLC'_{i, o}$, $RLC_p = RLC'_p$, $RLC_v = RLC'_v$.

While the prover has computed $f(i'_k)$ and $f(o'_k)$ during permutation, it can use them for consistency check. We can rewrite _consistency_ as:

2. $f(i'_k) = f(o'_{k-1})$ for all $k \neq 0$. (_consistency_)

_Remark_: $(i'_k, o'_k)$, $p'_k$, and $v'_k$ will be padded with 0 to the next power of 2, so consistency and coherence checks will have additional constraints to handle these 0 entries.

We can now generate all the circuits we need:

*  A set of circuits ($\mathcal{C}'_i$) that checks step 1, 5, and 6a for each block $i$. These circuits are modified from $\mathcal{C}_i$ to add the rlc function $f$ and polynomial evaluation. As a result, its satisfying assignments $z'_{i, j}$ also requires modification from $z_{i, j}$, to the following form:
$$z'_{i, j} = (z_{i, j}, r, rz_{i, j}, \pi_{i, j}, \pi'_{i, j})$$
- where
  - $r$ is the randomness used by $f$ and $\tau$
  - $rz_{i, j}$ records intermediate computations for $\tau - f(i_{i, j}) - r\cdot f(o_{i, j})$, $\tau - f(p_{i, j})$, and $\tau - f(v_{i, j})$
  - $\pi_{i, j}$ stores $\tau - f(i_{i, j}) - r\cdot f(o_{i, j})$, $\tau - f(p_{i, j})$, and $\tau - f(v_{i, j})$, as well as their cumulative product that forms $RLC_{i, o}$, $RLC_p$, $RLC_v$.
  - $\pi'_{i, j}$ is a shifted version of $\pi_{i, j}$, used to help compute the cumulative product. See _shift proofs_ section.
- To allow for each segment of $z'_{i, j}$ to be committed separately, `spartan_parallel` _conceptually_ pads each segment with 0's to the same length as $z_{i, j}$. Note that these pads are never materialized and can be skipped during actual computation. Since $z'_{i, j}$ also needs to be padded to a power of 2, this implies $|z'_{i, j}| = 8 \times |z_{i, j}|$ 

* A consistency circuit $\mathcal{C}_c$ for step 2 ($f(i'_k) = f(o'_{k-1})$).
* Stack and heap verification circuits $\mathcal{C}_p$, $\mathcal{C}_v$ for step 3 and 4.
* A permutation circuit $\mathcal{C}_\pi$ for step 6b.

Note that the verifier can check 6c efficiently without sumcheck.
Also, $\mathcal{C}'_i$ are the larger circuits while $\mathcal{C}_c$, $\mathcal{C}_p$, $\mathcal{C}_v$, $\mathcal{C}_\pi$ are small and easily parallelizable.

### Committing Circuits through Sparse Poly Commitment
Relevant functions:
* `next_group_size` in `src/instance.rs`
* `gen_block_inst` in `src/instance.rs`
* `SNARK::multi_encode` in `src/lib.rs`
* `R1CSInstance::multi_commit` in `src/r1csinstance.rs`
* `R1CSInstance::multi_evaluate` in `src/r1csinstance.rs`

The previous steps generate in total $b + 4$ circuits of various sizes. Our circuit commitment follows the existing batched sparse polynomial commitment scheme of Spartan. However, with circuits of different sizes, we want to only pay proportional to the approximate size of each circuit. The solution is to divide circuits of different sizes into groups and commit each groups separately.

Let each circuit $\mathcal{C}_i$ be of size $M_i\times N_i$ with $L_i$ non-zero entries. We assume that $M_i$ and $N_i$ are of similar sizes and $N_i$, and $L_i$ are roughly proportional to each other. 
For each commitment, the prover pays for $O(L)$ time to generate a proof of size $O(\log(N) + \log(L))$.

Our strategy is thus to group the circuits by the size of $N_i$. For each circuit $i$, the prover rounds its $N_i$ to the nearest power of 16 (or some other adjustable value) and put it in the corresponding group. For each group $j$, the prover computes the maximum $M_j$, $N_j$ and $L_j$ within the group, and batch commits every circuit of that group as $M_j \times N_j$ with $L_j$ non-zero entries.

There is, however, a problem with this approach with regard to the modified block circuits $\mathcal{C}'_i$. Recall that each $\mathcal{C}'_i$ matches with an assignment $z'_{i, j}$ of 5 segments: 
$$z'_{i, j} = (z_{i, j}, r, rz_{i, j}, \pi_{i, j}, \pi'_{i, j})$$
each segment padded to the length of the block witness $|z_{i, j}|$. To perform the same sumcheck across all blocks, the size of all circuits needs to be _conceptually_ equivalent. (e,g, let $z_\text{max} = \max_{i, j} |z_{i, j}|$, for every block, the first variable of $r$ is always the $z_\text{max}$'th entry, the first variable of $rz_{i, j}$ is always the $2\times z_\text{max}$'th entry, etc.). However, for blocks of a different size, the padding size is different, and thus the first variable of $r$ will not be the same entry.

The solution is for the prover to keep two versions of each block circuit (toggled by `COMMIT_MODE` in `gen_block_inst`). In the _sumcheck version_, every circuit is of the same $M_{\text{max}} = \max{M}$ and $N_{\text{max}} = \max{N}$. In the _commit version_, every circuit has $M$ and $N$ according to their group. Note that the prover's time and space cost to process a circuit is linear to their number of non-zero entries, which is the same for both versions. The prover can thus use the sumcheck version to perform the sumcheck of all blocks together, and use the commit version to reduce the time size of the commitment.

The discrepancy between the two versions requires additional handling of commitment opening. The sumcheck produces two lists of challenges corresponding to the two dimensions of the circuit: $|rx| = \log M_{\text{max}}$, $|ry| = \log N_{\text{max}}$. On the constraint side, if $M_j < M_{\text{max}}$, the prover divides $rx \to rx_\text{pad} || rx_\text{eval}$. On the witness side, if $N_j < N_{\text{max}}$, the prover divides $ry\to ry_\text{comb} || ry_\text{pad} || ry_\text{eval}$. We describe each section:
* $rx_\text{pad}$ has length $(\log M_{\text{max}} - \log M_j)$ are the "extra" challenges
* $rx_\text{eval}$ has length $\log M_j$ are evaluated on the commitment
* $ry_\text{comb}$ has length-3 is used to combine the 8 different segments of witnesses
* $ry_\text{pad}$ has length $(\log N_{\text{max}} - 3 - \log N_j)$ are the "extra" challenges on each segment. By placing $ry_\text{comb}$ in front of $ry_\text{pad}$, the prover resolves the issue where witness segments are padded to a different length in the commit version and the sumcheck version.
* $ry_\text{eval}$ has length $\log N_j$ are evaluated on the commitment.

Thus,
$$\mathcal{C}_\text{sumcheck}(rx || ry) =  (\prod_{r\in rx_\text{pad} || ry_\text{pad}} 1 - r) \cdot \mathcal{C}_\text{commit}(rx_\text{eval} || ry_\text{comb} || ry_\text{eval})$$

So the opening is performed on $(rx_\text{eval} || ry_\text{comb} || ry_\text{eval})$, and the verifier checks the result by computing and multiplying by $\prod_{r\in rx_\text{pad} || ry_\text{pad}} (1 - r)$.