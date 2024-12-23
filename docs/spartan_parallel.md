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

## Circuit Preprocessing and Commitment (Compile Time)
> Relevant files: `examples/interface.rs`, `src/instance.rs`, and `src/r1csinstance.rs`

### Inputs from `circ_blocks`
> Relevant struct: `CompileTimeKnowledge` in `examples/interface.rs`

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
> Relevant struct: `Instance` in `src/instance.rs`

A prover of `spartan_parallel` needs to show the following:
1. For every block $i$, the witness generated from every execution $j$ of that block $z_{i, j}$ satisfies $\mathcal{C}_i$. (_block correctness_)
2. After permutating $(i_{i, j}, o_{i, j})$ into execution order $(i'_k, o'_k)$, we have $i'_k = o'_{k-1}$ for all $k \neq 0$. (_consistency_)
3. After permutating $p_{i, j} = \{(addr_{i, j, 0}, data_{i, j, 0}), (addr_{i, j, 1}, data_{i, j, 1}), \dots\}$ by address into $p'_k = (addr'_k, data'_k)$, $p'_k$ satisfies (_physical mem coherence_)
$$addr'_{k - 1} + 1 = addr'_k \vee (addr'_{k - 1} = addr'_k \wedge val'_{k - 1} = val'_k)$$
4. After permutating $v_{i, j}$ into $v'_k$, $v'_k$ satisfies memory coherence (_virtual mem coherence_)

We note that the above steps imply the following additional procedures:

5. Every $(i_{i, j}, o_{i, j}, p_{i, j}, v_{i, j})$ is correctly extracted from $z_{i, j}$
6. The sets of $\{i_{i, j}, o_{i, j}\}$, $\{p_{i, j}\}$, $\{v_{i, j}\}$ are permutations of $\{i'_k, o'_k\}$, $\{p'_k\}$, and $\{v'_k\}$

Permutations are checked via grand product proofs. Thus step 6 can be further divided into

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
> Relevant functions:
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

## Witness Preprocessing and Generation
> Relevant files: `examples/interface.rs` and `src/lib.rs`

### Inputs from `circ_blocks`
> Relevant struct: `RunTimeKnowledge` in `examples/interface.rs`

At runtime, `spartan_parallel` reads in from `circ_blocks` through the struct `RunTimeKnowledge`, which describes all the witnesses generated from the blocks:
* `block_vars_matrix`: all the inputs, outputs, memory accesses, and intermediate computations of every block executions, grouped by type of blocks.
* `exec_inputs`: all the inputs and outputs of every block, sorted by execution time.
* `init_phy_mems_list`, `init_vir_mems_list`: memory accesses that sets up the initial memory state, in any order.
* `addr_phy_mems_list`, `addr_vir_mems_list`: memory accesses throughout the program execution (including initialization), ordered by address.
* `addr_ts_bits_list`: bit split of timestamp difference, used by memory coherence check.

### Witness Preprocessing and Commitment
> Relevant file: `src/lib.rs`

Apart from the witnesses provided by each block execution, the prover also needs to compute additional witnesses used by permutation and consistency checks. This includes, most notably:
* `perm_w0 = [tau, r, r^2, ...]`: the randomness used by the random linear permutation. This value is can be efficiently generated by the verifier and does not require commitment.
* `block_w2`, `perm_exec_w2`, `phy_mem_w2`, `vir_mem_w2`: intermediate values used to compute random linear combinations.
* `block_w3`, `perm_exec_w3`, `phy_mem_w3`, `vir_mem_w3`: RLC and cumulative product of RLC. Each is consisted of $w3_k = [v_k, x_k, \pi_k, D_k, ri_k, ro_k]$, where
  - $v_k$ is the valid bit, set to 0 if this particular $w3$ is a pad. If $v_k$ is 0, then every entry of $w3_k$ is 0.
  - $x_k$ is the random linear combination of $(i_k, o_k)$, $p_k$, or $v_k$
  - $\pi_k$ is the cumulative product $\prod_{p \geq k}x_p$, computed as $\pi_k = v_k\cdot D_k$
  - $D_k$ is an intermediate variable: $D_k = x_k \cdot (\pi_{k+1} + (1 - v_{k+1}))$
  - $ri_k$ and $ro_k$ are only used by register transition to record the RLC of $i_k$ and $o_k$ individually
* `block_w3_shifted`, `perm_exec_w3_shifted`, `phy_mem_w3_shifted`, `vir_mem_w3_shifted`: each $w3$ shifted by one row. This is so that $D_k$ can obtain $\pi_{k+1}$ and $v_{k+1}$ for its computation. See shift proofs section for more details.

Note that all of the above witnesses have different sizes:
* `block_vars_matrix`: `block_num_proofs[i] * num_vars_per_block[i]` for each block `i`
* `perm_exec_w2`: `consis_num_proofs * num_ios`, where `num_ios` is the total number of inputs and outputs of a block, and is the same across all blocks.
* `addr_phy_mems_list`, `phy_mem_w2`: `total_num_phy_mem_accesses * 4`  
_XXX: we should be able to reduce the length to `total_num_phy_mem_accesses * 2`._
* `addr_vir_mems_list`, `vir_mem_w2`: `total_num_vir_mem_accesses * 8`  
_XXX: we should be able to reduce the length to `total_num_phy_mem_accesses * 4`._
* `block_w2`: `block_num_proofs[i] * (num_ios + block_num_phy_ops[i] + block_num_vir_ops[i])`
* `perm_exec_w3`, `perm_exec_shifted`: `consis_num_proofs * 8`
* `phy_mem_w3`, `phy_mem_w3_shifted`: `total_num_phy_mem_accesses * 8`
* `vir_mem_w3`, `vir_mem_w3_shifted`: `total_num_vir_mem_accesses * 8`
* `block_w3`, `block_w3_shifted`: `block_num_proofs[i] * 8` for each block `i`

All witnesses are committed using regular dense polynomial commitment schemes. `block_vars_matrix`, `block_w2`, `block_w3`, and `block_w3_shifted` are committed by each type of block. We note that we can use tricks similar to circuit commitment above to batch commit and batch open witness commitments.

## Sumcheck on Circuits and Instances
> Relevant files: `src/customdensepolynomial.rs`, `src/r1csproof.rs` and `src/sumcheck.rs`

The main section of `spartan_parallel` is consisted of three proofs, each with its own sumcheck and commitment opening. Each proof handles:
1. Block correctness and grand product on block-ordered witnesses
2. Transition state consistency and stack and heap coherence
3. Grand product on execution-ordered and memory-ordered witnesses

_XXX: The proofs were divided due to the different sizes of the circuits. However, this problem has since been resolved and one should be able to combine all the proofs together._

Without loss of generosity, we use the block correctness proof (proof 1) to illustrate details of an R1CS proof. Recall that the goal of block correctness proof is to test the satisfiability of each $z'_{i, j}$ on each modified block circuit $\mathcal{C'}_i = (A', B', C')_i$, where
$$z'_{i, j} = (z_{i, j}, r, rz_{i, j}, \pi_{i, j}, \pi'_{i, j})$$
We denote the following parameters for the proof:
* $P$ (`num_instances`): number of circuits.
* $Q_i$ (`num_proofs`): number of assignments to each circuit $i$.
* $X$ (`num_cons`): _maximum_ number of constraints of any circuit
* $W$ (`num_witness_secs`): number of padded segments of $z'_{i, j}$. In this case, $W = 8$.
* $Y$ (`max_num_inputs`): _maximum_ number of witnesses of any circuit

We use the lowercase version of each variable to denote their logarithmic value (e.g. $p = \log P$). Below we walkthrough the proving process of `spartan_parallel`.

The goal of Spartan is to prove that $Az \cdot Bz - Cz = 0$. This is separated into two sumchecks:
* Sumcheck 1 proves that given purported polynomial extensions $\tilde{Az}, \tilde{Bz}, \tilde{Cz}$, 
$$\sum \tilde{\text{eq}} \cdot (\tilde{Az} \cdot \tilde{Bz} - \tilde{Cz}) = 0$$
* Sumcheck 2 proves that given purported polynomial extensions $\tilde{A}, \tilde{B}, \tilde{C}, \tilde{z}$,
 $$(r_A\cdot \tilde{A} + r_B\cdot \tilde{B} + r_C\cdot \tilde{C})\cdot \tilde{z} = r_A\cdot \tilde{Az} + r_B\cdot \tilde{Bz} + r_C\cdot \tilde{Cz}$$
For some random $r_A$, $r_B$, $r_C$.

To implement data-parallelism, we divide Spartan into 4 steps.

#### Obtaining $\tilde{Az}, \tilde{Bz}, \tilde{Cz}$
> Relevant files: `src/r1csinstance.rs` and `src/customdensepolynomial.rs`

While in regular Spartan, $Az$ is simply a length-$X$ vector, obtained by multiplication of a $X\times Y$ matrix $A$ by a length-$Y$ vector $z$, the data-paralleled version is slightly more complicated.

The prover's first task is to construct a `$P\times Q_i\times W\times Y_i` struct `z_mat` through a 4-dimensional vector. For reasons later illustrated in the sumcheck, the $Q_i$ and $Y_i$ sections of `z_mat` are stored _in bit-reverse_: let $Q_\text{max} = \max_i Q_i$, then for a circuit $i$ with $Q_i$ satisfying assignments, assignment $j$ will be stored in the entry:
$$\text{bit\_reverse}_{q_\text{max}}(j) \cdot (Q_i / Q_\text{max})$$
where $\text{bit\_reverse}_{q_\text{max}}(x)$ expresses $x$ using $q_\text{max}$ bits and returns the value produced by assembling the bits from right to left.

For example, let $\max_i Q_i = 32$ and $Q_i = 8$ for a particular circuit $i$. The witnesses for execution 3 of the block is stored in entry $\text{bit\_reverse}_{\log 32}(3) = 11000_b = 24 * 8 / 32 = 6$.

To obtain $Az$, $Bz$, $Cz$, the prover treats `z_mat` as $P$ counts of $Q_i \times (W \cdot Y_i)$ matrix. Since $A$, $B$, $C$ can be expressed as $P$ counts of $X_i\times (W \cdot Y_i)$ matrices, this allows the prover to perform $P$ matrix multiplications to obtain $P \times Q_i \times X_i$ tensors $Az$, $Bz$, $Cz$ and their MLE $\tilde{Az}$ (`poly_Az`), $\tilde{Bz}$, $\tilde{Cz}$. This process is described in `R1CSinstance::multiply_vec_block`. Note that:
* Conceptually, `poly_Az` of every block $i$ has $p + q_\text{max} + x_\text{max}$ variables. However, the value of the variables indexed at $[p, p + q_\text{max} - q_i)$ and $[p + q_\text{max}, p + q_\text{max} + x_\text{max} - x_i)$ does not affect the evaluation of the polynomial.
* Each circuit $i$ has different $Q_i$ and $X_i$, so $Az$ is expressed as a 3-dimensional vector, and the prover stores its MLE in a concise structure `DensePolynomialPqx`.
* For efficiency of the sumcheck, the $Q_i$ and $X_i$ sections of `poly_Az` are stored in bit-reverse. Recall that the $Q_i$ and $Y_i$ sections of `z_mat` are stored in bit-reverse, this means that, during matrix multiplication:
  - The $Q_i$ dimension is already bit-reversed in `z_mat` and does not require additional action.
  - The $X_i$ dimension is in its natural order in $A$, and thus needs to be reversed during multiplication.
  - The $Y_i$ dimension is in its natural order in $A$ but in bit-reverse order in `z_mat`, so the dot product requires reversing one of the two.

#### Sumcheck 1
> Relevant functions: `R1CSProof::prove_phase_one` and `SumcheckInstanceProof::prove_cubic_with_additive_term_disjoint_rounds`

Similar to the regular Spartan, sumcheck 1 is of the following form:
$$\sum \tilde{\text{eq}} \cdot (\tilde{Az} \cdot \tilde{Bz} - \tilde{Cz}) = 0$$

Except that $\tilde{Az}$, $\tilde{Bz}$, and $\tilde{Cz}$ are now $p + q_\text{max} + x_\text{max}$-variate polynomials, which means the sumcheck involves $p + q_\text{max} + x_\text{max}$ rounds and returns with the challenge $r = r_p || r_q || r_x$. However, we want the prover to only perform $\sum_i Q_i \cdot X_i$ computations (as opposed to $P \cdot Q_\text{max} \cdot X_\text{max}$).

We first note that binding the $P$ variables first can cause inefficiencies. This is because each binding on a variable of the $P$ dimension collapses two vectors on the $Q_i$ dimension, which may be of different lengths. As for a toy example, assume that a polynomial $G$ only has 2 dimensions $P\times Q_i$, and let $P = 4$ and $Q_i = [4, 4, 2, 2]$. The polynomial would thus contain 4 variables: 
$$\tilde{G}(x_{p, 0}, x_{p, 1}, x_{q, 0}, x_{q, 1})$$

Binding $x_{p, 0}$ to $r$ is equivalent to the following operations:
$$G_0 = \langle(1 - r)\cdot G_{0, 0} + r\cdot G_{2, 0}, (1 - r)\cdot G_{0, 1} + r\cdot G_{2, 1}, (1 - r)\cdot G_{0, 2}, (1 - r)\cdot G_{0, 3}\rangle$$
$$G_1 = \langle(1 - r)\cdot G_{1, 0} + r\cdot G_{3, 0}, (1 - r)\cdot G_{1, 1} + r\cdot G_{3, 1}, (1 - r)\cdot G_{1, 2}, (1 - r)\cdot G_{1, 3}\rangle$$

Since $Q_2 = Q_3 = 2$, $G_{2, 2}, G_{2, 3}, G_{3, 2}, G_{3, 3}$ are all 0s, thus the prover does not access nor perform operations on them. As a result, in the first round, the prover's work is $\sum_i Q_i = 12$ multiplications. However, after the first round, the prover is left with $P = 2$ and $Q_i = [4, 4]$. So its work binding $x_{p, 1}$ would be 8 multiplications.

Now consider the alternative of binding $x_{q, 1}$ first. All bindings are performed within the $Q$ dimension:
$$G_0 = \langle(1 - r)\cdot G_{0, 0} + r\cdot G_{0, 1}, (1 - r)\cdot G_{0, 2} + r\cdot G_{0, 3}\rangle$$
$$G_1 = \langle(1 - r)\cdot G_{1, 0} + r\cdot G_{1, 1}, (1 - r)\cdot G_{1, 2} + r\cdot G_{1, 3}\rangle$$
$$G_2 = \langle(1 - r)\cdot G_{2, 0} + r\cdot G_{2, 1}\rangle$$
$$G_3 = \langle(1 - r)\cdot G_{3, 0} + r\cdot G_{3, 1}\rangle$$

This again costs 12 multiplications. However, this time it leaves us with $P = 4$ and $Q_i = [2, 2, 1, 1]$, and the next binding of $x_{q, 0}$ costs only 6 multiplications.

As a result, `spartan_parallel` always performs sumcheck bindings from right to left.

_XXX: `bit_reverse` was already designed to help the binding from right to left. Upon further thoughts, however, this seems unnecessary. I'm currently in the process of removing bit-reverse and opt for direct right-to-left sumcheck binding, which is also how ceno does it._