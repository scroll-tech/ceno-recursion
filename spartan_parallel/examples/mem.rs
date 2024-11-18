//! An simple program with some memory operations
//! The pseudocode is:
//!   a[0] = 1
//!   a[1] = 2
//!   s = 0
//!   i = 0
//!   while i != 3:
//!     i = i + a[0]
//!     s = s + a[1]
//! Which, when converted to blocks, is:
//! Block 0:                        Block 1:
//!   assert v * v = v                assert v * v = v
//!   if (v == 1) {                   if (v == 1) {
//!     assert b == 0                   assert b == 1
//!     assert A0 == 0                  assert A0 == 0
//!     assert V0 == 1                  LOAD(A0, V0)
//!     STORE(A0, V0)                   assert A1 == 1
//!     assert A1 == 1                  LOAD(A1, V1)
//!     assert V1 == 2                  i = i + V0
//!     STORE(A1, V1)                   s = s + V1
//!     s = 0                           if i != 3:
//!     i = 1                             b = 1
//!     if i != 3:                      else:
//!       b = 1                           b = 2
//!     else:                           }
//!       b = 2
//!   }
//! Note: take caution when translating STORE(0, 1) into constraints. If an execution of the block is invalid, this could cause a problem!
//!
//! Converting each block to constraints:
//!    Block 0:                        Block 1:
//!  0   v = v * v                       v = v * v
//!  1   0 = w - v                       0 = w - v
//!  2   0 = b0                          0 = b0 - 1
//!  3   0 = i0                          0 = A0
//!  4   0 = s0                          0 = A1 - 1
//!  5   Z1 = (i0 - 3) * Z0              0 = i1 - i0 - V0
//!  6   0 = A0                          0 = s1 - s0 - V1
//!  7   0 = V0 - 1                      Z1 = (i1 - 3) * Z0
//!  8   0 = A1 - 1                      0 = B0 * (Z1 - 1)
//!  9   0 = V1 - 2                      0 = B0 * (b1 - 1)
//! 10   0 = B0 * (Z1 - 1)               0 = (1 - B0) * (i1 - 3)
//! 11   0 = B0 * (b1 - 1)               0 = (1 - B0) * (b1 - 2)
//! 12   0 = (1 - B0) * (i0 - 3)
//! 13   0 = (1 - B0) * (b1 - 2)
//! 14   i1 = i0
//! 15   s1 = s0
//!
//! Program States
//! The first entry of the witness is a copy of the valid bit, followed by a list of addresses and then a list of values
//! Put all memory states at the front of the witnesses
//!        0    1   2   3    4    5   6   7     0   1   2   3   4   5   6   7
//! Exec:  v | b0  i0  s0  | _ | b1  i1  s1  |  w   A0  A1  V0  V1  Z0  Z1  B0
//! 0      1    0   0   0    0    1   0   0     1   0   1   1   2 -3i   1   1
//! 1      1    1   0   0    0    1   1   2     1   0   1   1   2 -2i   1   1
//! 2      1    1   1   2    0    1   2   4     1   0   1   1   2 -1i   1   1
//! 3      1    1   2   4    0    2   3   6     1   0   1   1   2   0   0   0
//! 4      0    0   0   0    0    0   0   0     0   0   0   0   0   0   0   0
//!
#![allow(clippy::assertions_on_result_states)]
use std::{ops::Neg, cmp::max};

use curve25519_dalek::scalar::Scalar;
use libspartan::{instance::Instance, SNARKGens, VarsAssignment, SNARK, InputsAssignment, MemsAssignment};
use merlin::Transcript;

// Everything provided by the frontend
struct CompileTimeKnowledge {
  block_num_instances: usize,
  num_vars: usize,
  num_inputs_unpadded: usize,
  total_num_proofs_bound: usize,
  block_num_mem_accesses: Vec<usize>,
  total_num_mem_accesses_bound: usize,

  args: Vec<Vec<(Vec<(usize, [u8; 32])>, Vec<(usize, [u8; 32])>, Vec<(usize, [u8; 32])>)>>,

  func_input_width: usize,
  input_offset: usize,
  input_block_num: usize,
  output_offset: usize,
  output_block_num: usize
}

// Everything provided by the prover
struct RunTimeKnowledge {
  block_max_num_proofs: usize,
  block_num_proofs: Vec<usize>,
  consis_num_proofs: usize,
  total_num_mem_accesses: usize,

  block_vars_matrix: Vec<Vec<VarsAssignment>>,
  block_inputs_matrix: Vec<Vec<InputsAssignment>>,
  exec_inputs: Vec<InputsAssignment>,
  addr_mems_list: Vec<MemsAssignment>,

  input: Vec<[u8; 32]>,
  output: [u8; 32],
  output_exec_num: usize
}

#[allow(non_snake_case)]
fn produce_r1cs() -> (
  CompileTimeKnowledge,
  RunTimeKnowledge
) {
  // Separate instances into three lists:
  // BLOCK: correctness within a block
  // CONSIS: consistency between blocks
  // PERM: permutation between two orderings
  //
  // Separate inputs into two lists:
  // BLOCK_ORDER
  // EXEC_ORDER
  //
  // Separate vars into three lists
  // BLOCK, CONSIS, PERM

  let minus_three = Scalar::from(3u32).neg().to_bytes();
  let minus_two = Scalar::from(2u32).neg().to_bytes();
  let minus_one = Scalar::from(1u32).neg().to_bytes();
  let zero = Scalar::zero().to_bytes();
  let one = Scalar::one().to_bytes();
  let two = Scalar::from(2u32).to_bytes();
  let three = Scalar::from(3u32).to_bytes();
  let four = Scalar::from(4u32).to_bytes();
  let six = Scalar::from(6u32).to_bytes();

  // --
  // COMPILE TIME KNOWLEDGE
  // --

  // num_vars should be consistent accross the instances
  // everything else is instance-specific
  // Divide inputs into (1, input, 1, output)
  // So num_inputs = num_outputs = num_vars / 2 - 1
  let num_vars = 16;
  // How many non-dummy inputs do we have?
  let num_inputs_unpadded = 4;

  // Number of proofs of each R1CS instance
  // Total for all blocks and one block
  // OBTAINED DURING COMPILE TIME
  let total_num_proofs_bound = 16;
  // Bound on total number of memory accesses
  let total_num_mem_accesses_bound = 16;

  // What is the input and output block?
  // Note: the assumption is that during a normal execution, the input block and the output block will only be reached once
  let input_block_num = 0;
  let output_block_num = 2;

  // --
  // BLOCK Instances
  // --

  // Number of R1CS instances
  let block_num_instances = 2;

  // Program States
  // Put all memory states at the front of the witnesses
  //        0    1   2   3    4    5   6   7     0   2   3   4   5   6   7   8
  // Exec:  v | b0  i0  s0  | _ | b1  i1  s1  |  w  A0  V0  A1  V1  Z0  Z1  B0
  let args = {
    let V_valid = 0;
    let V_cnst = V_valid;
    let V_b0 = 1;
    let V_i0 = 2;
    let V_s0 = 3;
    let V_b1 = num_inputs_unpadded + 1;
    let V_i1 = num_inputs_unpadded + 2;
    let V_s1 = num_inputs_unpadded + 3;
    let V_w = num_vars;
    let V_A0 = num_vars + 1;
    let V_V0 = num_vars + 2;
    let V_A1 = num_vars + 3;
    let V_V1 = num_vars + 4;
    let V_Z0 = num_vars + 5;
    let V_Z1 = num_vars + 6;
    let V_B0 = num_vars + 7;

    let mut args = Vec::new();
    // Block 0
    let arg = vec![
      // 0: v * v = v
      (vec![(V_valid, one)], vec![(V_valid, one)], vec![(V_valid, one)]),
      // 1: 0 = w - v
      (vec![], vec![], vec![(V_w, one), (V_valid, minus_one)]),
      // 2: 0 = b0
      (vec![], vec![], vec![(V_b0, one)]),
      // 3: 0 = i0
      (vec![], vec![], vec![(V_i0, one)]),
      // 4: 0 = s0
      (vec![], vec![], vec![(V_s0, one)]),
      // 5: (i0 - 3) * Z0 = Z1
      (vec![(V_i0, one), (V_cnst, minus_three)], vec![(V_Z0, one)], vec![(V_Z1, one)]),
      // 6: 0 = A0
      (vec![], vec![], vec![(V_A0, one)]),
      // 7: 0 = V0 - 1
      (vec![], vec![], vec![(V_V0, one), (V_cnst, minus_one)]),
      // 8: 0 = A1 - 1
      (vec![], vec![], vec![(V_A1, one), (V_cnst, minus_one)]),
      // 9: 0 = V1 - 2
      (vec![], vec![], vec![(V_V1, one), (V_cnst, minus_two)]),
      // 10: B0 * (Z1 - 1) = 0
      (vec![(V_B0, one)], vec![(V_Z1, one), (V_cnst, minus_one)], vec![]),
      // 11: B0 * (b1 - 1) = 0
      (vec![(V_B0, one)], vec![(V_b1, one), (V_cnst, minus_one)], vec![]),
      // 12: (1 - B0) * (i1 - 3) = 0
      (vec![(V_cnst, one), (V_B0, minus_one)], vec![(V_i1, one), (V_cnst, minus_three)], vec![]),
      // 13: (1 - B0) * (b1 - 2) = 0
      (vec![(V_cnst, one), (V_B0, minus_one)], vec![(V_b1, one), (V_cnst, minus_two)], vec![]),
      // 14: 0 = i1 - i0
      (vec![], vec![], vec![(V_i1, one), (V_i0, minus_one)]),
      // 15: 0 = s1 - s0
      (vec![], vec![], vec![(V_s1, one), (V_s0, minus_one)]),
    ];
    args.push(arg);

    // Block 1
    let arg = vec![
      // 0: v * v = v
      (vec![(V_valid, one)], vec![(V_valid, one)], vec![(V_valid, one)]),
      // 1: 0 = w - v
      (vec![], vec![], vec![(V_w, one), (V_valid, minus_one)]),
      // 2: 0 = b0 - 1
      (vec![], vec![], vec![(V_b0, one), (V_cnst, minus_one)]),
      // 3: 0 = A0
      (vec![], vec![], vec![(V_A0, one)]),
      // 4: 0 = A1 - 1
      (vec![], vec![], vec![(V_A1, one), (V_cnst, minus_one)]),
      // 5: 0 = i1 - i0 - V0
      (vec![], vec![], vec![(V_i1, one), (V_i0, minus_one), (V_V0, minus_one)]),
      // 6: 0 = s1 - s0 - V1
      (vec![], vec![], vec![(V_s1, one), (V_s0, minus_one), (V_V1, minus_one)]),
      // 7: (i1 - 3) * Z0 = Z1
      (vec![(V_i1, one), (V_cnst, minus_three)], vec![(V_Z0, one)], vec![(V_Z1, one)]),
      // 8: B0 * (Z1 - 1) = 0
      (vec![(V_B0, one)], vec![(V_Z1, one), (V_cnst, minus_one)], vec![]),
      // 9: B0 * (b1 - 1) = 0
      (vec![(V_B0, one)], vec![(V_b1, one), (V_cnst, minus_one)], vec![]),
      // 10: (1 - B0) * (i1 - 3) = 0
      (vec![(V_cnst, one), (V_B0, minus_one)], vec![(V_i1, one), (V_cnst, minus_three)], vec![]),
      // 11: (1 - B0) * (b1 - 2) = 0
      (vec![(V_cnst, one), (V_B0, minus_one)], vec![(V_b1, one), (V_cnst, minus_two)], vec![])
    ];
    args.push(arg);

    args
  };

  // --
  // End Instances
  // --

  // --
  // RUNTIME KNOWLEDGE
  // --
  let block_max_num_proofs = 4;
  let block_num_proofs = vec![1, 4];
  let consis_num_proofs: usize = 5;
  // What is the input and the output?
  let input = vec![zero, zero];
  let output = three;
  // Which block in the execution order is the output block?
  let output_exec_num = 3;
  // How many memory accesses per block?
  let block_num_mem_accesses = vec![2, 2];
  // How many memory accesses are there?
  let total_num_mem_accesses = 8;

  // --
  // Begin Assignments
  // --

  let (
    block_vars_matrix,
    block_inputs_matrix,
    exec_inputs,
    addr_mems_list
  ) = {

    let mut block_vars_matrix = Vec::new();
    let mut block_inputs_matrix = Vec::new();
    let mut exec_inputs = Vec::new();
    let mut addr_mems_list = Vec::new();

    // Assignment needs to be sorted by # of executions per block, so assignment[0] corresponds to block 1, assignment[1] is block 0
    // Block 1
    // Exec:  v | b0  i0  s0  | _ | b1  i1  s1  |  w  A0  V0  A1  V1  Z0  Z1  B0
    // 0      1    1   0   0    0    1   1   2     1   0   1   1   2 -2i   1   1
    // 1      1    1   1   2    0    1   2   4     1   0   1   1   2 -1i   1   1
    // 2      1    1   2   4    0    2   3   6     1   0   1   1   2   0   0   0
    // 3      0    0   0   0    0    0   0   0     0   0   0   0   0   0   0   0
    let (assignment_vars, assignment_inputs) = {
      let mut assignment_vars = Vec::new();
      let mut assignment_inputs = Vec::new();
      // Iteration i = 1
      let inputs: Vec<[u8; 32]> = [vec![one, one, zero, zero], vec![zero, one, one, two]].concat();
      let vars: Vec<[u8; 32]> = [vec![one, zero, one, one, two, Scalar::from(2u32).neg().invert().to_bytes(), one, one], vec![zero; 8]].concat();
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      exec_inputs.push(next_block_assignment_inputs);
      // Iteration i = 2
      let inputs: Vec<[u8; 32]> = [vec![one, one, one, two], vec![zero, one, two, four]].concat();
      let vars: Vec<[u8; 32]> = [vec![one, zero, one, one, two, Scalar::from(1u32).neg().invert().to_bytes(), one, one], vec![zero; 8]].concat();
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      exec_inputs.push(next_block_assignment_inputs);
      // Iteration i = 3
      let inputs: Vec<[u8; 32]> = [vec![one, one, two, four], vec![zero, two, three, six]].concat();
      let vars: Vec<[u8; 32]> = [vec![one, zero, one, one, two, zero, zero, zero], vec![zero; 8]].concat();
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      exec_inputs.push(next_block_assignment_inputs);
      // Iteration i = 4
      let inputs: Vec<[u8; 32]> = vec![zero; 8];
      let vars: Vec<[u8; 32]> = vec![zero; 16];
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      exec_inputs.push(next_block_assignment_inputs);

      (assignment_vars, assignment_inputs)
    };
    block_vars_matrix.push(assignment_vars);
    block_inputs_matrix.push(assignment_inputs);

    // Block 0
    // Exec:  v | b0  i0  s0  | _ | b1  i1  s1  |  w   L  A0  A1  V0  V1  Z0  Z1  B0
    // 0      1    0   0   0    0    1   0   0     1   2   0   1   1   2 -3i   1   1
    let (assignment_vars, assignment_inputs) = {
      let mut assignment_vars = Vec::new();
      let mut assignment_inputs = Vec::new();
      let inputs = [vec![one, zero, zero, zero], vec![zero, one, zero, zero]].concat();
      let vars = [vec![one, zero, one, one, two, Scalar::from(3u32).neg().invert().to_bytes(), one, one], vec![zero; 8]].concat();
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      exec_inputs.insert(0, next_block_assignment_inputs);

      (assignment_vars, assignment_inputs)
    };
    block_vars_matrix.push(assignment_vars);
    block_inputs_matrix.push(assignment_inputs);

    // Witnesses for permutation cannot be generated until tau and r are generated
    // Both can only be generated at proving time

    // Memory accesses in address order: (v, addr, val, D)
    // where D[k] = v[k + 1] * (1 - addr[k + 1] - addr[k])
    for _ in 0..3 {
      addr_mems_list.push(VarsAssignment::new(&vec![one, zero, one, one]).unwrap());
    }
    addr_mems_list.push(VarsAssignment::new(&vec![one, zero, one, zero]).unwrap());
    for _ in 0..3 {
      addr_mems_list.push(VarsAssignment::new(&vec![one, one, two, one]).unwrap());
    }
    addr_mems_list.push(VarsAssignment::new(&vec![one, one, two, zero]).unwrap());

    (block_vars_matrix, block_inputs_matrix, exec_inputs, addr_mems_list)
  };

  // --
  // End Assignments
  // --

  (
    // COMPILE TIME KNOWLEDGE
    CompileTimeKnowledge {
      block_num_instances,
      num_vars,
      num_inputs_unpadded,
      total_num_proofs_bound,
      block_num_mem_accesses,
      total_num_mem_accesses_bound,

      args,

      func_input_width: 2,
      input_offset: 2,
      input_block_num,
      output_offset: 2,
      output_block_num
    },

    // RUNTIME KNOWLEDGE
    RunTimeKnowledge {
      block_max_num_proofs,
      block_num_proofs,
      consis_num_proofs,
      total_num_mem_accesses,

      block_vars_matrix,
      block_inputs_matrix,
      exec_inputs,
      addr_mems_list,

      input,
      output,
      output_exec_num
    }
  )
}

fn main() {
  // produce an R1CS instance
  let (ctk, rtk) = produce_r1cs();
  let block_num_instances = ctk.block_num_instances;
  let num_vars = ctk.num_vars;
  let num_inputs_unpadded = ctk.num_inputs_unpadded;
  let num_ios = (num_inputs_unpadded * 2).next_power_of_two();
  let total_num_proofs_bound = ctk.total_num_proofs_bound;
  let block_num_mem_accesses = ctk.block_num_mem_accesses;
  let total_num_mem_accesses_bound = ctk.total_num_mem_accesses_bound;

  let block_vars_matrix = rtk.block_vars_matrix;
  let block_inputs_matrix = rtk.block_inputs_matrix;

  assert!(ctk.args.len() == block_num_instances);
  assert!(block_num_mem_accesses.len() == block_num_instances);
  for n in &block_num_mem_accesses {
    assert!(3 * n <= num_vars - 4);
  }

  // Generate all remaining instances

  // BLOCK INSTANCES
  let (block_num_cons, block_num_non_zero_entries, mut block_inst) = Instance::gen_block_inst(block_num_instances, num_vars, &ctk.args);

  // CONSIS INSTANCES
  // CONSIS is consisted of two instances
  // CONSIS_COMB performs random linear combination on inputs and outputs to a single value
  // It is parallelized for consis_num_proofs copies
  // CONSIS_CHECK checks that these values indeed matches
  // There is only one copy for CONSIS_CHECK
  // CONSIS_COMB
  let (consis_comb_num_cons, consis_comb_num_non_zero_entries, consis_comb_inst) = Instance::gen_consis_comb_inst(num_inputs_unpadded, num_ios);
  // CONSIS_CHECK
  let (consis_check_num_cons_base, consis_check_num_non_zero_entries, consis_check_inst) = Instance::gen_consis_check_inst(total_num_proofs_bound);

  // PERM INSTANCES
  // PERM is consisted of four instances
  // PERM_PRELIM checks the correctness of (r, r^2, ...)
  // PERM_ROOT and PERM_BLOCK_POLY compute the polynomial defined by block_inputs
  // PERM_ROOT and PERM_EXEC_POLY compute the polynomial defined by exec_inputs
  // Finally, the verifier checks that the two products are the same
  // The product is defined by PROD = \prod(\tau - (\sum_i a_i * r^{i-1}))
  // There is only one proof
  // PERM_PRELIM
  let (perm_prelim_num_cons, perm_prelim_num_non_zero_entries, perm_prelim_inst) = Instance::gen_perm_prelim_inst(num_inputs_unpadded, num_ios);
  // PERM_ROOT
  let (perm_root_num_cons, perm_root_num_non_zero_entries, perm_root_inst) = Instance::gen_perm_root_inst(num_inputs_unpadded, num_ios);
  // PERM_POLY for PERM_BLOCK_POLY, PERM_EXEC_POLY, & MEM_ADDR_POLY
  let perm_size_bound = max(total_num_proofs_bound, total_num_mem_accesses_bound);
  let (perm_poly_num_cons_base, perm_poly_num_non_zero_entries, perm_poly_inst) = Instance::gen_perm_poly_inst(perm_size_bound, 4);

  // MEM INSTANCES
  // MEM_EXTRACT
  let max_block_num_mem_accesses = *block_num_mem_accesses.iter().max().unwrap();
  let (mem_extract_num_cons, mem_extract_num_non_zero_entries, mem_extract_inst) = Instance::gen_mem_extract_inst(num_vars, max_block_num_mem_accesses);
  // MEM_BLOCK_POLY
  let (mem_block_poly_num_cons_base, mem_block_poly_num_non_zero_entries, mem_block_poly_inst) = Instance::gen_perm_poly_inst(total_num_proofs_bound, num_vars);
  // MEM_COHERE
  let (mem_cohere_num_cons_base, mem_cohere_num_non_zero_entries, mem_cohere_inst) = Instance::gen_mem_cohere_inst(total_num_mem_accesses_bound);
  // MEM_ADDR_COMB
  let (mem_addr_comb_num_cons, mem_addr_comb_num_non_zero_entries, mem_addr_comb_inst) = Instance::gen_mem_addr_comb_inst();

  // --
  // INSTANCE PREPROCESSING
  // --
  let consis_check_num_cons = consis_check_num_cons_base * total_num_proofs_bound;
  let perm_poly_num_cons = perm_poly_num_cons_base * perm_size_bound;
  let mem_block_poly_num_cons = mem_block_poly_num_cons_base * total_num_proofs_bound;
  let mem_cohere_num_cons = mem_cohere_num_cons_base * total_num_mem_accesses_bound;

  // produce public parameters
  let block_gens = SNARKGens::new(block_num_cons, 2 * num_vars, block_num_instances, block_num_non_zero_entries);
  let consis_comb_gens = SNARKGens::new(consis_comb_num_cons, 4 * num_ios, 1, consis_comb_num_non_zero_entries);
  let consis_check_gens = SNARKGens::new(consis_check_num_cons, total_num_proofs_bound * 4, 1, consis_check_num_non_zero_entries);
  let perm_prelim_gens = SNARKGens::new(perm_prelim_num_cons, num_ios, 1, perm_prelim_num_non_zero_entries);
  let perm_root_gens = SNARKGens::new(perm_root_num_cons, 4 * num_ios, 1, perm_root_num_non_zero_entries);
  let perm_poly_gens = SNARKGens::new(perm_poly_num_cons, perm_size_bound * 4, 1, perm_poly_num_non_zero_entries);
  let mem_extract_gens = SNARKGens::new(mem_extract_num_cons, 4 * num_vars, 1, mem_extract_num_non_zero_entries);
  let mem_block_poly_gens = SNARKGens::new(mem_block_poly_num_cons, total_num_proofs_bound * num_vars, 1, mem_block_poly_num_non_zero_entries);
  let mem_cohere_gens = SNARKGens::new(mem_cohere_num_cons, total_num_mem_accesses_bound * 4, 1, mem_cohere_num_non_zero_entries);
  let mem_addr_comb_gens = SNARKGens::new(mem_addr_comb_num_cons, 4 * 4, 1, mem_addr_comb_num_non_zero_entries);
  // Only use one version of gens_r1cs_sat
  // for size VAR
  let vars_gens = SNARKGens::new(block_num_cons, num_vars, block_num_instances, block_num_non_zero_entries).gens_r1cs_sat;
  // for size PROOF * VAR
  let proofs_times_vars_gens = SNARKGens::new(block_num_cons, max(total_num_proofs_bound, total_num_mem_accesses_bound) * num_vars, 1, block_num_non_zero_entries).gens_r1cs_sat;

  // create a commitment to the R1CS instance
  // TODO: change to encoding all r1cs instances
  let (block_comm, block_decomm) = SNARK::multi_encode(&block_inst, &block_gens);
  let (consis_comb_comm, consis_comb_decomm) = SNARK::encode(&consis_comb_inst, &consis_comb_gens);
  let (consis_check_comm, consis_check_decomm) = SNARK::encode(&consis_check_inst, &consis_check_gens);
  let (perm_prelim_comm, perm_prelim_decomm) = SNARK::encode(&perm_prelim_inst, &perm_prelim_gens);
  let (perm_root_comm, perm_root_decomm) = SNARK::encode(&perm_root_inst, &perm_root_gens);
  let (perm_poly_comm, perm_poly_decomm) = SNARK::encode(&perm_poly_inst, &perm_poly_gens);
  let (mem_extract_comm, mem_extract_decomm) = SNARK::encode(&mem_extract_inst, &mem_extract_gens);
  let (mem_block_poly_comm, mem_block_poly_decomm) = SNARK::encode(&mem_block_poly_inst, &mem_block_poly_gens);
  let (mem_cohere_comm, mem_cohere_decomm) = SNARK::encode(&mem_cohere_inst, &mem_cohere_gens);
  let (mem_addr_comb_comm, mem_addr_comb_decomm) = SNARK::encode(&mem_addr_comb_inst, &mem_addr_comb_gens);

  // Mask vector for mem_extract
  let (mem_block_mask, mem_block_poly_mask_list, mem_block_comm_mask_list) =
    Instance::gen_mem_extract_mask(block_num_instances, max_block_num_mem_accesses.next_power_of_two(), &block_num_mem_accesses, &vars_gens);

  // produce a proof of satisfiability
  let mut prover_transcript = Transcript::new(b"snark_example");
  let proof = SNARK::prove(
    ctk.input_block_num,
    ctk.output_block_num,
    ctk.func_input_width,
    ctk.input_offset,
    ctk.output_offset,
    &rtk.input,
    &rtk.output,
    rtk.output_exec_num,

    num_vars,
    num_ios,
    num_inputs_unpadded,
    total_num_proofs_bound,
    block_num_instances,
    rtk.block_max_num_proofs,
    &rtk.block_num_proofs,
    &mut block_inst,
    &block_comm,
    &block_decomm,
    &block_gens,

    rtk.consis_num_proofs,
    &consis_comb_inst,
    &consis_comb_comm,
    &consis_comb_decomm,
    &consis_comb_gens,
    consis_check_num_cons_base,
    &consis_check_inst,
    &consis_check_comm,
    &consis_check_decomm,
    &consis_check_gens,

    &perm_prelim_inst,
    &perm_prelim_comm,
    &perm_prelim_decomm,
    &perm_prelim_gens,
    &perm_root_inst,
    &perm_root_comm,
    &perm_root_decomm,
    &perm_root_gens,
    perm_poly_num_cons_base,
    &perm_poly_inst,
    &perm_poly_comm,
    &perm_poly_decomm,
    &perm_poly_gens,

    max_block_num_mem_accesses,
    &mem_extract_inst,
    &mem_extract_comm,
    &mem_extract_decomm,
    &mem_extract_gens,

    mem_block_poly_num_cons_base,
    &mem_block_poly_inst,
    &mem_block_poly_comm,
    &mem_block_poly_decomm,
    &mem_block_poly_gens,

    total_num_mem_accesses_bound,
    rtk.total_num_mem_accesses,
    mem_cohere_num_cons_base,
    &mem_cohere_inst,
    &mem_cohere_comm,
    &mem_cohere_decomm,
    &mem_cohere_gens,

    &mem_addr_comb_inst,
    &mem_addr_comb_comm,
    &mem_addr_comb_decomm,
    &mem_addr_comb_gens,

    block_vars_matrix,
    block_inputs_matrix,
    rtk.exec_inputs,
    rtk.addr_mems_list,

    &mem_block_mask,
    &mem_block_poly_mask_list,
    &mem_block_comm_mask_list,

    &vars_gens,
    &proofs_times_vars_gens,
    &mut prover_transcript,
  );

  // verify the proof of satisfiability
  let mut verifier_transcript = Transcript::new(b"snark_example");
  assert!(proof.verify(
    ctk.input_block_num,
    ctk.output_block_num,
    ctk.func_input_width,
    ctk.input_offset,
    ctk.output_offset,
    &rtk.input,
    &rtk.output,
    rtk.output_exec_num,

    num_vars,
    num_ios,
    num_inputs_unpadded,
    total_num_proofs_bound,
    block_num_instances,
    rtk.block_max_num_proofs,
    &rtk.block_num_proofs,
    block_num_cons,
    &block_comm,
    &block_gens,

    rtk.consis_num_proofs,
    consis_comb_num_cons,
    &consis_comb_comm,
    &consis_comb_gens,
    consis_check_num_cons_base,
    &consis_check_comm,
    &consis_check_gens,

    perm_prelim_num_cons,
    &perm_prelim_comm,
    &perm_prelim_gens,
    perm_root_num_cons,
    &perm_root_comm,
    &perm_root_gens,
    perm_poly_num_cons_base,
    &perm_poly_comm,
    &perm_poly_gens,

    max_block_num_mem_accesses,
    mem_extract_num_cons,
    &mem_extract_comm,
    &mem_extract_gens,
    mem_block_poly_num_cons_base,
    &mem_block_poly_comm,
    &mem_block_poly_gens,
    total_num_mem_accesses_bound,
    rtk.total_num_mem_accesses,
    mem_cohere_num_cons_base,
    &mem_cohere_comm,
    &mem_cohere_gens,
    mem_addr_comb_num_cons,
    &mem_addr_comb_comm,
    &mem_addr_comb_gens,

    &mem_block_comm_mask_list,

    &vars_gens,
    &proofs_times_vars_gens,
    &mut verifier_transcript
  ).is_ok());
  println!("proof verification successful!");
}
