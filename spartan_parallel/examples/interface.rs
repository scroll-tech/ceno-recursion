//! Reads in constraints and inputs from zok_tests/constraints and zok_tests/inputs
//! Used as a temporary interface to / from CirC
#![allow(clippy::assertions_on_result_states)]
use std::io::{BufRead, Read};
use std::{default, env};
use std::{fs::File, io::BufReader};

use libspartan::scalar::{ScalarExt2, SpartanExtensionField};
use libspartan::{instance::Instance, InputsAssignment, MemsAssignment, VarsAssignment, SNARK};
use transcript::BasicTranscript as Transcript;
use serde::{Deserialize, Serialize};
use std::time::*;

const TOTAL_NUM_VARS_BOUND: usize = 10000000;

// Everything provided by the frontend
#[derive(Serialize, Deserialize)]
struct CompileTimeKnowledge {
  block_num_instances: usize,
  num_vars: usize,
  num_inputs_unpadded: usize,
  num_vars_per_block: Vec<usize>,
  block_num_phy_ops: Vec<usize>,
  block_num_vir_ops: Vec<usize>,
  max_ts_width: usize,

  args: Vec<
    Vec<(
      Vec<(usize, [u8; 32])>,
      Vec<(usize, [u8; 32])>,
      Vec<(usize, [u8; 32])>,
    )>,
  >,

  input_liveness: Vec<bool>,
  func_input_width: usize,
  input_offset: usize,
  input_block_num: usize,
  output_offset: usize,
  output_block_num: usize,
}

impl CompileTimeKnowledge {
  fn deserialize_from_file(benchmark_name: String) -> CompileTimeKnowledge {
    // Input can be provided through multiple files, use i to determine the next file label
    let mut i = 0;
    let mut file_name = format!("../zok_tests/constraints/{benchmark_name}_bin_{i}.ctk");
    let mut content: Vec<u8> = Vec::new();
    while let Ok(mut f) = File::open(file_name) {
      let mut new_content: Vec<u8> = Vec::new();
      f.read_to_end(&mut new_content).unwrap();
      content.extend(new_content);
      i += 1;
      file_name = format!("../zok_tests/constraints/{benchmark_name}_bin_{i}.ctk");
    }
    bincode::deserialize(&content).unwrap()
  }
}

// Everything provided by the prover
#[derive(Serialize, Deserialize)]
struct RunTimeKnowledge<S: SpartanExtensionField> {
  block_max_num_proofs: usize,
  block_num_proofs: Vec<usize>,
  consis_num_proofs: usize,
  total_num_init_phy_mem_accesses: usize,
  total_num_init_vir_mem_accesses: usize,
  total_num_phy_mem_accesses: usize,
  total_num_vir_mem_accesses: usize,

  block_vars_matrix: Vec<Vec<VarsAssignment<S>>>,
  exec_inputs: Vec<InputsAssignment<S>>,
  init_phy_mems_list: Vec<MemsAssignment<S>>,
  init_vir_mems_list: Vec<MemsAssignment<S>>,
  addr_phy_mems_list: Vec<MemsAssignment<S>>,
  addr_vir_mems_list: Vec<MemsAssignment<S>>,
  addr_ts_bits_list: Vec<MemsAssignment<S>>,

  input: Vec<[u8; 32]>,
  input_stack: Vec<[u8; 32]>,
  input_mem: Vec<[u8; 32]>,
  output: [u8; 32],
  output_exec_num: usize,
}

impl<S: SpartanExtensionField + for<'de> serde::de::Deserialize<'de>> RunTimeKnowledge<S> {
  fn deserialize_from_file(benchmark_name: String) -> RunTimeKnowledge<S> {
    // Input can be provided through multiple files, use i to determine the next file label
    let mut i = 0;
    let mut file_name = format!("../zok_tests/inputs/{benchmark_name}_bin_{i}.rtk");
    let mut content: Vec<u8> = Vec::new();
    while let Ok(mut f) = File::open(file_name) {
      let mut new_content: Vec<u8> = Vec::new();
      f.read_to_end(&mut new_content).unwrap();
      content.extend(new_content);
      i += 1;
      file_name = format!("../zok_tests/inputs/{benchmark_name}_bin_{i}.rtk");
    }
    bincode::deserialize(&content).unwrap()
  }
}

fn main() {
  let benchmark_name = &env::args().collect::<Vec<String>>()[1];
  // let ctk = CompileTimeKnowledge::read_from_file(benchmark_name.to_string()).unwrap();
  let ctk = CompileTimeKnowledge::deserialize_from_file(benchmark_name.to_string());
  // let rtk = RunTimeKnowledge::read_from_file(benchmark_name.to_string()).unwrap();
  let rtk: RunTimeKnowledge<ScalarExt2> =
    RunTimeKnowledge::deserialize_from_file(benchmark_name.to_string());

  // --
  // INSTANCE PREPROCESSING
  // --
  println!("Preprocessing instances...");
  let preprocess_start = Instant::now();
  let block_num_instances_bound = ctk.block_num_instances;
  let num_vars = ctk.num_vars;
  // num_inputs_unpadded is the actual size of the input
  let num_inputs_unpadded = ctk.num_inputs_unpadded;
  // num_ios is the width used by all input related computations
  let num_ios = (num_inputs_unpadded * 2).next_power_of_two();
  let block_num_phy_ops = ctk.block_num_phy_ops;
  let block_num_vir_ops = ctk.block_num_vir_ops;
  let max_block_num_phy_ops = *block_num_phy_ops.iter().max().unwrap();
  let max_block_num_vir_ops = *block_num_vir_ops.iter().max().unwrap();

  let mem_addr_ts_bits_size = (2 + ctk.max_ts_width).next_power_of_two();

  assert_eq!(num_vars, num_vars.next_power_of_two());
  assert!(ctk.args.len() == block_num_instances_bound);
  assert!(block_num_phy_ops.len() == block_num_instances_bound);
  // If output_block_num < block_num_instances, the prover can cheat by executing the program multiple times
  assert!(ctk.output_block_num >= block_num_instances_bound);

  println!("Generating Circuits...");
  // --
  // BLOCK INSTANCES
  // block_inst is used by sumcheck. Every block has the same number of variables
  let (block_num_vars, block_num_cons, block_num_non_zero_entries, mut block_inst) =
    Instance::gen_block_inst::<true, false>(
      block_num_instances_bound,
      num_vars,
      &ctk.args,
      num_inputs_unpadded,
      &block_num_phy_ops,
      &block_num_vir_ops,
      &ctk.num_vars_per_block,
      &rtk.block_num_proofs,
    );
  // block_inst is used by commitment. Every block has different number of variables
  let (_, _, _, block_inst_for_commit) = Instance::<ScalarExt2>::gen_block_inst::<true, true>(
    block_num_instances_bound,
    num_vars,
    &ctk.args,
    num_inputs_unpadded,
    &block_num_phy_ops,
    &block_num_vir_ops,
    &ctk.num_vars_per_block,
    &rtk.block_num_proofs,
  );
  println!("Finished Block");

  // Pairwise INSTANCES
  // CONSIS_CHECK & PHY_MEM_COHERE
  let (
    pairwise_check_num_vars,
    pairwise_check_num_cons,
    pairwise_check_num_non_zero_entries,
    mut pairwise_check_inst,
  ) = Instance::gen_pairwise_check_inst::<true>(
    ctk.max_ts_width,
    mem_addr_ts_bits_size,
    rtk.consis_num_proofs,
    rtk.total_num_phy_mem_accesses,
    rtk.total_num_vir_mem_accesses,
  );
  println!("Finished Pairwise");

  // PERM INSTANCES
  // PERM_ROOT
  let (perm_root_num_cons, perm_root_num_non_zero_entries, perm_root_inst) =
    Instance::gen_perm_root_inst::<true>(
      num_inputs_unpadded,
      num_ios,
      rtk.consis_num_proofs,
      rtk.total_num_phy_mem_accesses,
      rtk.total_num_vir_mem_accesses,
    );
  println!("Finished Perm");

  // --
  // COMMITMENT PREPROCESSING
  // --
  println!("Producing Public Parameters...");

  // create a commitment to the R1CS instance
  println!("Comitting Circuits...");
  // block_comm_map records the sparse_polys committed in each commitment
  // Note that A, B, C are committed separately, so sparse_poly[3*i+2] corresponds to poly C of instance i
  let (block_comm_map, block_comm_list, block_decomm_list) =
    SNARK::multi_encode(&block_inst_for_commit);
  println!("Finished Block");
  let (pairwise_check_comm, pairwise_check_decomm) = SNARK::encode(&pairwise_check_inst);
  println!("Finished Pairwise");
  let (perm_root_comm, perm_root_decomm) = SNARK::encode(&perm_root_inst);
  println!("Finished Perm");

  // --
  // WITNESS PREPROCESSING
  // --
  let block_num_proofs = rtk.block_num_proofs;
  let block_vars_matrix = rtk.block_vars_matrix;

  assert!(block_num_proofs.len() <= block_num_instances_bound);
  assert!(block_vars_matrix.len() <= block_num_instances_bound);
  let preprocess_time = preprocess_start.elapsed();
  println!("Preprocess time: {}ms", preprocess_time.as_millis());

  println!("Running the proof...");
  // produce a proof of satisfiability
  let mut prover_transcript = Transcript::new(b"snark_example");
  let proof = SNARK::prove(
    ctk.input_block_num,
    ctk.output_block_num,
    &ctk.input_liveness,
    ctk.func_input_width,
    ctk.input_offset,
    ctk.output_offset,
    &rtk.input,
    &rtk.output,
    rtk.output_exec_num,
    num_vars,
    num_ios,
    max_block_num_phy_ops,
    &block_num_phy_ops,
    max_block_num_vir_ops,
    &block_num_vir_ops,
    mem_addr_ts_bits_size,
    num_inputs_unpadded,
    &ctk.num_vars_per_block,
    block_num_instances_bound,
    rtk.block_max_num_proofs,
    &block_num_proofs,
    &mut block_inst,
    &block_comm_map,
    &block_comm_list,
    &block_decomm_list,
    rtk.consis_num_proofs,
    rtk.total_num_init_phy_mem_accesses,
    rtk.total_num_init_vir_mem_accesses,
    rtk.total_num_phy_mem_accesses,
    rtk.total_num_vir_mem_accesses,
    &mut pairwise_check_inst,
    &pairwise_check_comm,
    &pairwise_check_decomm,
    block_vars_matrix,
    rtk.exec_inputs,
    rtk.init_phy_mems_list,
    rtk.init_vir_mems_list,
    rtk.addr_phy_mems_list,
    rtk.addr_vir_mems_list,
    rtk.addr_ts_bits_list,
    &perm_root_inst,
    &perm_root_comm,
    &perm_root_decomm,
    &mut prover_transcript,
  );

  println!("Verifying the proof...");
  // verify the proof of satisfiability
  let mut verifier_transcript = Transcript::new(b"snark_example");
  assert!(proof
    .verify(
      ctk.input_block_num,
      ctk.output_block_num,
      &ctk.input_liveness,
      ctk.func_input_width,
      ctk.input_offset,
      ctk.output_offset,
      &rtk.input,
      &rtk.input_stack,
      &rtk.input_mem,
      &rtk.output,
      rtk.output_exec_num,
      num_vars,
      num_ios,
      max_block_num_phy_ops,
      &block_num_phy_ops,
      max_block_num_vir_ops,
      &block_num_vir_ops,
      mem_addr_ts_bits_size,
      num_inputs_unpadded,
      &ctk.num_vars_per_block,
      block_num_instances_bound,
      rtk.block_max_num_proofs,
      &block_num_proofs,
      block_num_cons,
      &block_comm_map,
      &block_comm_list,
      rtk.consis_num_proofs,
      rtk.total_num_init_phy_mem_accesses,
      rtk.total_num_init_vir_mem_accesses,
      rtk.total_num_phy_mem_accesses,
      rtk.total_num_vir_mem_accesses,
      pairwise_check_num_cons,
      &pairwise_check_comm,
      perm_root_num_cons,
      &perm_root_comm,
      &mut verifier_transcript
    )
    .is_ok());
  println!("proof verification successful!");
}
