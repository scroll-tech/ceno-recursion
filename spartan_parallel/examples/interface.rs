//! Reads in constraints and inputs from zok_tests/constraints and zok_tests/inputs
//! Used as a temporary interface to / from CirC
#![allow(clippy::assertions_on_result_states)]
use std::{fs::File, io::BufReader};
use std::io::{BufRead, Read};
use std::{default, env};

use libspartan::{
  instance::Instance, 
  /* TODO: Alternative PCS
  SNARKGens, 
  */
  VarsAssignment, SNARK, InputsAssignment, MemsAssignment
};
use merlin::Transcript;
use std::time::*;
use serde::{Serialize, Deserialize};

const TOTAL_NUM_VARS_BOUND: usize = 10000000;

/*
// Convert a string of numbers separated by spaces into a vector
fn string_to_vec(buffer: String) -> Vec<usize> {
  let split: Vec<String> = buffer.split(' ').map(|i| i.to_string().trim().to_string()).collect();
  let mut list = Vec::new();
  for s in split {
    if s != "" {
      list.push(s.parse::<usize>().unwrap());
    }
  }
  list
}

// Convert a string of bytes separated by spaces into a vector
fn string_to_bytes(buffer: String) -> [u8; 32] {
  let split: Vec<String> = buffer.split(' ').map(|i| i.to_string().trim().to_string()).collect();
  let mut list = [0; 32];
  let mut count = 0;
  for s in &split {
    if s != "" {
      list[count] = s.parse::<u8>().unwrap();
    }
    count += 1;
  }
  list
}
*/

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

  args: Vec<Vec<(Vec<(usize, [u8; 32])>, Vec<(usize, [u8; 32])>, Vec<(usize, [u8; 32])>)>>,

  input_liveness: Vec<bool>,
  func_input_width: usize,
  input_offset: usize,
  input_block_num: usize,
  output_offset: usize,
  output_block_num: usize
}

impl CompileTimeKnowledge {
  fn deserialize_from_file(benchmark_name: String) -> CompileTimeKnowledge {
    let file_name = format!("../zok_tests/constraints/{}_bin.ctk", benchmark_name);
    let mut f = File::open(file_name).unwrap();
    let mut content: Vec<u8> = Vec::new();
    f.read_to_end(&mut content).unwrap();
    bincode::deserialize(&content).unwrap()
  }
  
  /* Archived & Outdated
  fn read_from_file(benchmark_name: String) -> std::io::Result<CompileTimeKnowledge> {
    let file_name = format!("../zok_tests/constraints/{}.ctk", benchmark_name);
    let f = File::open(file_name)?;
    let mut reader = BufReader::new(f);
    let mut buffer = String::new();

    let (block_num_instances, num_vars, num_inputs_unpadded, num_vars_per_block, block_num_phy_ops, block_num_vir_ops, max_ts_width) = {
      reader.read_line(&mut buffer)?;
      let block_num_instances = buffer.trim().parse::<usize>().unwrap();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let num_vars = buffer.trim().parse::<usize>().unwrap();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let num_inputs_unpadded = buffer.trim().parse::<usize>().unwrap();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let num_vars_per_block: Vec<usize> = string_to_vec(buffer.clone());
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let block_num_phy_ops: Vec<usize> = string_to_vec(buffer.clone());
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let block_num_vir_ops: Vec<usize> = string_to_vec(buffer.clone());
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let max_ts_width = buffer.trim().parse::<usize>().unwrap();
      (block_num_instances, num_vars, num_inputs_unpadded, num_vars_per_block, block_num_phy_ops, block_num_vir_ops, max_ts_width)
    };

    let mut args = vec![Vec::new(); block_num_instances];
    let mut inst_counter: usize = 0;
    let mut cons_counter: usize = 0;
    buffer.clear();
    reader.read_line(&mut buffer)?;
    assert_eq!(buffer, "INST 0\n".to_string());
    buffer.clear();
    reader.read_line(&mut buffer)?;
    assert_eq!(buffer, format!("A\n"));
    args[inst_counter].push((Vec::new(), Vec::new(), Vec::new()));
    // Use mat to indicate which matrix we are dealing with
    // 0 - A; 1 - B; 2 - C
    let mut mat = 0;
    buffer.clear();
    reader.read_line(&mut buffer)?;
    while buffer != format!("INST_END\n") {
      if buffer == format!("INST {}\n", inst_counter + 1) {
        inst_counter += 1;
        buffer.clear();
        reader.read_line(&mut buffer)?;
        assert_eq!(buffer, format!("A\n"));
        args[inst_counter].push((Vec::new(), Vec::new(), Vec::new()));
        cons_counter = 0;
        mat = 0;
      } else if buffer == format!("A\n") {
        args[inst_counter].push((Vec::new(), Vec::new(), Vec::new()));
        cons_counter += 1;
        mat = 0;
      } else if buffer == format!("B\n") {
        mat = 1;
      } else if buffer == format!("C\n") {
        mat = 2;
      } else {
        // Must be a line of a single number denoting variable and a [u8; 32] denoting the coefficient
        let var = buffer.trim().parse::<usize>().unwrap();
        buffer.clear();
        reader.read_line(&mut buffer)?;
        let val = string_to_bytes(buffer.clone());
        match mat {
          0 => { args[inst_counter][cons_counter].0.push((var, val)); }
          1 => { args[inst_counter][cons_counter].1.push((var, val)); }
          2 => { args[inst_counter][cons_counter].2.push((var, val)); }
          _ => { panic!("Invalid matrix: {}", mat) }
        }
      }
      buffer.clear();
      reader.read_line(&mut buffer)?;
    }
    buffer.clear();
    reader.read_line(&mut buffer)?;
    let func_input_width = buffer.trim().parse::<usize>().unwrap();
    buffer.clear();
    reader.read_line(&mut buffer)?;
    let input_offset = buffer.trim().parse::<usize>().unwrap();
    buffer.clear();
    reader.read_line(&mut buffer)?;
    let input_block_num = buffer.trim().parse::<usize>().unwrap();
    buffer.clear();
    reader.read_line(&mut buffer)?;
    let output_offset = buffer.trim().parse::<usize>().unwrap();
    buffer.clear();
    reader.read_line(&mut buffer)?;
    let output_block_num = buffer.trim().parse::<usize>().unwrap();

    Ok(CompileTimeKnowledge {
      block_num_instances,
      num_vars,
      num_inputs_unpadded,
      num_vars_per_block,
      block_num_phy_ops,
      block_num_vir_ops,
      max_ts_width,
      args,
      func_input_width,
      input_offset,
      input_block_num,
      output_offset,
      output_block_num
    })
  }
  */
}

// Everything provided by the prover
#[derive(Serialize, Deserialize)]
struct RunTimeKnowledge {
  block_max_num_proofs: usize,
  block_num_proofs: Vec<usize>,
  consis_num_proofs: usize,
  total_num_init_phy_mem_accesses: usize,
  total_num_init_vir_mem_accesses: usize,
  total_num_phy_mem_accesses: usize,
  total_num_vir_mem_accesses: usize,

  block_vars_matrix: Vec<Vec<VarsAssignment>>,
  exec_inputs: Vec<InputsAssignment>,
  init_phy_mems_list: Vec<MemsAssignment>,
  init_vir_mems_list: Vec<MemsAssignment>,
  addr_phy_mems_list: Vec<MemsAssignment>,
  addr_vir_mems_list: Vec<MemsAssignment>,
  addr_ts_bits_list: Vec<MemsAssignment>,

  input: Vec<[u8; 32]>,
  input_stack: Vec<[u8; 32]>,
  input_mem: Vec<[u8; 32]>,
  output: [u8; 32],
  output_exec_num: usize
}

impl RunTimeKnowledge {
  fn deserialize_from_file(benchmark_name: String) -> RunTimeKnowledge {
    let file_name = format!("../zok_tests/inputs/{}_bin.rtk", benchmark_name);
    let mut f = File::open(file_name).unwrap();
    let mut content: Vec<u8> = Vec::new();
    f.read_to_end(&mut content).unwrap();
    bincode::deserialize(&content).unwrap()
  }

  /* Archived
  fn read_from_file(benchmark_name: String) -> std::io::Result<RunTimeKnowledge> {
    let file_name = format!("../zok_tests/inputs/{}.rtk", benchmark_name);
    let f = File::open(file_name)?;
    let mut reader = BufReader::new(f);
    let mut buffer = String::new();

    let (block_max_num_proofs, block_num_proofs, consis_num_proofs, total_num_init_mem_accesses, total_num_phy_mem_accesses, total_num_vir_mem_accesses) = {
      reader.read_line(&mut buffer)?;
      let block_max_num_proofs = buffer.trim().parse::<usize>().unwrap();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let block_num_proofs = string_to_vec(buffer.clone());
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let consis_num_proofs = buffer.trim().parse::<usize>().unwrap();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let total_num_init_mem_accesses = buffer.trim().parse::<usize>().unwrap();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let total_num_phy_mem_accesses = buffer.trim().parse::<usize>().unwrap();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let total_num_vir_mem_accesses = buffer.trim().parse::<usize>().unwrap();
      (block_max_num_proofs, block_num_proofs, consis_num_proofs, total_num_init_mem_accesses, total_num_phy_mem_accesses, total_num_vir_mem_accesses)
    };
    
    let block_vars_matrix: Vec<Vec<VarsAssignment>> = {
      let mut block_vars_matrix = vec![Vec::new()];
      buffer.clear();
      reader.read_line(&mut buffer)?;
      assert_eq!(buffer, "BLOCK_VARS\n".to_string());
      buffer.clear();
      reader.read_line(&mut buffer)?;
      assert_eq!(buffer, "BLOCK 0\n".to_string());

      let mut block_counter = 0;
      let mut exec_counter = 0;
      buffer.clear();
      reader.read_line(&mut buffer)?;
      while buffer != "EXEC_INPUTS\n".to_string() {
        if buffer == format!("BLOCK {}\n", block_counter + 1) {
          block_counter += 1;
          exec_counter = 0;
          block_vars_matrix.push(Vec::new());
        } else if buffer == format!("EXEC 0\n") {
          block_vars_matrix[block_counter].push(Vec::new());
        } else if buffer == format!("EXEC {}\n", exec_counter + 1) {
          block_vars_matrix[block_counter].push(Vec::new());
          exec_counter += 1;
        } else {
          block_vars_matrix[block_counter][exec_counter].push(string_to_bytes(buffer.clone()));
        }
        buffer.clear();
        reader.read_line(&mut buffer)?;
      }
      block_vars_matrix.iter().map(|i| i.iter().map(|j| VarsAssignment::new(j).unwrap()).collect()).collect()
    };

    let exec_inputs: Vec<InputsAssignment> = {
      let mut exec_inputs = vec![Vec::new()];
      buffer.clear();
      reader.read_line(&mut buffer)?;
      assert_eq!(buffer, "EXEC 0\n".to_string());

      let mut exec_counter = 0;
      buffer.clear();
      reader.read_line(&mut buffer)?;
      while buffer != "INIT_MEMS\n".to_string() {
        if buffer == format!("EXEC {}\n", exec_counter + 1) {
          exec_inputs.push(Vec::new());
          exec_counter += 1;
        } else {
          exec_inputs[exec_counter].push(string_to_bytes(buffer.clone()));
        }
        buffer.clear();
        reader.read_line(&mut buffer)?;
      }

      exec_inputs.iter().map(|i| InputsAssignment::new(i).unwrap()).collect()
    };

    let init_mems_list: Vec<MemsAssignment> = {
      let mut init_mems_list = vec![Vec::new()];
      buffer.clear();
      reader.read_line(&mut buffer)?;
      
      let mut access_counter = 0;
      while buffer != "ADDR_PHY_MEMS\n".to_string() {
        if buffer == format!("ACCESS {}\n", access_counter + 1) {
          access_counter += 1;
          init_mems_list.push(Vec::new());
        } else if buffer == format!("ACCESS 0\n") {
        } else {
          init_mems_list[access_counter].push(string_to_bytes(buffer.clone()));
        }
        buffer.clear();
        reader.read_line(&mut buffer)?;
      }
      init_mems_list.iter().map(|i| InputsAssignment::new(i).unwrap()).collect()
    };

    let addr_phy_mems_list: Vec<MemsAssignment> = {
      let mut addr_phy_mems_list = vec![Vec::new()];
      buffer.clear();
      reader.read_line(&mut buffer)?;
      
      let mut access_counter = 0;
      while buffer != "ADDR_VIR_MEMS\n".to_string() {
        if buffer == format!("ACCESS {}\n", access_counter + 1) {
          access_counter += 1;
          addr_phy_mems_list.push(Vec::new());
        } else if buffer == format!("ACCESS 0\n") {
        } else {
          addr_phy_mems_list[access_counter].push(string_to_bytes(buffer.clone()));
        }
        buffer.clear();
        reader.read_line(&mut buffer)?;
      }
      addr_phy_mems_list.iter().map(|i| InputsAssignment::new(i).unwrap()).collect()
    };

    let addr_vir_mems_list: Vec<MemsAssignment> = {
      let mut addr_vir_mems_list = vec![Vec::new()];
      buffer.clear();
      reader.read_line(&mut buffer)?;
      
      let mut access_counter = 0;
      while buffer != "ADDR_VM_BITS\n".to_string() {
        if buffer == format!("ACCESS {}\n", access_counter + 1) {
          access_counter += 1;
          addr_vir_mems_list.push(Vec::new());
        } else if buffer == format!("ACCESS 0\n") {
        } else {
          addr_vir_mems_list[access_counter].push(string_to_bytes(buffer.clone()));
        }
        buffer.clear();
        reader.read_line(&mut buffer)?;
      }
      addr_vir_mems_list.iter().map(|i| InputsAssignment::new(i).unwrap()).collect()
    };

    let addr_ts_bits_list: Vec<MemsAssignment> = {
      let mut addr_ts_bits_list = vec![Vec::new()];
      buffer.clear();
      reader.read_line(&mut buffer)?;
      
      let mut access_counter = 0;
      while buffer != "INPUTS\n".to_string() {
        if buffer == format!("ACCESS {}\n", access_counter + 1) {
          access_counter += 1;
          addr_ts_bits_list.push(Vec::new());
        } else if buffer == format!("ACCESS 0\n") {
        } else {
          addr_ts_bits_list[access_counter].push(string_to_bytes(buffer.clone()));
        }
        buffer.clear();
        reader.read_line(&mut buffer)?;
      }
      addr_ts_bits_list.iter().map(|i| InputsAssignment::new(i).unwrap()).collect()
    };

    let func_inputs = {
      let mut func_inputs = Vec::new();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      while buffer != "INPUT_MEMS\n".to_string() {
        func_inputs.push(string_to_bytes(buffer.clone()));
        buffer.clear();
        reader.read_line(&mut buffer)?;
      }
      func_inputs
    };

    let input_mem = {
      let mut input_mem = Vec::new();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      while buffer != "OUTPUTS\n".to_string() {
        input_mem.push(string_to_bytes(buffer.clone()));
        buffer.clear();
        reader.read_line(&mut buffer)?;
      }
      input_mem
    };

    let func_outputs = {
      let mut func_outputs = Vec::new();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      while buffer != "OUTPUTS_END\n".to_string() {
        func_outputs.push(string_to_bytes(buffer.clone()));
        buffer.clear();
        reader.read_line(&mut buffer)?;
      }
      func_outputs
    };

    buffer.clear();
    reader.read_line(&mut buffer)?;
    let output_exec_num = buffer.trim().parse::<usize>().unwrap();

    Ok(RunTimeKnowledge {
      block_max_num_proofs,
      block_num_proofs,
      consis_num_proofs,
      total_num_init_mem_accesses,
      total_num_phy_mem_accesses,
      total_num_vir_mem_accesses,
    
      block_vars_matrix,
      exec_inputs,
      init_mems_list,
      addr_phy_mems_list,
      addr_vir_mems_list,
      addr_ts_bits_list,
    
      input: func_inputs,
      input_mem,
      output: func_outputs[0],
      output_exec_num
    })
  }
  */
}

fn main() {
  let benchmark_name = &env::args().collect::<Vec<String>>()[1];
  // let ctk = CompileTimeKnowledge::read_from_file(benchmark_name.to_string()).unwrap();
  let ctk = CompileTimeKnowledge::deserialize_from_file(benchmark_name.to_string());
  // let rtk = RunTimeKnowledge::read_from_file(benchmark_name.to_string()).unwrap();
  let rtk = RunTimeKnowledge::deserialize_from_file(benchmark_name.to_string());

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
  let (block_num_vars, block_num_cons, block_num_non_zero_entries, mut block_inst) = Instance::gen_block_inst::<true>(
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
  let (pairwise_check_num_vars, pairwise_check_num_cons, pairwise_check_num_non_zero_entries, mut pairwise_check_inst) = Instance::gen_pairwise_check_inst::<true>(
    ctk.max_ts_width, 
    mem_addr_ts_bits_size,
    rtk.consis_num_proofs,
    rtk.total_num_phy_mem_accesses,
    rtk.total_num_vir_mem_accesses,
  );
  println!("Finished Pairwise");

  // PERM INSTANCES
  // PERM_ROOT
  let (perm_root_num_cons, perm_root_num_non_zero_entries, perm_root_inst) = Instance::gen_perm_root_inst::<true>(
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

  /* TODO: Alternative PCS
  // produce public parameters
  let block_gens = SNARKGens::new(block_num_cons, block_num_vars, block_num_instances_bound, block_num_non_zero_entries);
  let pairwise_check_gens = SNARKGens::new(pairwise_check_num_cons, 4 * pairwise_check_num_vars, 3, pairwise_check_num_non_zero_entries);
  let perm_root_gens = SNARKGens::new(perm_root_num_cons, 8 * num_ios, 1, perm_root_num_non_zero_entries);
  // Only use one version of gens_r1cs_sat
  let vars_gens = SNARKGens::new(block_num_cons, TOTAL_NUM_VARS_BOUND, block_num_instances_bound.next_power_of_two(), block_num_non_zero_entries).gens_r1cs_sat;
  */
  
  // create a commitment to the R1CS instance
  println!("Comitting Circuits...");
  // block_comm_map records the sparse_polys committed in each commitment
  // Note that A, B, C are committed separately, so sparse_poly[3*i+2] corresponds to poly C of instance i
  let (block_comm_map, block_comm_list, block_decomm_list) = 
    /* TODO: Alternative PCS
    SNARK::multi_encode(&block_inst, &block_gens);
    */
    SNARK::multi_encode(&block_inst);
  println!("Finished Block");
  let (pairwise_check_comm, pairwise_check_decomm) = 
    /* TODO: Alternative PCS
    SNARK::encode(&pairwise_check_inst, &pairwise_check_gens);
    */
    SNARK::encode(&pairwise_check_inst);
  println!("Finished Pairwise");
  let (perm_root_comm, perm_root_decomm) = 
    /* TODO: Alternative PCS
    SNARK::encode(&perm_root_inst, &perm_root_gens);
    */
    SNARK::encode(&perm_root_inst);
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
    /* TODO: Alternative PCS
    &block_gens,
    */
    
    rtk.consis_num_proofs,
    rtk.total_num_init_phy_mem_accesses,
    rtk.total_num_init_vir_mem_accesses,
    rtk.total_num_phy_mem_accesses,
    rtk.total_num_vir_mem_accesses,
    &mut pairwise_check_inst,
    &pairwise_check_comm,
    &pairwise_check_decomm,
    /* TODO: Alternative PCS
    &pairwise_check_gens,
    */

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
    /* TODO: Alternative PCS
    &perm_root_gens,
    */

    /* TODO: Alternative PCS
    &vars_gens,
    */
    &mut prover_transcript,
  );

  println!("Verifying the proof...");
  // verify the proof of satisfiability
  let mut verifier_transcript = Transcript::new(b"snark_example");
  assert!(proof.verify(
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
    /* TODO: Alternative PCS
    &block_gens,
    */

    rtk.consis_num_proofs, 
    rtk.total_num_init_phy_mem_accesses,
    rtk.total_num_init_vir_mem_accesses,
    rtk.total_num_phy_mem_accesses,
    rtk.total_num_vir_mem_accesses,
    pairwise_check_num_cons,
    &pairwise_check_comm,
    /* TODO: Alternative PCS
    &pairwise_check_gens,
    */

    perm_root_num_cons,
    &perm_root_comm,
    /* TODO: Alternative PCS
    &perm_root_gens,
    */

    /* TODO: Alternative PCS
    &vars_gens,
    */
    &mut verifier_transcript
  ).is_ok());
  println!("proof verification successful!");
}
