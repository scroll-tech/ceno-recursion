#![allow(non_snake_case)]
#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![allow(clippy::assertions_on_result_states)]
#![feature(associated_type_defaults)]

// TODO: Can we allow split in R1CSGens?
// TODO: Can we parallelize the proofs?
// TODO: Problem when there is only one block & one execution

extern crate byteorder;
extern crate core;
extern crate curve25519_dalek;
extern crate digest;
extern crate merlin;
extern crate rand;
extern crate sha3;
extern crate rayon;

mod custom_dense_mlpoly;
mod dense_mlpoly;
mod errors;
/// R1CS instance used by libspartan
pub mod instance;
mod math;
mod product_tree;
mod r1csinstance;
mod r1csproof;
mod random;
/// Byte conversion utilities for field elements
pub mod bytes;
mod sparse_mlpoly;
mod sumcheck;
mod timer;
/// Transcript
pub mod transcript;
mod unipoly;

use std::{
  cmp::{max, Ordering},
  fs::File,
  io::Write,
};

use dense_mlpoly::{DensePolynomial, PolyEvalProof};
use errors::{ProofVerifyError, R1CSError};
use instance::Instance;
use itertools::Itertools;
use math::Math;
use multilinear_extensions::mle::DenseMultilinearExtension;
use mpcs::{PolynomialCommitmentScheme, ProverParam};
use r1csinstance::{R1CSCommitment, R1CSDecommitment, R1CSEvalProof, R1CSInstance};
use r1csproof::R1CSProof;
use random::RandomTape;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use ff_ext::ExtensionField;
use serde::{Deserialize, Serialize};
use timer::Timer;
use bytes::{from_bytes, to_bytes};
use transcript::{Transcript, append_protocol_name, append_field_to_transcript, append_field_vector_to_transcript, challenge_scalar};

const INIT_PHY_MEM_WIDTH: usize = 4;
const INIT_VIR_MEM_WIDTH: usize = 4;
const PHY_MEM_WIDTH: usize = 4;
const VIR_MEM_WIDTH: usize = 8;
const W3_WIDTH: usize = 8;

/// `ComputationCommitment` holds a public preprocessed NP statement (e.g., R1CS)
#[derive(Clone, Serialize)]
pub struct ComputationCommitment<E: ExtensionField> {
  comm: R1CSCommitment<E>,
}

/// `ComputationDecommitment` holds information to decommit `ComputationCommitment`
pub struct ComputationDecommitment<E: ExtensionField> {
  decomm: R1CSDecommitment<E>,
}

/// `Assignment` holds an assignment of values to either the inputs or variables in an `Instance`
#[derive(Clone, Serialize, Deserialize)]
pub struct Assignment<E: ExtensionField> {
  /// Entries of an assignment
  pub assignment: Vec<E>,
}

impl<E: ExtensionField> Assignment<E> {
  /// Constructs a new `Assignment` from a vector
  pub fn new(assignment: &[[u8; 32]]) -> Result<Assignment<E>, R1CSError> {
    let bytes_to_scalar = |vec: &[[u8; 32]]| -> Result<Vec<E>, R1CSError> {
      let mut vec_scalar: Vec<E> = Vec::new();
      for v in vec {
        let val = from_bytes(v);
        if val.is_some().unwrap_u8() == 1 {
          vec_scalar.push(val.unwrap());
        } else {
          return Err(R1CSError::InvalidScalar);
        }
      }
      Ok(vec_scalar)
    };
    let assignment_scalar = bytes_to_scalar(assignment);

    // check for any parsing errors
    if assignment_scalar.is_err() {
      return Err(R1CSError::InvalidScalar);
    }

    Ok(Assignment {
      assignment: assignment_scalar.unwrap(),
    })
  }

  /// Write the assignment into a file
  pub fn write(&self, f: &File) -> std::io::Result<()> {
    for assg in &self.assignment {
      write_bytes(f, &to_bytes(*assg))?;
    }
    Ok(())
  }
}

fn write_bytes(mut f: &File, bytes: &[u8; 32]) -> std::io::Result<()> {
  // Disregard the trailing zeros
  let mut size = 32;
  while size > 0 && bytes[size - 1] == 0 {
    size -= 1;
  }
  for i in 0..size {
    write!(&mut f, "{} ", bytes[i])?;
  }
  writeln!(&mut f)?;
  Ok(())
}

/// `VarsAssignment` holds an assignment of values to variables in an `Instance`
pub type VarsAssignment<E> = Assignment<E>;

/// `InputsAssignment` holds an assignment of values to inputs in an `Instance`
pub type InputsAssignment<E> = Assignment<E>;

/// `MemsAssignment` holds an assignment of values to (addr, val) pairs in an `Instance`
pub type MemsAssignment<E> = Assignment<E>;

// IOProofs contains a series of proofs that the committed values match the input and output of the program
#[derive(Serialize, Deserialize, Debug)]
struct IOProofs<E: ExtensionField> {
  // The prover needs to prove:
  // 1. Input and output block are both valid
  // 2. Block number of the input and output block are correct
  // 3. Input and outputs are correct
  // 4. The constant value of the input is 1
  proofs: Vec<PolyEvalProof<E>>,
}

impl<E: ExtensionField> IOProofs<E> {
  // Given the polynomial in execution order, generate all proofs
  fn prove(
    exec_poly_inputs: &DensePolynomial<E>,

    num_ios: usize,
    num_inputs_unpadded: usize,
    num_proofs: usize,
    input_block_num: E,
    output_block_num: E,

    input_liveness: &Vec<bool>,
    input_offset: usize,
    output_offset: usize,
    input: Vec<E>,
    output: E,
    output_exec_num: usize,
    transcript: &mut Transcript<E>,
    random_tape: &mut RandomTape<E>,
  ) -> IOProofs<E> {
    let r_len = (num_proofs * num_ios).log_2();
    let to_bin_array = |x: usize| {
      (0..r_len)
        .rev()
        .map(|n| (x >> n) & 1)
        .map(|i| E::from(i as u64))
        .collect::<Vec<E>>()
    };

    // input indices are 6(%SP) ++ 5(%AS) ++ [2 + input_offset..](others)
    // Filter out all dead inputs
    let mut input_indices: Vec<usize> = (0..input_liveness.len() - 2)
      .map(|i| 2 + input_offset + i)
      .collect();
    if input_liveness[1] {
      // %AS is alive, add entry 5
      input_indices.insert(0, 5);
    }
    if input_liveness[0] {
      // %SP is alive, add entry 6
      input_indices.insert(0, 6);
    }
    assert_eq!(input_liveness.len(), input.len());
    let mut live_input = Vec::new();
    for i in 0..input_liveness.len() {
      if input_liveness[i] {
        live_input.push(input[i].clone());
      }
    }
    input_indices = input_indices[..live_input.len()].to_vec();

    // batch prove all proofs
    let proofs = PolyEvalProof::prove_batched_points(
      exec_poly_inputs,
      [
        vec![
          0,                         // input valid
          output_exec_num * num_ios, // output valid
          2,                         // input block num
          output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1), // output block num
          output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1) + output_offset - 1, // output correctness
        ],
        input_indices, // input correctness
      ]
      .concat()
      .iter()
      .map(|i| to_bin_array(*i))
      .collect(),
      vec![
        vec![
          E::ONE,
          E::ONE,
          input_block_num,
          output_block_num,
          output,
        ],
        live_input,
      ]
      .concat(),
      transcript,
      random_tape,
    );
    IOProofs { proofs }
  }

  fn verify(
    &self,
    num_ios: usize,
    num_inputs_unpadded: usize,
    num_proofs: usize,
    input_block_num: E,
    output_block_num: E,

    input_liveness: &Vec<bool>,
    input_offset: usize,
    output_offset: usize,
    input: Vec<E>,
    output: E,
    output_exec_num: usize,
    transcript: &mut Transcript<E>,
  ) -> Result<(), ProofVerifyError> {
    let r_len = (num_proofs * num_ios).log_2();
    let to_bin_array = |x: usize| {
      (0..r_len)
        .rev()
        .map(|n| (x >> n) & 1)
        .map(|i| E::from(i as u64))
        .collect::<Vec<E>>()
    };

    // input indices are 6(%SP) ++ 5(%AS) ++ [2 + input_offset..](others)
    // Filter out all dead inputs
    let mut input_indices: Vec<usize> = (0..input_liveness.len() - 2)
      .map(|i| 2 + input_offset + i)
      .collect();
    if input_liveness[1] {
      // %AS is alive, add entry 5
      input_indices.insert(0, 5);
    }
    if input_liveness[0] {
      // %SP is alive, add entry 6
      input_indices.insert(0, 6);
    }
    assert_eq!(input_liveness.len(), input.len());
    let mut live_input = Vec::new();
    for i in 0..input_liveness.len() {
      if input_liveness[i] {
        live_input.push(input[i].clone());
      }
    }
    input_indices = input_indices[..live_input.len()].to_vec();

    // batch verify all proofs
    PolyEvalProof::verify_plain_batched_points(
      &self.proofs,
      transcript,
      [
        vec![
          0,                                                                             // input valid
          output_exec_num * num_ios, // output valid
          2,                         // input block num
          output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1), // output block num
          output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1) + output_offset - 1, // output correctness
        ],
        input_indices, // input correctness
      ]
      .concat()
      .iter()
      .map(|i| to_bin_array(*i))
      .collect(),
      vec![
        vec![
          E::ONE,
          E::ONE,
          input_block_num,
          output_block_num,
          output,
        ],
        live_input,
      ]
      .concat(),
    )
  }
}

// ShiftProofs contains a series of proofs and openings that a list of polynomials / commitments are indeed shifts of another list of polynomials
// We do so by treating both polynomials as univariate and evaluate on a single point C
// Finally, show shifted(C) = orig(C) * C^(shift_size) + rc * openings, where rc * openings are the first few entries of the original poly dot product with the power series of C
#[derive(Serialize, Deserialize, Debug)]
struct ShiftProofs<E: ExtensionField> {
  proof: PolyEvalProof<E>,
}

impl<E: ExtensionField> ShiftProofs<E> {
  fn prove(
    orig_polys: Vec<&DensePolynomial<E>>,
    shifted_polys: Vec<&DensePolynomial<E>>,
    // For each orig_poly, how many entries at the front of proof 0 are non-zero?
    header_len_list: Vec<usize>,
    transcript: &mut Transcript<E>,
    random_tape: &mut RandomTape<E>,
  ) -> ShiftProofs<E> {
    // Assert that all polynomials are of the same size
    let num_instances = orig_polys.len();
    assert_eq!(num_instances, shifted_polys.len());
    let max_poly_size = orig_polys
      .iter()
      .fold(0, |m, p| if p.len() > m { p.len() } else { m });
    let max_poly_size =
      shifted_polys
        .iter()
        .fold(max_poly_size, |m, p| if p.len() > m { p.len() } else { m });
    // Open entry 0..header_len_list[p] - 1
    for p in 0..num_instances {
      for _i in 0..header_len_list[p] {}
    }
    let c = challenge_scalar(transcript, b"challenge_c");
    let mut rc = Vec::new();
    let mut next_c = E::ONE;
    for _ in 0..max_poly_size {
      rc.push(next_c);
      next_c = next_c * c;
    }
    let mut orig_evals = Vec::new();
    let mut shifted_evals = Vec::new();

    for p in 0..num_instances {
      let orig_poly = orig_polys[p];
      let shifted_poly = shifted_polys[p];
      let orig_eval = (0..orig_poly.len()).fold(E::ZERO, |a, b| a + orig_poly[b] * rc[b]);
      let shifted_eval =
        (0..shifted_poly.len()).fold(E::ZERO, |a, b| a + shifted_poly[b] * rc[b]);
      orig_evals.push(orig_eval);
      shifted_evals.push(shifted_eval);
    }
    let addr_phy_mems_shift_proof = PolyEvalProof::prove_uni_batched_instances(
      &[orig_polys, shifted_polys].concat(),
      &c,
      &[orig_evals, shifted_evals].concat(),
      transcript,
      random_tape,
    );

    ShiftProofs {
      proof: addr_phy_mems_shift_proof,
    }
  }

  fn verify(
    &self,
    poly_size_list: Vec<usize>,
    shift_size_list: Vec<usize>,
    // For each orig_poly, how many entries at the front of proof 0 are non-zero?
    header_len_list: Vec<usize>,
    transcript: &mut Transcript<E>,
  ) -> Result<(), ProofVerifyError> {
    let num_instances = header_len_list.len();

    // Open entry 0..header_len_list[p] - 1
    for p in 0..num_instances {
      for _i in 0..header_len_list[p] {}
    }
    let max_shift_size = shift_size_list
      .iter()
      .fold(0, |m, i| if *i > m { *i } else { m });
    let c = challenge_scalar(transcript, b"challenge_c");
    let mut rc = Vec::new();
    let mut next_c = E::ONE;
    for _ in 0..max_shift_size + 1 {
      rc.push(next_c);
      next_c = next_c * c;
    }

    // Proof of opening
    self.proof.verify_uni_batched_instances(
      transcript,
      &c,
      [poly_size_list.clone(), poly_size_list].concat(),
    )?;
    Ok(())
  }
}

// Information regarding one witness sec
#[derive(Clone)]
struct ProverWitnessSecInfo<E: ExtensionField, Pcs: PolynomialCommitmentScheme<E>> {
  // Number of inputs per block
  num_inputs: Vec<usize>,
  // num_instances x num_proofs x num_inputs hypermatrix for all values
  w_mat: Vec<Vec<Vec<E>>>,
  // One polynomial per instance
  poly_w: Vec<DenseMultilinearExtension<E>>,
  comm_w: Vec<Pcs::CommitmentWithWitness>,
}

impl<E: ExtensionField, Pcs: PolynomialCommitmentScheme<E>> ProverWitnessSecInfo<E, Pcs> {
  fn new(w_mat: Vec<Vec<Vec<E>>>, poly_w: Vec<DenseMultilinearExtension<E>>, comm_w: Vec<Pcs::CommitmentWithWitness>) -> ProverWitnessSecInfo<E, Pcs> {
    ProverWitnessSecInfo {
      num_inputs: w_mat.iter().map(|i| i[0].len()).collect(),
      w_mat,
      poly_w,
      comm_w,
    }
  }

  // Empty ProverWitnessSecInfo
  fn dummy() -> ProverWitnessSecInfo<E, Pcs> {
    ProverWitnessSecInfo {
      num_inputs: Vec::new(),
      w_mat: Vec::new(),
      poly_w: Vec::new(),
      comm_w: Vec::new(),
    }
  }

  // Zero ProverWitnessSecInfo
  fn pad() -> ProverWitnessSecInfo<E, Pcs> {
    let ZERO = E::ZERO;
    ProverWitnessSecInfo {
      num_inputs: vec![1],
      w_mat: vec![vec![vec![ZERO]]],
      poly_w: Vec::new(),
      comm_w: Vec::new(),
    }
  }

  // Concatenate the components in the given order to a new prover witness sec
  fn concat(components: Vec<&ProverWitnessSecInfo<E, Pcs>>) -> ProverWitnessSecInfo<E, Pcs> {
    let mut num_inputs = Vec::new();
    let mut w_mat = Vec::new();
    let mut poly_w = Vec::new();
    let mut comm_w = Vec::new();

    for c in components {
      num_inputs.extend(c.num_inputs.clone());
      w_mat.extend(c.w_mat.clone());
      poly_w.extend(c.poly_w.clone());
      comm_w.extend(c.comm_w.clone());
    }

    ProverWitnessSecInfo {
      num_inputs,
      w_mat,
      poly_w,
      comm_w,
    }
  }

  // Merge multiple ProverWitnessSec, sort them by decreasing number of proofs
  // Assume all components are sorted
  // Returns: 1. the merged ProverWitnessSec,
  //          2. for each instance in the merged ProverWitnessSec, the component it orignally belongs to
  fn merge(components: Vec<&ProverWitnessSecInfo<E, Pcs>>) -> (ProverWitnessSecInfo<E, Pcs>, Vec<usize>) {
    // Merge algorithm with pointer on each component
    let mut pointers = vec![0; components.len()];
    let merged_size = components.iter().map(|c| c.num_inputs.len()).sum();
    // Map from instances of the merged ProverWitnessSec to each component
    let mut inst_map = Vec::new();
    let mut merged_num_inputs = Vec::new();
    let mut merged_w_mat = Vec::new();
    let mut merged_poly_w = Vec::new();
    let mut merged_comm_w = Vec::new();
    while inst_map.len() < merged_size {
      // Choose the next instance with the most proofs
      let mut next_max_num_proofs = 0;
      let mut next_component = 0;
      for i in 0..components.len() {
        if pointers[i] < components[i].w_mat.len() {
          let next_num_proofs = components[i].w_mat[pointers[i]].len();
          if next_num_proofs > next_max_num_proofs {
            next_max_num_proofs = next_num_proofs;
            next_component = i;
          }
        }
      }
      // Append the selected instance
      inst_map.push(next_component);
      merged_num_inputs.push(components[next_component].num_inputs[pointers[next_component]]);
      merged_w_mat.push(components[next_component].w_mat[pointers[next_component]].clone());
      merged_poly_w.push(components[next_component].poly_w[pointers[next_component]].clone());
      merged_comm_w.push(components[next_component].comm_w[pointers[next_component]].clone());
      pointers[next_component] = pointers[next_component] + 1;
    }

    (
      ProverWitnessSecInfo {
        num_inputs: merged_num_inputs,
        w_mat: merged_w_mat,
        poly_w: merged_poly_w,
        comm_w: merged_comm_w,
      },
      inst_map,
    )
  }
}

// Information regarding one witness sec
#[derive(Clone)]
struct VerifierWitnessSecInfo<E: ExtensionField, Pcs: PolynomialCommitmentScheme<E>> {
  // Number of inputs per block
  num_inputs: Vec<usize>,
  // Number of proofs per block, used by merge
  num_proofs: Vec<usize>,
  // One commitment per circuit
  comm_w: Vec<Pcs::Commitment>
}

impl<E: ExtensionField, Pcs: PolynomialCommitmentScheme<E>> VerifierWitnessSecInfo<E, Pcs> {
  // Unfortunately, cannot obtain all metadata from the commitment
  fn new(num_inputs: Vec<usize>, num_proofs: &Vec<usize>, comm_w: Vec<Pcs::Commitment>) -> VerifierWitnessSecInfo<E, Pcs> {
    let l = num_inputs.len();
    VerifierWitnessSecInfo {
      num_inputs,
      num_proofs: num_proofs[..l].to_vec(),
      comm_w,
    }
  }

  fn dummy() -> VerifierWitnessSecInfo<E, Pcs> {
    VerifierWitnessSecInfo {
      num_inputs: Vec::new(),
      num_proofs: Vec::new(),
      comm_w: Vec::new(),
    }
  }

  fn pad() -> VerifierWitnessSecInfo<E, Pcs> {
    VerifierWitnessSecInfo {
      num_inputs: vec![1],
      num_proofs: vec![1],
      comm_w: Vec::new(),
    }
  }

  // Concatenate the components in the given order to a new verifier witness sec
  fn concat(components: Vec<&VerifierWitnessSecInfo<E, Pcs>>) -> VerifierWitnessSecInfo<E, Pcs> {
    let mut num_inputs = Vec::new();
    let mut num_proofs = Vec::new();
    let mut comm_w = Vec::new();

    for c in components {
      num_inputs.extend(c.num_inputs.clone());
      num_proofs.extend(c.num_proofs.clone());
      comm_w.extend(c.comm_w.clone());
    }

    VerifierWitnessSecInfo {
      num_inputs,
      num_proofs,
      comm_w,
    }
  }

  // Merge multiple VerifierWitnessSec, sort them by decreasing number of proofs
  // Assume all components are sorted
  // Returns: 1. the merged VerifierWitnessSec,
  //          2. for each instance in the merged VerifierWitnessSec, the component it orignally belong to
  fn merge(components: Vec<&VerifierWitnessSecInfo<E, Pcs>>) -> (VerifierWitnessSecInfo<E, Pcs>, Vec<usize>) {
    // Merge algorithm with pointer on each component
    let mut pointers = vec![0; components.len()];
    let merged_size = components.iter().map(|c| c.num_inputs.len()).sum();
    // Map from instances of the merged ProverWitnessSec to each component
    let mut inst_map = Vec::new();
    let mut merged_num_inputs = Vec::new();
    let mut merged_num_proofs = Vec::new();
    let mut merged_comm_w = Vec::new();
    while inst_map.len() < merged_size {
      // Choose the next instance with the most proofs
      let mut next_max_num_proofs = 0;
      let mut next_component = 0;
      for i in 0..components.len() {
        if pointers[i] < components[i].num_proofs.len() {
          let next_num_proofs = components[i].num_proofs[pointers[i]];
          if next_num_proofs > next_max_num_proofs {
            next_max_num_proofs = next_num_proofs;
            next_component = i;
          }
        }
      }
      // Append the selected instance
      inst_map.push(next_component);
      merged_num_inputs.push(components[next_component].num_inputs[pointers[next_component]]);
      merged_num_proofs.push(components[next_component].num_proofs[pointers[next_component]]);
      merged_comm_w.push(components[next_component].comm_w[pointers[next_component]].clone());
      pointers[next_component] = pointers[next_component] + 1;
    }

    (
      VerifierWitnessSecInfo {
        num_inputs: merged_num_inputs,
        num_proofs: merged_num_proofs,
        comm_w: merged_comm_w,
      },
      inst_map,
    )
  }
}

/// `SNARK` holds a proof produced by Spartan SNARK
#[derive(Serialize, Debug)]
pub struct SNARK<E: ExtensionField, Pcs: PolynomialCommitmentScheme<E>> {
  poly_vp: Pcs::VerifierParam,
  block_vars_comm_list: Vec<Pcs::Commitment>,
  exec_inputs_comm: Pcs::Commitment,
  addr_phy_mems_comm: Option<Pcs::Commitment>,
  addr_phy_mems_shifted_comm: Option<Pcs::Commitment>,
  addr_vir_mems_comm: Option<Pcs::Commitment>,
  addr_vir_mems_shifted_comm: Option<Pcs::Commitment>,
  addr_ts_bits_comm: Option<Pcs::Commitment>,

  perm_exec_w2_comm: Pcs::Commitment,
  perm_exec_w3_comm: Pcs::Commitment,
  perm_exec_w3_shifted_comm: Pcs::Commitment,
  block_w2_comm_list: Vec<Pcs::Commitment>,
  block_w3_comm_list: Vec<Pcs::Commitment>,
  block_w3_shifted_comm_list: Vec<Pcs::Commitment>,

  init_phy_mem_w2_comm: Option<Pcs::Commitment>,
  init_phy_mem_w3_comm: Option<Pcs::Commitment>,
  init_phy_mem_w3_shifted_comm: Option<Pcs::Commitment>,
  init_vir_mem_w2_comm: Option<Pcs::Commitment>,
  init_vir_mem_w3_comm: Option<Pcs::Commitment>,
  init_vir_mem_w3_shifted_comm: Option<Pcs::Commitment>,

  phy_mem_addr_w2_comm: Option<Pcs::Commitment>,
  phy_mem_addr_w3_comm: Option<Pcs::Commitment>,
  phy_mem_addr_w3_shifted_comm: Option<Pcs::Commitment>,
  vir_mem_addr_w2_comm: Option<Pcs::Commitment>,
  vir_mem_addr_w3_comm: Option<Pcs::Commitment>,
  vir_mem_addr_w3_shifted_comm: Option<Pcs::Commitment>,

  block_r1cs_sat_proof: R1CSProof<E, Pcs>,
  block_inst_evals_bound_rp: [E; 3],
  block_inst_evals_list: Vec<E>,
  block_r1cs_eval_proof_list: Vec<R1CSEvalProof<E>>,

  pairwise_check_r1cs_sat_proof: R1CSProof<E, Pcs>,
  pairwise_check_inst_evals_bound_rp: [E; 3],
  pairwise_check_inst_evals_list: Vec<E>,
  pairwise_check_r1cs_eval_proof: R1CSEvalProof<E>,

  perm_root_r1cs_sat_proof: R1CSProof<E, Pcs>,
  perm_root_inst_evals: [E; 3],
  perm_root_r1cs_eval_proof: R1CSEvalProof<E>,
  // Product proof for permutation
  // perm_poly_poly_list: Vec<E>,
  // proof_eval_perm_poly_prod_list: Vec<PolyEvalProof<E>>,

  // shift_proof: ShiftProofs<E>,
  // io_proof: IOProofs<E>,
}

// Sort block_num_proofs and record where each entry is
struct InstanceSortHelper {
  num_exec: usize,
  index: usize,
}
impl InstanceSortHelper {
  fn new(num_exec: usize, index: usize) -> InstanceSortHelper {
    InstanceSortHelper { num_exec, index }
  }
}

// Ordering of InstanceSortHelper solely by num_exec
impl Ord for InstanceSortHelper {
  fn cmp(&self, other: &Self) -> Ordering {
    self.num_exec.cmp(&other.num_exec)
  }
}
impl PartialOrd for InstanceSortHelper {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}
impl PartialEq for InstanceSortHelper {
  fn eq(&self, other: &Self) -> bool {
    self.num_exec == other.num_exec
  }
}
impl Eq for InstanceSortHelper {}

impl<E: ExtensionField + Send + Sync, Pcs: PolynomialCommitmentScheme<E>> SNARK<E, Pcs> {
  fn protocol_name() -> &'static [u8] {
    b"Spartan SNARK proof"
  }

  // Computes proof size by commitment / non-commitment
  fn compute_size(&self) -> (usize, usize, usize, usize) {
    /*
    let commit_size = bincode::serialize(&self.block_comm_vars_list).unwrap().len()
                           + bincode::serialize(&self.exec_inputs_comm).unwrap().len()
                           + bincode::serialize(&self.addr_comm_phy_mems).unwrap().len()
                           + bincode::serialize(&self.addr_comm_phy_mems_shifted).unwrap().len()
                           + bincode::serialize(&self.addr_comm_vir_mems).unwrap().len()
                           + bincode::serialize(&self.addr_comm_vir_mems_shifted).unwrap().len()
                           + bincode::serialize(&self.addr_comm_ts_bits).unwrap().len()

                           + bincode::serialize(&self.perm_exec_w2_comm_list).unwrap().len()
                           + bincode::serialize(&self.perm_exec_comm_w3_list).unwrap().len()
                           + bincode::serialize(&self.perm_exec_comm_w3_shifted).unwrap().len()

                           + bincode::serialize(&self.block_comm_w2_list).unwrap().len()
                           + bincode::serialize(&self.block_comm_w3_list).unwrap().len()
                           + bincode::serialize(&self.block_comm_w3_list_shifted).unwrap().len()

                           + bincode::serialize(&self.init_phy_mem_comm_w2).unwrap().len()
                           + bincode::serialize(&self.init_phy_mem_comm_w3).unwrap().len()
                           + bincode::serialize(&self.init_phy_mem_comm_w3_shifted).unwrap().len()

                           + bincode::serialize(&self.init_vir_mem_comm_w2).unwrap().len()
                           + bincode::serialize(&self.init_vir_mem_comm_w3).unwrap().len()
                           + bincode::serialize(&self.init_vir_mem_comm_w3_shifted).unwrap().len()

                           + bincode::serialize(&self.phy_mem_addr_comm_w2).unwrap().len()
                           + bincode::serialize(&self.phy_mem_addr_comm_w3).unwrap().len()
                           + bincode::serialize(&self.phy_mem_addr_comm_w3_shifted).unwrap().len()

                           + bincode::serialize(&self.vir_mem_addr_comm_w2).unwrap().len()
                           + bincode::serialize(&self.vir_mem_addr_comm_w3).unwrap().len()
                           + bincode::serialize(&self.vir_mem_addr_comm_w3_shifted).unwrap().len();
    */
    let dense_commit_size = 0;

    let block_proof_size = bincode::serialize(&self.block_r1cs_sat_proof)
      .unwrap()
      .len()
      + bincode::serialize(&self.block_inst_evals_bound_rp)
        .unwrap()
        .len()
      + bincode::serialize(&self.block_inst_evals_list)
        .unwrap()
        .len()
      + bincode::serialize(&self.block_r1cs_eval_proof_list)
        .unwrap()
        .len();

    let pairwise_proof_size = bincode::serialize(&self.pairwise_check_r1cs_sat_proof)
      .unwrap()
      .len()
      + bincode::serialize(&self.pairwise_check_inst_evals_bound_rp)
        .unwrap()
        .len()
      + bincode::serialize(&self.pairwise_check_inst_evals_list)
        .unwrap()
        .len()
      + bincode::serialize(&self.pairwise_check_r1cs_eval_proof)
        .unwrap()
        .len();

    let perm_proof_size = bincode::serialize(&self.perm_root_r1cs_sat_proof)
      .unwrap()
      .len()
      + bincode::serialize(&self.perm_root_inst_evals)
        .unwrap()
        .len()
      + bincode::serialize(&self.perm_root_r1cs_eval_proof)
        .unwrap()
        .len();
    // + bincode::serialize(&self.perm_poly_poly_list).unwrap().len()
    // + bincode::serialize(&self.proof_eval_perm_poly_prod_list).unwrap().len();

    // + bincode::serialize(&self.shift_proof).unwrap().len()
    // let io_proof_size = bincode::serialize(&self.io_proof).unwrap().len();
    (
      dense_commit_size,
      block_proof_size,
      pairwise_proof_size,
      perm_proof_size,
    )
  }

  /// A public computation to create a commitment to a list of R1CS instances
  pub fn multi_encode(
    inst: &Instance<E>,
  ) -> (
    Vec<Vec<usize>>,
    Vec<ComputationCommitment<E>>,
    Vec<ComputationDecommitment<E>>,
  ) {
    let timer_encode = Timer::new("SNARK::encode");
    let (label_map, mut comm, mut decomm) = inst.inst.multi_commit();

    timer_encode.stop();
    (
      label_map,
      comm
        .drain(..)
        .map(|i| ComputationCommitment { comm: i })
        .collect(),
      decomm
        .drain(..)
        .map(|i| ComputationDecommitment { decomm: i })
        .collect(),
    )
  }

  /// A public computation to create a commitment to a single R1CS instance
  pub fn encode(inst: &Instance<E>) -> (ComputationCommitment<E>, ComputationDecommitment<E>) {
    let timer_encode = Timer::new("SNARK::encode");
    let (comm, decomm) = inst.inst.commit();

    timer_encode.stop();
    (
      ComputationCommitment { comm },
      ComputationDecommitment { decomm },
    )
  }

  // Given information regarding a group of memory assignments, generate w2, w3, and w3_shifted
  fn mem_gen<const MEM_WIDTH: usize>(
    total_num_mem_accesses: usize,
    mems_list: &Vec<Vec<E>>,
    comb_r: &E,
    comb_tau: &E,
    _transcript: &mut Transcript<E>,
    pp: &ProverParam<E, Pcs>,
  ) -> (
    ProverWitnessSecInfo<E, Pcs>,
    Option<Pcs::Commitment>,
    ProverWitnessSecInfo<E, Pcs>,
    Option<Pcs::Commitment>,
    ProverWitnessSecInfo<E, Pcs>,
    Option<Pcs::Commitment>,
  ) {
    if total_num_mem_accesses > 0 {
      // init_mem_w2 is (I, O, ZO, r * data, 0, 0)
      // where ZO = 0,

      let mut mem_w2 = Vec::new();
      for q in 0..total_num_mem_accesses {
        mem_w2.push(vec![E::ZERO; MEM_WIDTH]);
        mem_w2[q][3] = *comb_r * mems_list[q][3];
      }
      // init_mems_w3 is (v, x, pi, D, I, O)
      // where I = v * (v + addr + r * data + r^2 * ls + r^3 * ts),
      //       O = v * v = v
      // are used by (dummy) consistency check
      let mut mem_w3 = vec![vec![E::ZERO; W3_WIDTH]; total_num_mem_accesses];
      for q in (0..total_num_mem_accesses).rev() {
        // v
        mem_w3[q][0] = mems_list[q][0];
        // x = v * (tau - addr - r * data - r^2 * ls - r^3 * ts)
        mem_w3[q][1] = mems_list[q][0] * (*comb_tau - mems_list[q][2] - mem_w2[q][3]);
        // pi and D
        if q != total_num_mem_accesses - 1 {
          mem_w3[q][3] = mem_w3[q][1] * (mem_w3[q + 1][2] + E::ONE - mem_w3[q + 1][0]);
        } else {
          mem_w3[q][3] = mem_w3[q][1];
        }
        mem_w3[q][2] = mem_w3[q][0] * mem_w3[q][3];
        mem_w3[q][4] = mems_list[q][0] * (mems_list[q][0] + mems_list[q][2] + mem_w2[q][3]);
        mem_w3[q][5] = mems_list[q][0];
      }
      let mem_w3_shifted_mat = [mem_w3[1..].to_vec(), vec![vec![E::ZERO; W3_WIDTH]]].concat();

      let (mem_w2_mle, mem_w2_p_comm, mem_w2_v_comm) = Self::mat_to_comm(&mem_w2, pp);
      let (mem_w3_mle, mem_w3_p_comm, mem_w3_v_comm) = Self::mat_to_comm(&mem_w3, pp);
      let (mem_w3_shifted_mle, mem_w3_shifted_p_comm, mem_w3_shifted_v_comm) = Self::mat_to_comm(&mem_w3_shifted_mat, pp);

      let mem_w2_prover = ProverWitnessSecInfo::new(vec![mem_w2], vec![mem_w2_mle], vec![mem_w2_p_comm]);
      let mem_w3_prover = ProverWitnessSecInfo::new(vec![mem_w3.clone()], vec![mem_w3_mle], vec![mem_w3_p_comm]);
      let mem_w3_shifted_prover = ProverWitnessSecInfo::new(
        vec![mem_w3_shifted_mat],
        vec![mem_w3_shifted_mle],
        vec![mem_w3_shifted_p_comm],
      );

      (mem_w2_prover, Some(mem_w2_v_comm), mem_w3_prover, Some(mem_w3_v_comm), mem_w3_shifted_prover, Some(mem_w3_shifted_v_comm))
    } else {
      (
        ProverWitnessSecInfo::dummy(),
        None,
        ProverWitnessSecInfo::dummy(),
        None,
        ProverWitnessSecInfo::dummy(),
        None,
      )
    }
  }

  // Convert a matrix into mles and commitments
  fn mat_to_comm(mat: &Vec<Vec<E>>, _pp: &ProverParam<E, Pcs>) -> (
    DenseMultilinearExtension<E>,
    Pcs::CommitmentWithWitness,
    Pcs::Commitment,
  ) {
    // Flatten the witnesses into a Q_i * X list
    let mat_concat_p: Vec<E::BaseField> = mat.clone().into_iter().flatten().map(|e| e.as_bases()[0].clone()).collect();
    let num_vars = mat_concat_p.len();
    let param = Pcs::setup(num_vars).unwrap();
    let (pp, _error) = Pcs::trim(param, num_vars).unwrap();
    // create a multilinear polynomial using the supplied assignment for variables
    let poly = DenseMultilinearExtension::from_evaluation_vec_smart(mat_concat_p.len().log_2(), mat_concat_p);
    let p_comm = Pcs::commit(&pp, &poly).unwrap();
    let v_comm = Pcs::get_pure_commitment(&p_comm);
    (poly, p_comm, v_comm)
  }

  // Convert a matrix into a prover witness sec and a commitment
  fn mat_to_prove_wit_sec(mat: Vec<Vec<E>>, pp: &ProverParam<E, Pcs>) -> (
    ProverWitnessSecInfo<E, Pcs>,
    Pcs::Commitment,
  ) {
    let (poly, p_comm, v_comm) = Self::mat_to_comm(&mat, pp);
    let prover_wit_sec = ProverWitnessSecInfo::new(vec![mat], vec![poly], vec![p_comm]);
    (prover_wit_sec, v_comm)
  }

  // Convert a matrix into a prover witness sec without committing
  fn mat_to_prover_wit_sec_no_commit(mat: Vec<Vec<E>>) -> ProverWitnessSecInfo<E, Pcs> {
    // Flatten the witnesses into a Q_i * X list
    let mat_concat_p: Vec<E::BaseField> = mat.clone().into_iter().flatten().map(|e| e.as_bases()[0].clone()).collect();
    // create a multilinear polynomial using the supplied assignment for variables
    let poly = DenseMultilinearExtension::from_evaluation_vec_smart(mat_concat_p.len().log_2(), mat_concat_p);
    let prover_wit_sec = ProverWitnessSecInfo::new(vec![mat], vec![poly], Vec::new()); // No commitment
    prover_wit_sec
  }

  // Convert a list of matrices into prover witness secs and commitments
  fn mats_to_prove_wit_sec(mats: Vec<Vec<Vec<E>>>, pp: &ProverParam<E, Pcs>) -> (
    ProverWitnessSecInfo<E, Pcs>,
    Vec<Pcs::Commitment>,
  ) {
    let mut polys = Vec::new();
    let mut p_comms = Vec::new();
    let mut v_comms = Vec::new();
    for mat in &mats {
      let (poly, p_comm, v_comm) = Self::mat_to_comm(mat, pp);
      polys.push(poly);
      p_comms.push(p_comm);
      v_comms.push(v_comm);
    }
    let prover_wit_sec = ProverWitnessSecInfo::new(mats, polys, p_comms);
    (prover_wit_sec, v_comms)
  }

  /// A method to produce a SNARK proof of the satisfiability of an R1CS instance
  pub fn prove(
    input_block_num: usize,
    output_block_num: usize,
    input_liveness: &Vec<bool>,
    func_input_width: usize,
    input_offset: usize,
    output_offset: usize,
    input: &Vec<[u8; 32]>,
    output: &[u8; 32],
    output_exec_num: usize,

    num_vars: usize,
    num_ios: usize,
    max_block_num_phy_ops: usize,
    block_num_phy_ops: &Vec<usize>,
    max_block_num_vir_ops: usize,
    block_num_vir_ops: &Vec<usize>,
    mem_addr_ts_bits_size: usize,
    num_inputs_unpadded: usize,
    block_num_vars: &Vec<usize>,

    block_num_instances_bound: usize,
    block_max_num_proofs: usize,
    block_num_proofs: &Vec<usize>,
    block_inst: &mut Instance<E>,
    block_comm_map: &Vec<Vec<usize>>,
    block_comm_list: &Vec<ComputationCommitment<E>>,
    block_decomm_list: &Vec<ComputationDecommitment<E>>,

    consis_num_proofs: usize,
    total_num_init_phy_mem_accesses: usize,
    total_num_init_vir_mem_accesses: usize,
    total_num_phy_mem_accesses: usize,
    total_num_vir_mem_accesses: usize,
    pairwise_check_inst: &mut Instance<E>,
    pairwise_check_comm: &ComputationCommitment<E>,
    pairwise_check_decomm: &ComputationDecommitment<E>,

    block_vars_mat: Vec<Vec<VarsAssignment<E>>>,
    exec_inputs_list: Vec<InputsAssignment<E>>,
    init_phy_mems_list: Vec<MemsAssignment<E>>,
    init_vir_mems_list: Vec<MemsAssignment<E>>,
    addr_phy_mems_list: Vec<MemsAssignment<E>>,
    addr_vir_mems_list: Vec<MemsAssignment<E>>,
    addr_ts_bits_list: Vec<MemsAssignment<E>>,

    perm_root_inst: &Instance<E>,
    perm_root_comm: &ComputationCommitment<E>,
    perm_root_decomm: &ComputationDecommitment<E>,
    transcript: &mut Transcript<E>,
  ) -> Self {
    let timer_prove = Timer::new("SNARK::prove");

    // we create a Transcript object seeded with a random Scalar
    // to aid the prover produce its randomness
    let mut random_tape = RandomTape::new(b"proof");

    append_protocol_name(
      transcript,
      SNARK::<E, Pcs>::protocol_name(),
    );

    // --
    // ASSERTIONS
    // --
    assert!(0 < consis_num_proofs);
    for p in 0..block_num_instances_bound {
      assert!(block_num_proofs[p] <= block_max_num_proofs);
    }
    let io_width = 2 * num_inputs_unpadded;

    // --
    // PREPROCESSING
    // --
    // unwrap the assignments
    let mut block_vars_mat = block_vars_mat
      .into_iter()
      .map(|a| a.into_iter().map(|v| v.assignment).collect::<Vec<Vec<E>>>())
      .collect::<Vec<Vec<Vec<E>>>>();
    let mut exec_inputs_list = exec_inputs_list
      .into_iter()
      .map(|v| v.assignment)
      .collect::<Vec<Vec<E>>>();
    let mut init_phy_mems_list = init_phy_mems_list
      .into_iter()
      .map(|v| v.assignment)
      .collect::<Vec<Vec<E>>>();
    let mut init_vir_mems_list = init_vir_mems_list
      .into_iter()
      .map(|v| v.assignment)
      .collect::<Vec<Vec<E>>>();
    let mut addr_phy_mems_list = addr_phy_mems_list
      .into_iter()
      .map(|v| v.assignment)
      .collect::<Vec<Vec<E>>>();
    let mut addr_vir_mems_list = addr_vir_mems_list
      .into_iter()
      .map(|v| v.assignment)
      .collect::<Vec<Vec<E>>>();
    let mut addr_ts_bits_list = addr_ts_bits_list
      .into_iter()
      .map(|v| v.assignment)
      .collect::<Vec<Vec<E>>>();

    // --
    // INSTANCE COMMITMENTS
    // --
    let input_block_num = E::from(input_block_num as u64);
    let output_block_num = E::from(output_block_num as u64);
    let input: Vec<E> = input.iter().map(|i| from_bytes(i).unwrap()).collect();
    let output: E = from_bytes(output).unwrap();
    {
      let timer_commit = Timer::new("inst_commit");
      // Commit public parameters
      append_field_to_transcript(
        b"func_input_width",
        transcript,
        E::from(func_input_width as u64),
      );
      append_field_to_transcript(b"input_offset", transcript, E::from(input_offset as u64));
      append_field_to_transcript(b"output_offset", transcript, E::from(output_offset as u64));
      append_field_to_transcript(
        b"output_exec_num",
        transcript,
        E::from(output_exec_num as u64),
      );
      append_field_to_transcript(b"num_ios", transcript, E::from(num_ios as u64));

      for n in block_num_vars {
        append_field_to_transcript(b"block_num_vars", transcript, E::from(*n as u64));
      }
      append_field_to_transcript(
        b"mem_addr_ts_bits_size",
        transcript,
        E::from(mem_addr_ts_bits_size as u64),
      );
      append_field_to_transcript(
        b"num_inputs_unpadded",
        transcript,
        E::from(num_inputs_unpadded as u64),
      );
      append_field_to_transcript(
        b"block_num_instances_bound",
        transcript,
        E::from(block_num_instances_bound as u64),
      );
      append_field_to_transcript(
        b"block_max_num_proofs",
        transcript,
        E::from(block_max_num_proofs as u64),
      );
      for p in block_num_phy_ops {
        append_field_to_transcript(b"block_num_phy_ops", transcript, E::from(*p as u64));
      }
      for v in block_num_vir_ops {
        append_field_to_transcript(b"block_num_vir_ops", transcript, E::from(*v as u64));
      }
      append_field_to_transcript(
        b"total_num_init_phy_mem_accesses",
        transcript,
        E::from(total_num_init_phy_mem_accesses as u64),
      );
      append_field_to_transcript(
        b"total_num_init_vir_mem_accesses",
        transcript,
        E::from(total_num_init_vir_mem_accesses as u64),
      );
      append_field_to_transcript(
        b"total_num_phy_mem_accesses",
        transcript,
        E::from(total_num_phy_mem_accesses as u64),
      );
      append_field_to_transcript(
        b"total_num_vir_mem_accesses",
        transcript,
        E::from(total_num_vir_mem_accesses as u64),
      );
      // commit num_proofs
      append_field_to_transcript(
        b"block_max_num_proofs",
        transcript,
        E::from(block_max_num_proofs as u64),
      );
      for n in block_num_proofs {
        append_field_to_transcript(b"block_num_proofs", transcript, E::from(*n as u64));
      }

      // append a commitment to the computation to the transcript
      for b in block_comm_map {
        for l in b {
          append_field_to_transcript(b"block_comm_map", transcript, E::from(*l as u64));
        }
      }
      for c in block_comm_list {
        c.comm.append_to_transcript(b"block_comm", transcript);
      }
      pairwise_check_comm
        .comm
        .append_to_transcript(b"pairwise_comm", transcript);
      perm_root_comm
        .comm
        .append_to_transcript(b"perm_comm", transcript);

      // Commit io
      append_field_to_transcript(b"input_block_num", transcript, input_block_num);
      append_field_to_transcript(b"output_block_num", transcript, output_block_num);
      append_field_vector_to_transcript(b"input_list", transcript, &input);
      append_field_to_transcript(b"output_list", transcript, output);

      timer_commit.stop();
    }

    // --
    // BLOCK SORT
    // --
    let timer_sort = Timer::new("block_sort");
    // Block_num_instance is the number of non-zero entries in block_num_proofs
    let block_num_instances = block_num_proofs
      .iter()
      .fold(0, |i, j| if *j > 0 { i + 1 } else { i });
    // Sort the following based on block_num_proofs:
    // - block_num_proofs
    // - block_inst, block_comm, block_decomm
    // - block_num_phy_mem_accesses
    // - mem_extract_inst, mem_extract_comm, mem_extract_decomm
    let mut inst_sorter = Vec::new();
    for i in 0..block_num_instances_bound {
      inst_sorter.push(InstanceSortHelper::new(block_num_proofs[i], i))
    }
    // Sort from high -> low
    inst_sorter.sort_by(|a, b| b.cmp(a));

    let inst_sorter = &inst_sorter[..block_num_instances];
    let mut block_num_proofs: Vec<usize> = inst_sorter.iter().map(|i| i.num_exec).collect();
    // index[i] = j => the original jth entry should now be at the ith position
    let index: Vec<usize> = inst_sorter.iter().map(|i| i.index).collect();
    let block_inst_unsorted = block_inst.clone();
    block_inst.sort(block_num_instances, &index);
    let block_num_phy_ops: Vec<usize> = (0..block_num_instances)
      .map(|i| block_num_phy_ops[index[i]])
      .collect();
    let block_num_vir_ops: Vec<usize> = (0..block_num_instances)
      .map(|i| block_num_vir_ops[index[i]])
      .collect();

    // --
    // PADDING
    // --
    let dummy_inputs = vec![E::ZERO; num_ios];
    // For every block that num_proofs is not a power of 2, pad vars_mat and inputs_mat until the length is a power of 2
    let block_max_num_proofs = block_max_num_proofs.next_power_of_two();
    for i in 0..block_num_instances {
      let dummy_vars = vec![E::ZERO; block_vars_mat[i][0].len()];
      let gap = block_num_proofs[i].next_power_of_two() - block_num_proofs[i];
      block_vars_mat[i].extend(vec![dummy_vars.clone(); gap]);
      block_num_proofs[i] = block_num_proofs[i].next_power_of_two();
    }
    // Pad exec_inputs with dummys so the length is a power of 2
    exec_inputs_list.extend(vec![
      dummy_inputs;
      consis_num_proofs.next_power_of_two()
        - consis_num_proofs
    ]);
    let consis_num_proofs = consis_num_proofs.next_power_of_two();

    // Pad init_mems with dummys so the length is a power of 2
    if total_num_init_phy_mem_accesses > 0 {
      let dummy_addr = vec![E::ZERO; INIT_PHY_MEM_WIDTH];
      init_phy_mems_list.extend(vec![
        dummy_addr;
        total_num_init_phy_mem_accesses.next_power_of_two()
          - total_num_init_phy_mem_accesses
      ]);
    }
    let total_num_init_phy_mem_accesses = if total_num_init_phy_mem_accesses == 0 {
      0
    } else {
      total_num_init_phy_mem_accesses.next_power_of_two()
    };
    if total_num_init_vir_mem_accesses > 0 {
      let dummy_addr = vec![E::ZERO; INIT_VIR_MEM_WIDTH];
      init_vir_mems_list.extend(vec![
        dummy_addr;
        total_num_init_vir_mem_accesses.next_power_of_two()
          - total_num_init_vir_mem_accesses
      ]);
    }
    let total_num_init_vir_mem_accesses = if total_num_init_vir_mem_accesses == 0 {
      0
    } else {
      total_num_init_vir_mem_accesses.next_power_of_two()
    };
    // Pad addr_phy_mems with dummys so the length is a power of 2
    if total_num_phy_mem_accesses > 0 {
      let dummy_addr = vec![E::ZERO; PHY_MEM_WIDTH];
      addr_phy_mems_list.extend(vec![
        dummy_addr;
        total_num_phy_mem_accesses.next_power_of_two()
          - total_num_phy_mem_accesses
      ]);
    }
    let total_num_phy_mem_accesses = if total_num_phy_mem_accesses == 0 {
      0
    } else {
      total_num_phy_mem_accesses.next_power_of_two()
    };
    // Pad addr_vir_mems with dummys so the length is a power of 2
    if total_num_vir_mem_accesses > 0 {
      let dummy_addr = vec![E::ZERO; VIR_MEM_WIDTH];
      addr_vir_mems_list.extend(vec![
        dummy_addr;
        total_num_vir_mem_accesses.next_power_of_two()
          - total_num_vir_mem_accesses
      ]);
      let dummy_ts = vec![E::ZERO; mem_addr_ts_bits_size];
      addr_ts_bits_list.extend(vec![
        dummy_ts;
        total_num_vir_mem_accesses.next_power_of_two()
          - total_num_vir_mem_accesses
      ]);
    }
    let total_num_vir_mem_accesses = if total_num_vir_mem_accesses == 0 {
      0
    } else {
      total_num_vir_mem_accesses.next_power_of_two()
    };
    let block_num_proofs = &block_num_proofs;

    // --
    // PAIRWISE SORT
    // --
    // Note: perform pairwise sort after padding because pairwise sort uses padded values as parameter
    // Sort the pairwise instances: CONSIS_CHECK, PHY_MEM_COHERE
    let mut inst_sorter = Vec::new();
    inst_sorter.push(InstanceSortHelper::new(consis_num_proofs, 0));
    inst_sorter.push(InstanceSortHelper::new(total_num_phy_mem_accesses, 1));
    inst_sorter.push(InstanceSortHelper::new(total_num_vir_mem_accesses, 2));
    // Sort from high -> low
    inst_sorter.sort_by(|a, b| b.cmp(a));

    let pairwise_num_instances = 1
      + if total_num_phy_mem_accesses > 0 { 1 } else { 0 }
      + if total_num_vir_mem_accesses > 0 { 1 } else { 0 };
    let inst_sorter = &inst_sorter[..pairwise_num_instances];
    // index[i] = j => the original jth entry should now be at the ith position
    let index: Vec<usize> = inst_sorter.iter().map(|i| i.index).collect();
    let pairwise_check_inst_unsorted = pairwise_check_inst.clone();
    pairwise_check_inst.sort(pairwise_num_instances, &index);

    timer_sort.stop();

    // --
    // CHALLENGES AND WITNESSES FOR PERMUTATION
    // --
    let timer_gen = Timer::new("witness_gen");
    // Block
    let timer_sec_gen = Timer::new("block_witness_gen");
    let max_poly_size = block_max_num_proofs * num_vars;
    println!("MAX_POLY_SIZE: {}", max_poly_size);
    let poly_param = Pcs::setup(max_poly_size).unwrap();
    let (poly_pp, poly_vp) = Pcs::trim(poly_param, num_vars).unwrap();

    let (
      comb_tau,
      comb_r,
      perm_w0_prover,
      // perm_exec
      perm_exec_w2_prover,
      perm_exec_w2_comm,
      perm_exec_w3_prover,
      perm_exec_w3_comm,
      perm_exec_w3_shifted_prover, // shifted by W3_WIDTH
      perm_exec_w3_shifted_comm,
      // input_block_w2 | phy_mem_block_w2 | vir_mem_block_w2
      block_w2_prover,
      block_w2_comm_list,
      // block_w3
      block_w3_prover,
      block_w3_comm_list,
      block_w3_shifted_prover, // shifted by W3_WIDTH
      block_w3_shifted_comm_list,
    ) = {
      let comb_tau = challenge_scalar(transcript, b"challenge_tau");
      let comb_r = challenge_scalar(transcript, b"challenge_r");

      // PERM_W0
      // w0 is (tau, r, r^2, ...) for the first 2 * num_inputs_unpadded entries
      // set the first entry to 1 for multiplication and later revert it to tau
      let perm_w0 = {
        let mut perm_w0 = vec![comb_tau];
        let mut r_tmp = comb_r;
        for _ in 1..2 * num_inputs_unpadded {
          perm_w0.push(r_tmp);
          r_tmp = r_tmp * comb_r;
        }
        perm_w0.extend(vec![E::ZERO; num_ios - 2 * num_inputs_unpadded]);
        perm_w0
      };

      // PERM_EXEC
      // w2 is _, _, ZO, r * i1, r^2 * i2, r^3 * i3, ...
      // where ZO * r^n = r^n * o0 + r^(n + 1) * o1, ...,
      // are used by the consistency check
      let (perm_exec_w2, perm_exec_w3) = {
        let perm_exec_w2: Vec<Vec<E>>;
        let mut perm_exec_w3: Vec<Vec<E>>;
        // Entries that do not depend on others can be generated in parallel
        (perm_exec_w2, perm_exec_w3) = (0..consis_num_proofs).into_par_iter().map(|q| {
          // perm_exec_w2
          let mut perm_exec_w2_q = [
            vec![E::ZERO; 3],
            (1..2 * num_inputs_unpadded - 2)
              .map(|j| perm_w0[j] * exec_inputs_list[q][j + 2])
              .collect(),
            vec![E::ZERO; num_ios - 2 * num_inputs_unpadded],
          ].concat();
          perm_exec_w2_q[0] = exec_inputs_list[q][0];
          perm_exec_w2_q[1] = exec_inputs_list[q][0];
          for i in 0..num_inputs_unpadded - 1 {
            let perm = if i == 0 { E::ONE } else { perm_w0[i] };
            perm_exec_w2_q[0] = perm_exec_w2_q[0] + perm * exec_inputs_list[q][2 + i];
            perm_exec_w2_q[2] =
              perm_exec_w2_q[2] + perm * exec_inputs_list[q][2 + (num_inputs_unpadded - 1) + i];
          }
          perm_exec_w2_q[0] = perm_exec_w2_q[0] * exec_inputs_list[q][0];
          let ZO = perm_exec_w2_q[2];
          perm_exec_w2_q[1] = perm_exec_w2_q[1] + ZO;
          perm_exec_w2_q[1] = perm_exec_w2_q[1] * exec_inputs_list[q][0];

          // perm_exec_w3
          let mut perm_exec_w3_q = vec![E::ZERO; 8];
          perm_exec_w3_q[0] = exec_inputs_list[q][0];
          perm_exec_w3_q[1] = perm_exec_w3_q[0]
            * (comb_tau
              - perm_exec_w2_q[3..]
                .iter()
                .fold(E::ZERO, |a, b| a + *b)
              - exec_inputs_list[q][2]);
          perm_exec_w3_q[4] = perm_exec_w2_q[0];
          perm_exec_w3_q[5] = perm_exec_w2_q[1];

          (perm_exec_w2_q, perm_exec_w3_q)
        }).unzip();
        // Generate sequential entries separately
        for q in (0..consis_num_proofs).rev() {
          if q != consis_num_proofs - 1 {
            perm_exec_w3[q][3] = perm_exec_w3[q][1]
              * (perm_exec_w3[q + 1][2] + E::ONE - perm_exec_w3[q + 1][0]);
          } else {
            perm_exec_w3[q][3] = perm_exec_w3[q][1];
          }
          perm_exec_w3[q][2] = perm_exec_w3[q][0] * perm_exec_w3[q][3];
        }
        (perm_exec_w2, perm_exec_w3)
      };
      let perm_exec_w3_shifted_mat = [perm_exec_w3[1..].to_vec(), vec![vec![E::ZERO; 8]]].concat();

      // INPUT_BLOCK_W2 | PHY_MEM_BLOCK_W2 & VIR_MEM_BLOCK_W2
      // BLOCK_W3
      //           INPUT      PHY    VIR
      // w3 is [v, x, pi, D, pi, D, pi, D]
      let mut block_w3: Vec<Vec<Vec<E>>> = Vec::new();
      let block_w2 = {
        let mut block_w2: Vec<Vec<Vec<E>>> = Vec::new();
        let block_w2_size_list: Vec<usize> = (0..block_num_instances)
          .map(|i| {
            (2 * num_inputs_unpadded + 2 * block_num_phy_ops[i] + 4 * block_num_vir_ops[i])
              .next_power_of_two()
          })
          .collect();

        // PHY_MEM
        // w2 is (MR, MC, MR, MC, MR, MC, ...)
        // w3 is (V, X, PI, D)
        let V_PA = |i: usize| 2 * i;
        let V_PD = |i: usize| 2 * i + 1;
        let V_PMR = |i: usize| 2 * num_inputs_unpadded + 2 * i;
        let V_PMC = |i: usize| 2 * num_inputs_unpadded + 2 * i + 1;
        // VIR_MEM
        // w2 is (MR1, MR2, MR3, MC, MR1, MR2, MR3, MC, ...)
        // w3 is (V, X, PI, D)
        let V_VA = |b: usize, i: usize| 2 * block_num_phy_ops[b] + 4 * i;
        let V_VD = |b: usize, i: usize| 2 * block_num_phy_ops[b] + 4 * i + 1;
        let V_VL = |b: usize, i: usize| 2 * block_num_phy_ops[b] + 4 * i + 2;
        let V_VT = |b: usize, i: usize| 2 * block_num_phy_ops[b] + 4 * i + 3;
        let V_VMR1 =
          |b: usize, i: usize| 2 * num_inputs_unpadded + 2 * block_num_phy_ops[b] + 4 * i;
        let V_VMR2 =
          |b: usize, i: usize| 2 * num_inputs_unpadded + 2 * block_num_phy_ops[b] + 4 * i + 1;
        let V_VMR3 =
          |b: usize, i: usize| 2 * num_inputs_unpadded + 2 * block_num_phy_ops[b] + 4 * i + 2;
        let V_VMC =
          |b: usize, i: usize| 2 * num_inputs_unpadded + 2 * block_num_phy_ops[b] + 4 * i + 3;

        for p in 0..block_num_instances {
          let block_w2_p: Vec<Vec<E>>;
          let mut block_w3_p: Vec<Vec<E>>;
          // Entries that do not depend on others can be generated in parallel
          (block_w2_p, block_w3_p) = (0..block_num_proofs[p]).into_par_iter().map(|q| {
            let V_CNST = block_vars_mat[p][q][0];
            // For INPUT
            let mut q2 = vec![E::ZERO; block_w2_size_list[p]];

            q2[0] = block_vars_mat[p][q][0];
            q2[1] = block_vars_mat[p][q][0];
            for i in 1..2 * (num_inputs_unpadded - 1) {
              q2[2 + i] = q2[2 + i] + perm_w0[i] * block_vars_mat[p][q][i + 2];
            }
            for i in 0..num_inputs_unpadded - 1 {
              let perm = if i == 0 { E::ONE } else { perm_w0[i] };
              q2[0] = q2[0] + perm * block_vars_mat[p][q][2 + i];
              q2[2] = q2[2] + perm * block_vars_mat[p][q][2 + (num_inputs_unpadded - 1) + i];
            }
            q2[0] = q2[0] * block_vars_mat[p][q][0];
            let ZO = q2[2];
            q2[1] = q2[1] + ZO;
            q2[1] = q2[1] * block_vars_mat[p][q][0];
            let mut q3 = vec![E::ZERO; 8];
            q3[0] = block_vars_mat[p][q][0];

            // For PHY
            // Compute PMR, PMC
            for i in 0..block_num_phy_ops[p] {
              // PMR = r * PD
              q2[V_PMR(i)] = comb_r * block_vars_mat[p][q][io_width + V_PD(i)];
              // PMC = (1 or PMC[i-1]) * (tau - PA - PMR)
              let t = if i == 0 {
                V_CNST
              } else {
                q2[V_PMC(i - 1)]
              };
              q2[V_PMC(i)] = t
                * (comb_tau - block_vars_mat[p][q][io_width + V_PA(i)] - q2[V_PMR(i)]);
            }

            // For VIR
            // Compute VMR1, VMR2, VMR3, VMC
            for i in 0..block_num_vir_ops[p] {
              // VMR1 = r * VD
              q2[V_VMR1(p, i)] = comb_r * block_vars_mat[p][q][io_width + V_VD(p, i)];
              // VMR2 = r^2 * VL
              q2[V_VMR2(p, i)] =
                comb_r * comb_r * block_vars_mat[p][q][io_width + V_VL(p, i)];
              // VMR1 = r^3 * VT
              q2[V_VMR3(p, i)] =
                comb_r * comb_r * comb_r * block_vars_mat[p][q][io_width + V_VT(p, i)];
              // VMC = (1 or VMC[i-1]) * (tau - VA - VMR1 - VMR2 - VMR3)
              let t = if i == 0 {
                V_CNST
              } else {
                q2[V_VMC(p, i - 1)]
              };
              q2[V_VMC(p, i)] = t
                * (comb_tau
                  - block_vars_mat[p][q][io_width + V_VA(p, i)]
                  - q2[V_VMR1(p, i)]
                  - q2[V_VMR2(p, i)]
                  - q2[V_VMR3(p, i)]);
            }
            (q2, q3)
          }).unzip();
          // Generate sequential entries separately
          for q in (0..block_num_proofs[p]).rev() {
            let V_CNST = block_vars_mat[p][q][0];
            // For INPUT
            block_w3_p[q][1] = block_w3_p[q][0]
              * (comb_tau
                - block_w2_p[q][3..]
                  .iter()
                  .fold(E::ZERO, |a, b| a + *b)
                - block_vars_mat[p][q][2]);
            if q != block_num_proofs[p] - 1 {
              block_w3_p[q][3] = block_w3_p[q][1]
                * (block_w3_p[q + 1][2] + E::ONE - block_w3_p[q + 1][0]);
            } else {
              block_w3_p[q][3] = block_w3_p[q][1];
            }
            block_w3_p[q][2] = block_w3_p[q][0] * block_w3_p[q][3];

            // For PHY
            // Compute x
            let px = if block_num_phy_ops[p] == 0 {
              V_CNST
            } else {
              block_w2_p[q][V_PMC(block_num_phy_ops[p] - 1)]
            };
            // Compute D and pi
            if q != block_num_proofs[p] - 1 {
              block_w3_p[q][5] =
                px * (block_w3_p[q + 1][4] + E::ONE - block_w3_p[q + 1][0]);
            } else {
              block_w3_p[q][5] = px;
            }
            block_w3_p[q][4] = V_CNST * block_w3_p[q][5];

            // For VIR
            // Compute x
            let vx = if block_num_vir_ops[p] == 0 {
              V_CNST
            } else {
              block_w2_p[q][V_VMC(p, block_num_vir_ops[p] - 1)]
            };
            // Compute D and pi
            if q != block_num_proofs[p] - 1 {
              block_w3_p[q][7] =
                vx * (block_w3_p[q + 1][6] + E::ONE - block_w3_p[q + 1][0]);
            } else {
              block_w3_p[q][7] = vx;
            }
            block_w3_p[q][6] = V_CNST * block_w3_p[q][7];
          }

          block_w2.push(block_w2_p);
          block_w3.push(block_w3_p);
        }

        block_w2
      };
      let block_w3_shifted_mat = block_w3.iter().map(|i| [i[1..].to_vec(), vec![vec![E::ZERO; 8]]].concat()).collect();

      let perm_w0_prover = Self::mat_to_prover_wit_sec_no_commit(vec![perm_w0]); // Do not commit perm_w0
      let (perm_exec_w2_prover, perm_exec_w2_v_comm) = Self::mat_to_prove_wit_sec(perm_exec_w2, &poly_pp);
      let (perm_exec_w3_prover, perm_exec_w3_v_comm) = Self::mat_to_prove_wit_sec(perm_exec_w3, &poly_pp);
      let (perm_exec_w3_shifted_prover, perm_exec_w3_shifted_v_comm) = Self::mat_to_prove_wit_sec(perm_exec_w3_shifted_mat, &poly_pp);
      let (block_w2_prover, block_w2_v_comm) = Self::mats_to_prove_wit_sec(block_w2, &poly_pp);
      let (block_w3_prover, block_w3_v_comm) = Self::mats_to_prove_wit_sec(block_w3, &poly_pp);
      let (block_w3_shifted_prover, block_w3_shifted_v_comm) = Self::mats_to_prove_wit_sec(block_w3_shifted_mat, &poly_pp);

      // Append commmitments to transcript
      for comm in vec![
        &perm_exec_w2_v_comm,
        &perm_exec_w3_v_comm,
        &perm_exec_w3_shifted_v_comm,
      ] {
        Pcs::write_commitment(comm, transcript);
      }
      for comm in block_w2_v_comm.iter() {
        Pcs::write_commitment(comm, transcript);
      }
      for comm in block_w3_v_comm.iter() {
        Pcs::write_commitment(comm, transcript);
      }
      for comm in block_w3_shifted_v_comm.iter() {
        Pcs::write_commitment(comm, transcript);
      }

      (
        comb_tau,
        comb_r,
        perm_w0_prover,
        perm_exec_w2_prover,
        perm_exec_w2_v_comm,
        perm_exec_w3_prover,
        perm_exec_w3_v_comm,
        perm_exec_w3_shifted_prover,
        perm_exec_w3_shifted_v_comm,
        block_w2_prover,
        block_w2_v_comm,
        block_w3_prover,
        block_w3_v_comm,
        block_w3_shifted_prover,
        block_w3_shifted_v_comm,
      )
    };
    timer_sec_gen.stop();

    // Initial Physical Memory-as-a-whole
    let timer_sec_gen = Timer::new("init_phy_mem_witness_gen");
    let (init_phy_mem_w2_prover, init_phy_mem_w2_comm, init_phy_mem_w3_prover, init_phy_mem_w3_comm, init_phy_mem_w3_shifted_prover, init_phy_mem_w3_shifted_comm) =
      Self::mem_gen::<INIT_PHY_MEM_WIDTH>(
        total_num_init_phy_mem_accesses,
        &init_phy_mems_list,
        &comb_r,
        &comb_tau,
        transcript,
        &poly_pp,
      );
    timer_sec_gen.stop();

    // Initial Virtual Memory-as-a-whole
    let timer_sec_gen = Timer::new("init_vir_mem_witness_gen");
    let (init_vir_mem_w2_prover, init_vir_mem_w2_comm, init_vir_mem_w3_prover, init_vir_mem_w3_comm, init_vir_mem_w3_shifted_prover, init_vir_mem_w3_shifted_comm) =
      Self::mem_gen::<INIT_VIR_MEM_WIDTH>(
        total_num_init_vir_mem_accesses,
        &init_vir_mems_list,
        &comb_r,
        &comb_tau,
        transcript,
        &poly_pp,
      );
    timer_sec_gen.stop();

    // Physical Memory-as-a-whole
    let timer_sec_gen = Timer::new("phy_mem_addr_witness_gen");
    let (phy_mem_addr_w2_prover, phy_mem_addr_w2_comm, phy_mem_addr_w3_prover, phy_mem_addr_w3_comm, phy_mem_addr_w3_shifted_prover, phy_mem_addr_w3_shifted_comm) =
      Self::mem_gen::<PHY_MEM_WIDTH>(
        total_num_phy_mem_accesses,
        &addr_phy_mems_list,
        &comb_r,
        &comb_tau,
        transcript,
        &poly_pp,
      );

    for op_comm in vec![
      &init_phy_mem_w2_comm,
      &init_phy_mem_w3_comm,
      &init_phy_mem_w3_shifted_comm,
      &init_vir_mem_w2_comm,
      &init_vir_mem_w3_comm,
      &init_vir_mem_w3_shifted_comm,
      &phy_mem_addr_w2_comm,
      &phy_mem_addr_w3_comm,
      &phy_mem_addr_w3_shifted_comm,
    ] {
      match op_comm {
        Some(comm) => {
          Pcs::write_commitment(comm, transcript).unwrap()
        },
        None => (),
      }
    }

    timer_sec_gen.stop();

    // Virtual Memory-as-a-whole
    let timer_sec_gen = Timer::new("vir_mem_addr_witness_gen");
    let (vir_mem_addr_w2_prover, vir_mem_addr_w2_comm, vir_mem_addr_w3_prover, vir_mem_addr_w3_comm, vir_mem_addr_w3_shifted_prover, vir_mem_addr_w3_shifted_comm) = {
      if total_num_vir_mem_accesses > 0 {
        // vir_mem_addr_w2 is (I, O, ZO, r * data, r^2 * ls, r^3 * ts)
        // where ZO = 0,

        let mut vir_mem_addr_w2 = Vec::new();
        for q in 0..total_num_vir_mem_accesses {
          vir_mem_addr_w2.push(vec![E::ZERO; VIR_MEM_WIDTH]);
          vir_mem_addr_w2[q][3] = comb_r * addr_vir_mems_list[q][3];
          vir_mem_addr_w2[q][4] = comb_r * comb_r * addr_vir_mems_list[q][4];
          vir_mem_addr_w2[q][5] = comb_r * comb_r * comb_r * addr_vir_mems_list[q][5];
        }
        // vir_mem_addr_w3 is (v, x, pi, D, I, O)
        // where I = v * (v + addr + r * data + r^2 * ls + r^3 * ts),
        //       O = v * v = v
        // are used by (dummy) consistency check
        let mut vir_mem_addr_w3 = vec![vec![E::ZERO; W3_WIDTH]; total_num_vir_mem_accesses];
        for q in (0..total_num_vir_mem_accesses).rev() {
          // v
          vir_mem_addr_w3[q][0] = addr_vir_mems_list[q][0];
          // x = v * (tau - addr - r * data - r^2 * ls - r^3 * ts)
          vir_mem_addr_w3[q][1] = addr_vir_mems_list[q][0]
            * (comb_tau
              - addr_vir_mems_list[q][2]
              - vir_mem_addr_w2[q][3]
              - vir_mem_addr_w2[q][4]
              - vir_mem_addr_w2[q][5]);
          // pi and D
          if q != total_num_vir_mem_accesses - 1 {
            vir_mem_addr_w3[q][3] = vir_mem_addr_w3[q][1]
              * (vir_mem_addr_w3[q + 1][2] + E::ONE - vir_mem_addr_w3[q + 1][0]);
          } else {
            vir_mem_addr_w3[q][3] = vir_mem_addr_w3[q][1];
          }
          vir_mem_addr_w3[q][2] = vir_mem_addr_w3[q][0] * vir_mem_addr_w3[q][3];
          vir_mem_addr_w3[q][4] = addr_vir_mems_list[q][0]
            * (addr_vir_mems_list[q][0]
              + addr_vir_mems_list[q][2]
              + vir_mem_addr_w2[q][3]
              + vir_mem_addr_w2[q][4]
              + vir_mem_addr_w2[q][5]);
          vir_mem_addr_w3[q][5] = addr_vir_mems_list[q][0];
        }
        let vir_mem_addr_w3_shifted_mat = [vir_mem_addr_w3[1..].to_vec(), vec![vec![E::ZERO; W3_WIDTH]]].concat();

        let (vir_mem_addr_w2_mle, vir_mem_addr_w2_p_comm, vir_mem_addr_w2_v_comm) = Self::mat_to_comm(&vir_mem_addr_w2, &poly_pp);
        let (vir_mem_addr_w3_mle, vir_mem_addr_w3_p_comm, vir_mem_addr_w3_v_comm) = Self::mat_to_comm(&vir_mem_addr_w3, &poly_pp);
        let (vir_mem_addr_w3_shifted_mle, vir_mem_addr_w3_shifted_p_comm, vir_mem_addr_w3_shifted_v_comm) = Self::mat_to_comm(&vir_mem_addr_w3_shifted_mat, &poly_pp);  

        for comm in vec![
          &vir_mem_addr_w2_v_comm,
          &vir_mem_addr_w3_v_comm,
          &vir_mem_addr_w3_shifted_v_comm,
        ] {
          Pcs::write_commitment(comm, transcript).unwrap();
        }

        let vir_mem_addr_w2_prover =
          ProverWitnessSecInfo::new(vec![vir_mem_addr_w2], vec![vir_mem_addr_w2_mle], vec![vir_mem_addr_w2_p_comm]);
        let vir_mem_addr_w3_prover =
          ProverWitnessSecInfo::new(vec![vir_mem_addr_w3], vec![vir_mem_addr_w3_mle], vec![vir_mem_addr_w3_p_comm]);
        let vir_mem_addr_w3_shifted_prover = ProverWitnessSecInfo::new(
          vec![vir_mem_addr_w3_shifted_mat],
          vec![vir_mem_addr_w3_shifted_mle],
          vec![vir_mem_addr_w3_shifted_p_comm],
        );

        (
          vir_mem_addr_w2_prover,
          Some(vir_mem_addr_w2_v_comm),
          vir_mem_addr_w3_prover,
          Some(vir_mem_addr_w3_v_comm),
          vir_mem_addr_w3_shifted_prover,
          Some(vir_mem_addr_w3_shifted_v_comm),
        )
      } else {
        (
          ProverWitnessSecInfo::dummy(),
          None,
          ProverWitnessSecInfo::dummy(),
          None,
          ProverWitnessSecInfo::dummy(),
          None,
        )
      }
    };
    timer_sec_gen.stop();

    timer_gen.stop();

    // --
    // WITNESS COMMITMENTS
    // --
    let timer_commit = Timer::new("input_commit");
    let (block_vars_prover, block_vars_v_comm_list) = Self::mats_to_prove_wit_sec(block_vars_mat, &poly_pp);
    let (exec_inputs_prover, exec_inputs_v_comm) = Self::mat_to_prove_wit_sec(exec_inputs_list, &poly_pp);
    for comm in block_vars_v_comm_list.iter() {
      Pcs::write_commitment(comm, transcript).unwrap();
    }
    Pcs::write_commitment(&exec_inputs_v_comm, transcript).unwrap();
    
    let init_phy_mems_prover = if total_num_init_phy_mem_accesses > 0 {
      Self::mat_to_prover_wit_sec_no_commit(init_phy_mems_list)
    } else {
      ProverWitnessSecInfo::dummy()
    };
    let init_vir_mems_prover = if total_num_init_vir_mem_accesses > 0 {
      Self::mat_to_prover_wit_sec_no_commit(init_vir_mems_list)
    } else {
      ProverWitnessSecInfo::dummy()
    };
    let (addr_phy_mems_prover, addr_phy_mems_comm, addr_phy_mems_shifted_prover, addr_phy_mems_shifted_comm) = {
      if total_num_phy_mem_accesses > 0 {
        // Remove the first entry and shift the remaining entries up by one
        let addr_phy_mems_shifted_list = vec![addr_phy_mems_list[1..].to_vec(), vec![vec![E::ZERO; PHY_MEM_WIDTH]]].concat();
        let (addr_phy_mems_prover, addr_phy_mems_v_comm) = Self::mat_to_prove_wit_sec(addr_phy_mems_list, &poly_pp);
        let (addr_phy_mems_shifted_prover, addr_phy_mems_shifted_v_comm) = Self::mat_to_prove_wit_sec(addr_phy_mems_shifted_list, &poly_pp);

        for comm in vec![
          &addr_phy_mems_v_comm,
          &addr_phy_mems_shifted_v_comm,
        ] {
          Pcs::write_commitment(comm, transcript).unwrap();
        }

        (addr_phy_mems_prover, Some(addr_phy_mems_v_comm), addr_phy_mems_shifted_prover, Some(addr_phy_mems_shifted_v_comm))
      } else {
        (ProverWitnessSecInfo::dummy(), None, ProverWitnessSecInfo::dummy(), None)
      }
    };
    let (addr_vir_mems_prover, addr_vir_mems_comm, addr_vir_mems_shifted_prover, addr_vir_mems_shifted_comm, addr_ts_bits_prover, addr_ts_bits_comm) = {
      if total_num_vir_mem_accesses > 0 {
        // Remove the first entry and shift the remaining entries up by one
        let addr_vir_mems_shifted_list = vec![addr_vir_mems_list[1..].to_vec(), vec![vec![E::ZERO; VIR_MEM_WIDTH]]].concat();
        let (addr_vir_mems_prover, addr_vir_mems_v_comm) = Self::mat_to_prove_wit_sec(addr_vir_mems_list, &poly_pp);
        let (addr_vir_mems_shifted_prover, addr_vir_mems_shifted_v_comm) = Self::mat_to_prove_wit_sec(addr_vir_mems_shifted_list, &poly_pp);
        let (addr_ts_bits_prover, addr_ts_bits_v_comm) = Self::mat_to_prove_wit_sec(addr_ts_bits_list, &poly_pp);

        for comm in vec![
          &addr_vir_mems_v_comm,
          &addr_vir_mems_shifted_v_comm,
          &addr_ts_bits_v_comm,
        ] {
          Pcs::write_commitment(comm, transcript).unwrap();
        }

        (
          addr_vir_mems_prover,
          Some(addr_vir_mems_v_comm),
          addr_vir_mems_shifted_prover,
          Some(addr_vir_mems_shifted_v_comm),
          addr_ts_bits_prover,
          Some(addr_ts_bits_v_comm),
        )
      } else {
        (
          ProverWitnessSecInfo::dummy(),
          None,
          ProverWitnessSecInfo::dummy(),
          None,
          ProverWitnessSecInfo::dummy(),
          None,
        )
      }
    };
    timer_commit.stop();

    // Record total size of witnesses:
    let block_witness_sizes: Vec<usize> = [
      block_vars_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
      block_w2_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
      block_w3_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
      block_w3_shifted_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
    ]
    .concat();
    let exec_witness_sizes: Vec<usize> = [
      exec_inputs_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
      perm_exec_w2_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
      perm_exec_w3_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
      perm_exec_w3_shifted_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
    ]
    .concat();
    let mem_witness_sizes: Vec<usize> = [
      addr_phy_mems_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
      phy_mem_addr_w2_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
      phy_mem_addr_w3_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
      phy_mem_addr_w3_shifted_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
      addr_vir_mems_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
      addr_ts_bits_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
      vir_mem_addr_w2_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
      vir_mem_addr_w3_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
      vir_mem_addr_w3_shifted_prover
        .poly_w
        .iter()
        .map(|i| i.evaluations.len())
        .collect::<Vec<usize>>(),
    ]
    .concat();

    println!("BLOCK WITNESSES: {:?} Goldilocks", block_witness_sizes);
    println!("EXEC WITNESSES: {:?} Goldilocks", exec_witness_sizes);
    println!("MEM WITNESSES: {:?} Goldilocks", mem_witness_sizes);

    // --
    // BLOCK_CORRECTNESS_EXTRACT
    // --
    let timer_proof = Timer::new("Block Correctness Extract");
    let block_wit_secs = vec![
      &block_vars_prover,
      &block_w2_prover,
      &perm_w0_prover,
      &block_w3_prover,
      &block_w3_shifted_prover,
    ];

    let (block_r1cs_sat_proof, block_challenges) = {
      let (proof, block_challenges) = {
        R1CSProof::prove(
          block_num_instances,
          block_max_num_proofs,
          block_num_proofs,
          num_vars,
          block_wit_secs,
          &block_inst.inst,
          transcript,
        )
      };

      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, block_challenges)
    };

    // Final evaluation on BLOCK
    let (block_inst_evals_bound_rp, block_inst_evals_list, block_r1cs_eval_proof_list) = {
      let [rp, _, rx, ry] = block_challenges;
      let timer_eval = Timer::new("eval_sparse_polys");

      // Per instance evaluation is unsorted
      let inst_evals_list = block_inst_unsorted.inst.multi_evaluate::<true>(&rx, &ry);
      // RP-bound evaluation is sorted
      let (_, inst_evals_bound_rp) = block_inst
        .inst
        .multi_evaluate_bound_rp::<true>(&rp, &rx, &ry);
      timer_eval.stop();

      for r in &inst_evals_list {
        append_field_to_transcript(b"ABCr_claim", transcript, *r);
      }

      // Sample random combinations of A, B, C for inst_evals_bound_rp check in the Verifier
      // The random values are not used by the prover, but need to be appended to the transcript
      let _: E = challenge_scalar(transcript, b"challenge_c0");
      let _: E = challenge_scalar(transcript, b"challenge_c1");
      let _: E = challenge_scalar(transcript, b"challenge_c2");

      let r1cs_eval_proof_list = {
        let mut r1cs_eval_proof_list = Vec::new();
        for i in 0..block_comm_list.len() {
          let proof = R1CSEvalProof::prove::<true>(
            &block_decomm_list[i].decomm,
            &rx,
            &ry,
            &block_comm_map[i]
              .iter()
              .map(|i| inst_evals_list[*i])
              .collect(),
            transcript,
            &mut random_tape,
          );

          let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
          Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));

          r1cs_eval_proof_list.push(proof);
        }
        r1cs_eval_proof_list
      };

      (
        [
          inst_evals_bound_rp.0,
          inst_evals_bound_rp.1,
          inst_evals_bound_rp.2,
        ],
        inst_evals_list,
        r1cs_eval_proof_list,
      )
    };
    timer_proof.stop();

    // --
    // PAIRWISE_CHECK
    // --
    let timer_proof = Timer::new("Pairwise Check");
    let pairwise_size = [
      consis_num_proofs,
      total_num_phy_mem_accesses,
      total_num_vir_mem_accesses,
    ]
    .iter()
    .max()
    .unwrap()
    .clone();
    let (pairwise_w0_prover, inst_map) = ProverWitnessSecInfo::merge(vec![
      &perm_exec_w3_prover,
      &addr_phy_mems_prover,
      &addr_ts_bits_prover,
    ]);
    let (pairwise_w1_prover, _) = ProverWitnessSecInfo::merge(vec![
      &perm_exec_w3_shifted_prover,
      &addr_phy_mems_shifted_prover,
      &addr_vir_mems_prover,
    ]);
    let dummy_w2 = ProverWitnessSecInfo::pad();
    let pairwise_w2_prover = {
      let mut components = vec![&dummy_w2; inst_map.len()];
      for i in 0..inst_map.len() {
        if inst_map[i] == 2 {
          components[i] = &addr_vir_mems_shifted_prover;
        }
      }
      ProverWitnessSecInfo::concat(components)
    };
    let pairwise_num_instances = pairwise_w0_prover.w_mat.len();
    let pairwise_num_proofs: Vec<usize> = pairwise_w0_prover.w_mat.iter().map(|i| i.len()).collect();
    let (pairwise_check_r1cs_sat_proof, pairwise_check_challenges) = {
      let (proof, pairwise_check_challenges) = {
        R1CSProof::prove(
          pairwise_num_instances,
          pairwise_size,
          &pairwise_num_proofs,
          max(8, mem_addr_ts_bits_size),
          vec![
            &pairwise_w0_prover,
            &pairwise_w1_prover,
            &pairwise_w2_prover,
          ],
          &pairwise_check_inst.inst,
          transcript,
        )
      };

      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, pairwise_check_challenges)
    };

    // Final evaluation on PAIRWISE_CHECK
    let (
      pairwise_check_inst_evals_bound_rp,
      pairwise_check_inst_evals_list,
      pairwise_check_r1cs_eval_proof,
    ) = {
      let [rp, _, rx, ry] = pairwise_check_challenges;
      let timer_eval = Timer::new("eval_sparse_polys");

      // Per instance evaluation is unsorted
      let inst_evals_list = pairwise_check_inst_unsorted
        .inst
        .multi_evaluate::<false>(&rx, &ry);
      // RP-bound evaluation is sorted
      let (_, inst_evals_bound_rp) = pairwise_check_inst
        .inst
        .multi_evaluate_bound_rp::<false>(&rp, &rx, &ry);
      timer_eval.stop();

      for r in &inst_evals_list {
        append_field_to_transcript(b"ABCr_claim", transcript, *r);
      }
      // Sample random combinations of A, B, C for inst_evals_bound_rp check in the Verifier
      // The random values are not used by the prover, but need to be appended to the transcript
      let _: E = challenge_scalar(transcript, b"challenge_c0");
      let _: E = challenge_scalar(transcript, b"challenge_c1");
      let _: E = challenge_scalar(transcript, b"challenge_c2");

      let r1cs_eval_proof = {
        let proof = R1CSEvalProof::prove::<false>(
          &pairwise_check_decomm.decomm,
          &rx,
          &ry,
          &inst_evals_list,
          transcript,
          &mut random_tape,
        );

        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
        proof
      };

      (
        [
          inst_evals_bound_rp.0,
          inst_evals_bound_rp.1,
          inst_evals_bound_rp.2,
        ],
        inst_evals_list,
        r1cs_eval_proof,
      )
    };
    // Correctness of the shift will be handled in SHIFT_PROOFS
    timer_proof.stop();

    // --
    // PERM_EXEC_ROOT, MEM_ADDR_ROOT
    // --
    let timer_proof = Timer::new("Perm Root");
    let perm_size = [
      consis_num_proofs,
      total_num_init_phy_mem_accesses,
      total_num_init_vir_mem_accesses,
      total_num_phy_mem_accesses,
      total_num_vir_mem_accesses,
    ]
    .iter()
    .max()
    .unwrap()
    .clone();
    let (perm_root_w1_prover, _) = ProverWitnessSecInfo::merge(vec![
      &exec_inputs_prover,
      &init_phy_mems_prover,
      &init_vir_mems_prover,
      &addr_phy_mems_prover,
      &addr_vir_mems_prover,
    ]);
    let (perm_root_w2_prover, _) = ProverWitnessSecInfo::merge(vec![
      &perm_exec_w2_prover,
      &init_phy_mem_w2_prover,
      &init_vir_mem_w2_prover,
      &phy_mem_addr_w2_prover,
      &vir_mem_addr_w2_prover,
    ]);
    let (perm_root_w3_prover, _) = ProverWitnessSecInfo::merge(vec![
      &perm_exec_w3_prover,
      &init_phy_mem_w3_prover,
      &init_vir_mem_w3_prover,
      &phy_mem_addr_w3_prover,
      &vir_mem_addr_w3_prover,
    ]);
    let (perm_root_w3_shifted_prover, _) = ProverWitnessSecInfo::merge(vec![
      &perm_exec_w3_shifted_prover,
      &init_phy_mem_w3_shifted_prover,
      &init_vir_mem_w3_shifted_prover,
      &phy_mem_addr_w3_shifted_prover,
      &vir_mem_addr_w3_shifted_prover,
    ]);
    let perm_root_num_instances = perm_root_w1_prover.w_mat.len();
    let perm_root_num_proofs: Vec<usize> =
      perm_root_w1_prover.w_mat.iter().map(|i| i.len()).collect();
    let (perm_root_r1cs_sat_proof, perm_root_challenges) = {
      let (proof, perm_root_challenges) = {
        R1CSProof::prove(
          perm_root_num_instances,
          perm_size,
          &perm_root_num_proofs,
          num_ios,
          vec![
            &perm_w0_prover,
            &perm_root_w1_prover,
            &perm_root_w2_prover,
            &perm_root_w3_prover,
            &perm_root_w3_shifted_prover,
          ],
          &perm_root_inst.inst,
          transcript,
        )
      };

      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, perm_root_challenges)
    };

    // Final evaluation on PERM_ROOT
    let (perm_root_inst_evals, perm_root_r1cs_eval_proof) = {
      let [_, _, rx, ry] = perm_root_challenges;
      let inst = perm_root_inst;
      let timer_eval = Timer::new("eval_sparse_polys");
      let inst_evals = {
        let (Ar, Br, Cr) = inst.inst.evaluate(&rx, &ry);

        for (val, tag) in [(Ar, b"Ar_claim"), (Br, b"Br_claim"), (Cr, b"Cr_claim")].into_iter() {
          append_field_to_transcript(tag, transcript, val);
        }

        [Ar, Br, Cr]
      };
      timer_eval.stop();

      let r1cs_eval_proof = {
        let proof = R1CSEvalProof::prove::<false>(
          &perm_root_decomm.decomm,
          &rx,
          &ry,
          &inst_evals.to_vec(),
          transcript,
          &mut random_tape,
        );

        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
        proof
      };

      (inst_evals, r1cs_eval_proof)
    };
    timer_proof.stop();

    // --
    // PERM_PRODUCT_PROOF
    // --
    /*
    let timer_proof = Timer::new("Perm Product");
    // Record the prod of exec, blocks, mem_block, & mem_addr
    let (perm_poly_poly_list, proof_eval_perm_poly_prod_list) = {
      let (perm_poly_w3_prover, inst_map) = {
        let mut components = vec![
          &perm_exec_w3_prover,
          &init_phy_mem_w3_prover,
          &init_vir_mem_w3_prover,
          &phy_mem_addr_w3_prover,
          &vir_mem_addr_w3_prover,
          &block_w3_prover,
        ];
        if max_block_num_phy_ops > 0 {
          components.push(&block_w3_prover);
        }
        if max_block_num_vir_ops > 0 {
          components.push(&block_w3_prover);
        }
        ProverWitnessSecInfo::merge(components)
      };
      let pm_bl_id = 6;
      let vm_bl_id = if max_block_num_phy_ops > 0 { 7 } else { 6 };
      // PHY_MEM_BLOCK takes r = 4, VIR_MEM_BLOCK takes r = 6, everything else takes r = 2
      let perm_poly_poly_list: Vec<E> = (0..inst_map.len())
        .map(|i| {
          let p: &DensePolynomial<E> = &perm_poly_w3_prover.poly_w[i];
          let i = inst_map[i];
          if i == vm_bl_id {
            p[6]
          } else if i == pm_bl_id {
            p[4]
          } else {
            p[2]
          }
        })
        .collect();
      let two_b = vec![E::ONE, E::ZERO];
      let four_b = vec![E::ONE, E::ZERO, E::ZERO];
      let six_b = vec![E::ONE, E::ONE, E::ZERO];
      let r_list: Vec<&Vec<E>> = inst_map
        .iter()
        .map(|i| {
          if *i == vm_bl_id {
            &six_b
          } else if *i == pm_bl_id {
            &four_b
          } else {
            &two_b
          }
        })
        .collect();
      let proof_eval_perm_poly_prod_list = PolyEvalProof::prove_batched_instances(
        &perm_poly_w3_prover.poly_w,
        r_list,
        &perm_poly_poly_list,
        transcript,
        &mut random_tape,
      );
      (perm_poly_poly_list, proof_eval_perm_poly_prod_list)
    };
    timer_proof.stop();

    // --
    // SHIFT_PROOFS
    // --
    // Prove in the order of
    // - perm_block_w3 => shift by 4
    // - perm_exec_w3 => shift by 8
    // - (if exist) init_mem_w3 => shift by 8
    // - (if exist) addr_phy_mems => shift by 4
    // - (if exist) phy_mem_addr_w3 => shift by 8
    // - (if exist) addr_vir_mems => shift by 8
    // - (if exist) vir_mem_addr_w3 => shift by 8
    let timer_proof = Timer::new("Shift Proofs");
    let shift_proof = {
      // perm_exec_w3
      let mut orig_polys = vec![&perm_exec_w3_prover.poly_w[0]];
      let mut shifted_polys = vec![&perm_exec_w3_shifted_prover.poly_w[0]];
      let mut header_len_list = vec![6];
      // block_w3
      for poly in &block_w3_prover.poly_w {
        orig_polys.push(poly);
      }
      for poly in &block_w3_shifted_prover.poly_w {
        shifted_polys.push(poly);
      }
      header_len_list.extend(vec![8; block_num_instances]);
      // init_phy_mem_w3, init_vir_mem_w3
      if total_num_init_phy_mem_accesses > 0 {
        orig_polys.push(&init_phy_mem_w3_prover.poly_w[0]);
        shifted_polys.push(&init_phy_mem_w3_shifted_prover.poly_w[0]);
        header_len_list.push(6);
      }
      if total_num_init_vir_mem_accesses > 0 {
        orig_polys.push(&init_vir_mem_w3_prover.poly_w[0]);
        shifted_polys.push(&init_vir_mem_w3_shifted_prover.poly_w[0]);
        header_len_list.push(6);
      }
      // addr_phy_mems, phy_mem_addr_w3
      if total_num_phy_mem_accesses > 0 {
        orig_polys.push(&addr_phy_mems_prover.poly_w[0]);
        shifted_polys.push(&addr_phy_mems_shifted_prover.poly_w[0]);
        header_len_list.push(4);
        orig_polys.push(&phy_mem_addr_w3_prover.poly_w[0]);
        shifted_polys.push(&phy_mem_addr_w3_shifted_prover.poly_w[0]);
        header_len_list.push(6);
      }
      // addr_vir_mems, vir_mem_addr_w3
      if total_num_vir_mem_accesses > 0 {
        orig_polys.push(&addr_vir_mems_prover.poly_w[0]);
        shifted_polys.push(&addr_vir_mems_shifted_prover.poly_w[0]);
        header_len_list.push(6);
        orig_polys.push(&vir_mem_addr_w3_prover.poly_w[0]);
        shifted_polys.push(&vir_mem_addr_w3_shifted_prover.poly_w[0]);
        header_len_list.push(6);
      }
      /*
      let shift_proof = ShiftProofs::prove(
        orig_polys,
        shifted_polys,
        header_len_list,
        transcript,
        &mut random_tape,
      );
      shift_proof
      */
    };
    timer_proof.stop();

    // --
    // IO_PROOFS
    // --

    let timer_proof = Timer::new("IO Proofs");
    let io_proof = IOProofs::prove(
      &exec_inputs_prover.poly_w[0],
      num_ios,
      num_inputs_unpadded,
      consis_num_proofs,
      input_block_num,
      output_block_num,
      input_liveness,
      input_offset,
      output_offset,
      input,
      output,
      output_exec_num,
      transcript,
      &mut random_tape,
    );
    timer_proof.stop();
    */

    timer_prove.stop();

    SNARK {
      poly_vp,
      block_vars_comm_list: block_vars_v_comm_list,
      exec_inputs_comm: exec_inputs_v_comm,
      addr_phy_mems_comm,
      addr_phy_mems_shifted_comm,
      addr_vir_mems_comm,
      addr_vir_mems_shifted_comm,
      addr_ts_bits_comm,

      perm_exec_w2_comm,
      perm_exec_w3_comm,
      perm_exec_w3_shifted_comm,
      block_w2_comm_list,
      block_w3_comm_list,
      block_w3_shifted_comm_list,

      init_phy_mem_w2_comm,
      init_phy_mem_w3_comm,
      init_phy_mem_w3_shifted_comm,
      init_vir_mem_w2_comm,
      init_vir_mem_w3_comm,
      init_vir_mem_w3_shifted_comm,

      phy_mem_addr_w2_comm,
      phy_mem_addr_w3_comm,
      phy_mem_addr_w3_shifted_comm,
      vir_mem_addr_w2_comm,
      vir_mem_addr_w3_comm,
      vir_mem_addr_w3_shifted_comm,

      block_r1cs_sat_proof,
      block_inst_evals_bound_rp,
      block_inst_evals_list,
      block_r1cs_eval_proof_list,

      pairwise_check_r1cs_sat_proof,
      pairwise_check_inst_evals_bound_rp,
      pairwise_check_inst_evals_list,
      pairwise_check_r1cs_eval_proof,

      perm_root_r1cs_sat_proof,
      perm_root_inst_evals,
      perm_root_r1cs_eval_proof,
      // perm_poly_poly_list,
      // proof_eval_perm_poly_prod_list,

      // shift_proof,
      // io_proof,
    }
  }

  /// A method to verify the SNARK proof of the satisfiability of an R1CS instance
  pub fn verify(
    &self,
    input_block_num: usize,
    output_block_num: usize,
    input_liveness: &Vec<bool>,
    func_input_width: usize,
    input_offset: usize,
    output_offset: usize,
    input: &Vec<[u8; 32]>,
    input_stack: &Vec<[u8; 32]>,
    input_mem: &Vec<[u8; 32]>,
    output: &[u8; 32],
    output_exec_num: usize,

    num_vars: usize,
    num_ios: usize,
    max_block_num_phy_ops: usize,
    block_num_phy_ops: &Vec<usize>,
    max_block_num_vir_ops: usize,
    block_num_vir_ops: &Vec<usize>,
    mem_addr_ts_bits_size: usize,

    num_inputs_unpadded: usize,
    // How many variables (witnesses) are used by each block? Round to the next power of 2
    block_num_vars: &Vec<usize>,
    block_num_instances_bound: usize,

    block_max_num_proofs: usize,
    block_num_proofs: &Vec<usize>,
    block_num_cons: usize,
    block_comm_map: &Vec<Vec<usize>>,
    block_comm_list: &Vec<ComputationCommitment<E>>,

    consis_num_proofs: usize,
    total_num_init_phy_mem_accesses: usize,
    total_num_init_vir_mem_accesses: usize,
    total_num_phy_mem_accesses: usize,
    total_num_vir_mem_accesses: usize,
    pairwise_check_num_cons: usize,
    pairwise_check_comm: &ComputationCommitment<E>,

    perm_root_num_cons: usize,
    perm_root_comm: &ComputationCommitment<E>,

    transcript: &mut Transcript<E>,
  ) -> Result<(), ProofVerifyError> {
    let (_, block_size, pairwise_size, perm_size) = self.compute_size();
    let meta_size =
      // usize
      19 * std::mem::size_of::<usize>() +
      // Vec<usize> or Vec<Vec<usize>>
      bincode::serialize(block_num_phy_ops).unwrap().len() +
      bincode::serialize(block_num_vir_ops).unwrap().len() +
      bincode::serialize(block_num_vars).unwrap().len() +
      bincode::serialize(block_num_proofs).unwrap().len() +
      bincode::serialize(block_comm_map).unwrap().len() +
      // Other vectors
      bincode::serialize(input).unwrap().len() +
      bincode::serialize(output).unwrap().len();
    // Everything else
    // bincode::serialize(vars_gens).unwrap().len();

    let timer_verify = Timer::new("SNARK::verify");
    append_protocol_name(
      transcript,
      SNARK::<E, Pcs>::protocol_name(),
    );

    // --
    // ASSERTIONS
    // --
    assert!(0 < consis_num_proofs);
    for p in 0..block_num_instances_bound {
      assert!(block_num_proofs[p] <= block_max_num_proofs);
    }

    // --
    // COMMITMENTS
    // --
    let input_block_num = E::from(input_block_num as u64);
    let output_block_num = E::from(output_block_num as u64);
    let input: Vec<E> = input.iter().map(|i| from_bytes(i).unwrap()).collect();
    let input_stack: Vec<E> = input_stack
      .iter()
      .map(|i| from_bytes(i).unwrap())
      .collect();
    let input_mem: Vec<E> = input_mem
      .iter()
      .map(|i| from_bytes(i).unwrap())
      .collect();
    let output: E = from_bytes(output).unwrap();
    {
      let timer_commit = Timer::new("inst_commit");
      // Commit public parameters
      append_field_to_transcript(
        b"func_input_width",
        transcript,
        E::from(func_input_width as u64),
      );
      append_field_to_transcript(b"input_offset", transcript, E::from(input_offset as u64));
      append_field_to_transcript(b"output_offset", transcript, E::from(output_offset as u64));
      append_field_to_transcript(
        b"output_exec_num",
        transcript,
        E::from(output_exec_num as u64),
      );
      append_field_to_transcript(b"num_ios", transcript, E::from(num_ios as u64));

      for n in block_num_vars {
        append_field_to_transcript(b"block_num_vars", transcript, E::from(*n as u64));
      }
      append_field_to_transcript(
        b"mem_addr_ts_bits_size",
        transcript,
        E::from(mem_addr_ts_bits_size as u64),
      );
      append_field_to_transcript(
        b"num_inputs_unpadded",
        transcript,
        E::from(num_inputs_unpadded as u64),
      );
      append_field_to_transcript(
        b"block_num_instances_bound",
        transcript,
        E::from(block_num_instances_bound as u64),
      );
      append_field_to_transcript(
        b"block_max_num_proofs",
        transcript,
        E::from(block_max_num_proofs as u64),
      );

      for p in block_num_phy_ops {
        append_field_to_transcript(b"block_num_phy_ops", transcript, E::from(*p as u64));
      }
      for v in block_num_vir_ops {
        append_field_to_transcript(b"block_num_vir_ops", transcript, E::from(*v as u64));
      }
      append_field_to_transcript(
        b"total_num_init_phy_mem_accesses",
        transcript,
        E::from(total_num_init_phy_mem_accesses as u64),
      );
      append_field_to_transcript(
        b"total_num_init_vir_mem_accesses",
        transcript,
        E::from(total_num_init_vir_mem_accesses as u64),
      );
      append_field_to_transcript(
        b"total_num_phy_mem_accesses",
        transcript,
        E::from(total_num_phy_mem_accesses as u64),
      );
      append_field_to_transcript(
        b"total_num_vir_mem_accesses",
        transcript,
        E::from(total_num_vir_mem_accesses as u64),
      );

      // commit num_proofs
      append_field_to_transcript(
        b"block_max_num_proofs",
        transcript,
        E::from(block_max_num_proofs as u64),
      );

      for n in block_num_proofs {
        append_field_to_transcript(b"block_num_proofs", transcript, E::from(*n as u64));
      }

      // append a commitment to the computation to the transcript
      for b in block_comm_map {
        for l in b {
          append_field_to_transcript(b"block_comm_map", transcript, E::from(*l as u64));
        }
      }
      for c in block_comm_list {
        c.comm.append_to_transcript(b"block_comm", transcript);
      }
      pairwise_check_comm
        .comm
        .append_to_transcript(b"pairwise_comm", transcript);
      perm_root_comm
        .comm
        .append_to_transcript(b"perm_comm", transcript);

      // Commit io
      append_field_to_transcript(b"input_block_num", transcript, input_block_num);
      append_field_to_transcript(b"output_block_num", transcript, output_block_num);
      append_field_vector_to_transcript(b"input_list", transcript, &input);
      append_field_to_transcript(b"output_list", transcript, output);

      timer_commit.stop();
    }

    // --
    // BLOCK SORT
    // --
    // Block_num_instance is the number of non-zero entries in block_num_proofs
    let timer_sort = Timer::new("block_sort");
    let block_num_instances = block_num_proofs
      .iter()
      .fold(0, |i, j| if *j > 0 { i + 1 } else { i });
    // Sort the following based on block_num_proofs:
    // - block_num_proofs
    // - block_inst, block_comm, block_decomm
    // - block_num_phy_mem_accesses
    // - mem_extract_inst, mem_extract_decomm
    let mut inst_sorter = Vec::new();
    for i in 0..block_num_instances_bound {
      inst_sorter.push(InstanceSortHelper::new(block_num_proofs[i], i))
    }
    // Sort from high -> low
    inst_sorter.sort_by(|a, b| b.cmp(a));

    let inst_sorter = &inst_sorter[..block_num_instances];
    let mut block_num_proofs: Vec<usize> = inst_sorter.iter().map(|i| i.num_exec).collect();
    // index[i] = j => the original jth entry should now be at the ith position
    let block_index: Vec<usize> = inst_sorter.iter().map(|i| i.index).collect();
    let block_num_vars: Vec<usize> = (0..block_num_instances).map(|i| block_num_vars[block_index[i]]).collect();
    let block_num_phy_ops: Vec<usize> = (0..block_num_instances)
      .map(|i| block_num_phy_ops[block_index[i]])
      .collect();
    let block_num_vir_ops: Vec<usize> = (0..block_num_instances)
      .map(|i| block_num_vir_ops[block_index[i]])
      .collect();

    // --
    // PADDING
    // --
    // Pad entries of block_num_proofs to a power of 2
    let block_max_num_proofs = block_max_num_proofs.next_power_of_two();
    for i in 0..block_num_instances {
      block_num_proofs[i] = block_num_proofs[i].next_power_of_two();
    }
    // Pad exec_inputs, addr_phy_mems, addr_vir_mems with dummys so the length is a power of 2
    let consis_num_proofs = consis_num_proofs.next_power_of_two();
    let total_num_init_phy_mem_accesses = if total_num_init_phy_mem_accesses == 0 {
      0
    } else {
      total_num_init_phy_mem_accesses.next_power_of_two()
    };
    let total_num_init_vir_mem_accesses = if total_num_init_vir_mem_accesses == 0 {
      0
    } else {
      total_num_init_vir_mem_accesses.next_power_of_two()
    };
    let total_num_phy_mem_accesses = if total_num_phy_mem_accesses == 0 {
      0
    } else {
      total_num_phy_mem_accesses.next_power_of_two()
    };
    let total_num_vir_mem_accesses = if total_num_vir_mem_accesses == 0 {
      0
    } else {
      total_num_vir_mem_accesses.next_power_of_two()
    };

    // Pad num_proofs with 1 until the next power of 2
    block_num_proofs.extend(vec![
      1;
      block_num_instances.next_power_of_two()
        - block_num_instances
    ]);
    let block_num_proofs = &block_num_proofs;

    // --
    // PAIRWISE SORT
    // --
    // Sort the pairwise instances: CONSIS_CHECK, PHY_MEM_COHERE
    let mut inst_sorter = Vec::new();
    inst_sorter.push(InstanceSortHelper::new(consis_num_proofs, 0));
    inst_sorter.push(InstanceSortHelper::new(total_num_phy_mem_accesses, 1));
    inst_sorter.push(InstanceSortHelper::new(total_num_vir_mem_accesses, 2));
    // Sort from high -> low
    inst_sorter.sort_by(|a, b| b.cmp(a));

    let pairwise_num_instances = 1
      + if total_num_phy_mem_accesses > 0 { 1 } else { 0 }
      + if total_num_vir_mem_accesses > 0 { 1 } else { 0 };
    let inst_sorter = &inst_sorter[..pairwise_num_instances];
    // index[i] = j => the original jth entry should now be at the ith position
    let pairwise_index: Vec<usize> = inst_sorter.iter().map(|i| i.index).collect();
    timer_sort.stop();

    // --
    // SAMPLE CHALLENGES, COMMIT WITNESSES, & CONSTRUCT WITNESS_SEC_INFO
    // --
    let timer_commit = Timer::new("witness_commit");

    let comb_tau = challenge_scalar(transcript, b"challenge_tau");
    let comb_r = challenge_scalar(transcript, b"challenge_r");

    let (
      perm_w0_verifier,
      perm_exec_w2_verifier,
      perm_exec_w3_verifier,
      perm_exec_w3_shifted_verifier,
      block_w2_verifier,
      block_w3_verifier,
      block_w3_shifted_verifier,
    ) = {
      // Let the verifier generate perm_w0 itself
      let mut perm_w0 = vec![comb_tau];
      let mut r_tmp = comb_r;
      for _ in 1..2 * num_inputs_unpadded {
        perm_w0.push(r_tmp);
        r_tmp = r_tmp * comb_r;
      }
      perm_w0.extend(vec![E::ZERO; num_ios - 2 * num_inputs_unpadded]);
      // create a multilinear polynomial using the supplied assignment for variables
      let _perm_poly_w0 = DensePolynomial::new(perm_w0.clone());

      // block_w2
      let block_w2_verifier = {
        let block_w2_size_list: Vec<usize> = (0..block_num_instances)
          .map(|i| {
            (2 * num_inputs_unpadded + 2 * block_num_phy_ops[i] + 4 * block_num_vir_ops[i])
              .next_power_of_two()
          })
          .collect();
        VerifierWitnessSecInfo::new(block_w2_size_list, &block_num_proofs, self.block_w2_comm_list.clone())
      };
      (
        VerifierWitnessSecInfo::new(vec![num_ios], &vec![1], vec![Pcs::Commitment::default()]),
        VerifierWitnessSecInfo::new(vec![num_ios], &vec![consis_num_proofs], vec![self.perm_exec_w2_comm.clone()]),
        VerifierWitnessSecInfo::new(vec![W3_WIDTH], &vec![consis_num_proofs], vec![self.perm_exec_w3_comm.clone()]),
        VerifierWitnessSecInfo::new(vec![W3_WIDTH], &vec![consis_num_proofs], vec![self.perm_exec_w3_shifted_comm.clone()]),
        block_w2_verifier,
        VerifierWitnessSecInfo::new(
          vec![W3_WIDTH; block_num_instances],
          &block_num_proofs.clone(),
          self.block_w3_comm_list.clone(),
        ),
        VerifierWitnessSecInfo::new(
          vec![W3_WIDTH; block_num_instances],
          &block_num_proofs.clone(),
          self.block_w3_shifted_comm_list.clone(),
        ),
      )
    };

    // Append commmitments to transcript
    for comm in vec![
      &self.perm_exec_w2_comm,
      &self.perm_exec_w3_comm,
      &self.perm_exec_w3_shifted_comm,
    ] {
      Pcs::write_commitment(comm, transcript).unwrap();
    }
    for comm in self.block_w2_comm_list.iter() {
      Pcs::write_commitment(comm, transcript).unwrap();
    }
    for comm in self.block_w3_comm_list.iter() {
      Pcs::write_commitment(comm, transcript).unwrap();
    }
    for comm in self.block_w3_shifted_comm_list.iter() {
      Pcs::write_commitment(comm, transcript).unwrap();
    }

    let (init_phy_mem_w2_verifier, init_phy_mem_w3_verifier, init_phy_mem_w3_shifted_verifier) = {
      if total_num_init_phy_mem_accesses > 0 {
        (
          VerifierWitnessSecInfo::new(
            vec![INIT_PHY_MEM_WIDTH],
            &vec![total_num_init_phy_mem_accesses],
            vec![self.init_phy_mem_w2_comm.clone().expect("commitment should exist")]
          ),
          VerifierWitnessSecInfo::new(vec![W3_WIDTH], &vec![total_num_init_phy_mem_accesses], vec![self.init_phy_mem_w3_comm.clone().expect("commitment should exist")]),
          VerifierWitnessSecInfo::new(vec![W3_WIDTH], &vec![total_num_init_phy_mem_accesses], vec![self.init_phy_mem_w3_shifted_comm.clone().expect("commitment should exist")]),
        )
      } else {
        (
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
        )
      }
    };

    let (init_vir_mem_w2_verifier, init_vir_mem_w3_verifier, init_vir_mem_w3_shifted_verifier) = {
      if total_num_init_vir_mem_accesses > 0 {
        (
          VerifierWitnessSecInfo::new(
            vec![INIT_VIR_MEM_WIDTH],
            &vec![total_num_init_vir_mem_accesses],
            vec![self.init_vir_mem_w2_comm.clone().expect("commitment should exist")],
          ),
          VerifierWitnessSecInfo::new(vec![W3_WIDTH], &vec![total_num_init_vir_mem_accesses], vec![self.init_vir_mem_w3_comm.clone().expect("commitment should exist")]),
          VerifierWitnessSecInfo::new(vec![W3_WIDTH], &vec![total_num_init_vir_mem_accesses], vec![self.init_vir_mem_w3_shifted_comm.clone().expect("commitment should exist")]),
        )
      } else {
        (
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
        )
      }
    };

    let (phy_mem_addr_w2_verifier, phy_mem_addr_w3_verifier, phy_mem_addr_w3_shifted_verifier) = {
      if total_num_phy_mem_accesses > 0 {
        (
          VerifierWitnessSecInfo::new(vec![PHY_MEM_WIDTH], &vec![total_num_phy_mem_accesses], vec![self.phy_mem_addr_w2_comm.clone().expect("commitment should exist")]),
          VerifierWitnessSecInfo::new(vec![W3_WIDTH], &vec![total_num_phy_mem_accesses], vec![self.phy_mem_addr_w3_comm.clone().expect("commitment should exist")]),
          VerifierWitnessSecInfo::new(vec![W3_WIDTH], &vec![total_num_phy_mem_accesses], vec![self.phy_mem_addr_w3_shifted_comm.clone().expect("commitment should exist")]),
        )
      } else {
        (
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
        )
      }
    };

    let (vir_mem_addr_w2_verifier, vir_mem_addr_w3_verifier, vir_mem_addr_w3_shifted_verifier) = {
      if total_num_vir_mem_accesses > 0 {
        Pcs::write_commitment(self.vir_mem_addr_w2_comm.as_ref().clone().expect("valid commitment expected"), transcript).unwrap();
        Pcs::write_commitment(self.vir_mem_addr_w3_comm.as_ref().clone().expect("valid commitment expected"), transcript).unwrap();
        Pcs::write_commitment(self.vir_mem_addr_w3_shifted_comm.as_ref().clone().expect("valid commitment expected"), transcript).unwrap();

        (
          VerifierWitnessSecInfo::new(vec![VIR_MEM_WIDTH], &vec![total_num_vir_mem_accesses], vec![self.vir_mem_addr_w2_comm.clone().expect("valid commitment expected")]),
          VerifierWitnessSecInfo::new(vec![W3_WIDTH], &vec![total_num_vir_mem_accesses], vec![self.vir_mem_addr_w3_comm.clone().expect("valid commitment expected")]),
          VerifierWitnessSecInfo::new(vec![W3_WIDTH], &vec![total_num_vir_mem_accesses], vec![self.vir_mem_addr_w3_shifted_comm.clone().expect("valid commitment expected")]),
        )
      } else {
        (
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
        )
      }
    };

    let (block_vars_verifier, exec_inputs_verifier) = {
      // add the commitment to the verifier's transcript
      for comm in self.block_vars_comm_list.iter() {
        Pcs::write_commitment(comm, transcript).unwrap();
      }
      Pcs::write_commitment(&self.exec_inputs_comm, transcript).unwrap();

      (
        VerifierWitnessSecInfo::new(block_num_vars, &block_num_proofs, self.block_vars_comm_list.clone()),
        VerifierWitnessSecInfo::new(vec![num_ios], &vec![consis_num_proofs], vec![self.exec_inputs_comm.clone()]),
      )
    };

    let init_phy_mems_verifier = {
      if input_stack.len() > 0 {
        assert_eq!(
          total_num_init_phy_mem_accesses,
          input_stack.len().next_power_of_two()
        );
        // Let the verifier generate init_mems itself
        let init_stacks = [
          (0..input_stack.len())
            .map(|i| {
              vec![
                E::ONE,
                E::ZERO,
                E::from(i as u64),
                input_stack[i].clone(),
              ]
            })
            .concat(),
          vec![
            E::ZERO;
            INIT_PHY_MEM_WIDTH * (total_num_init_phy_mem_accesses - input_stack.len())
          ],
        ]
        .concat();
        // create a multilinear polynomial using the supplied assignment for variables
        let _poly_init_stacks = DensePolynomial::new(init_stacks.clone());
        VerifierWitnessSecInfo::new(
          vec![INIT_PHY_MEM_WIDTH],
          &vec![total_num_init_phy_mem_accesses],
          vec![Pcs::Commitment::default()],
        )
      } else {
        VerifierWitnessSecInfo::dummy()
      }
    };
    let init_vir_mems_verifier = {
      if input_mem.len() > 0 {
        assert_eq!(
          total_num_init_vir_mem_accesses,
          input_mem.len().next_power_of_two()
        );
        // Let the verifier generate init_mems itself
        let init_mems = [
          (0..input_mem.len())
            .map(|i| {
              vec![
                E::ONE,
                E::ZERO,
                E::from(i as u64),
                input_mem[i].clone(),
              ]
            })
            .concat(),
          vec![
            E::ZERO;
            INIT_VIR_MEM_WIDTH * (total_num_init_vir_mem_accesses - input_mem.len())
          ],
        ]
        .concat();
        // create a multilinear polynomial using the supplied assignment for variables
        let _poly_init_mems = DensePolynomial::new(init_mems.clone());
        VerifierWitnessSecInfo::new(
          vec![INIT_VIR_MEM_WIDTH],
          &vec![total_num_init_vir_mem_accesses],
          vec![Pcs::Commitment::default()],
        )
      } else {
        VerifierWitnessSecInfo::dummy()
      }
    };

    let (addr_phy_mems_verifier, addr_phy_mems_shifted_verifier) = {
      if total_num_phy_mem_accesses > 0 {
        Pcs::write_commitment(&self.addr_phy_mems_comm.clone().expect("valid commitment expected"), transcript).unwrap();
        Pcs::write_commitment(&self.addr_phy_mems_shifted_comm.clone().expect("valid commitment expected"), transcript).unwrap();

        (
          VerifierWitnessSecInfo::new(vec![PHY_MEM_WIDTH], &vec![total_num_phy_mem_accesses], vec![self.addr_phy_mems_comm.clone().expect("commitment should exist")]),
          VerifierWitnessSecInfo::new(vec![PHY_MEM_WIDTH], &vec![total_num_phy_mem_accesses], vec![self.addr_phy_mems_shifted_comm.clone().expect("commitment should exist")]),
        )
      } else {
        (
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
        )
      }
    };

    let (addr_vir_mems_verifier, addr_vir_mems_shifted_verifier, addr_ts_bits_verifier) = {
      if total_num_vir_mem_accesses > 0 {
        Pcs::write_commitment(self.addr_vir_mems_comm.clone().as_ref().expect("valid commitment expected"), transcript).unwrap();
        Pcs::write_commitment(self.addr_vir_mems_shifted_comm.clone().as_ref().expect("valid commitment expected"), transcript).unwrap();
        Pcs::write_commitment(self.addr_ts_bits_comm.clone().as_ref().expect("valid commitment expected"), transcript).unwrap();

        (
          VerifierWitnessSecInfo::new(vec![VIR_MEM_WIDTH], &vec![total_num_vir_mem_accesses], vec![self.addr_vir_mems_comm.clone().expect("commitment should exist")]),
          VerifierWitnessSecInfo::new(vec![VIR_MEM_WIDTH], &vec![total_num_vir_mem_accesses], vec![self.addr_vir_mems_shifted_comm.clone().expect("commitment should exist")]),
          VerifierWitnessSecInfo::new(
            vec![mem_addr_ts_bits_size],
            &vec![total_num_vir_mem_accesses],
            vec![self.addr_ts_bits_comm.clone().expect("commitment should exist")],
          ),
        )
      } else {
        (
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
        )
      }
    };
    timer_commit.stop();

    // --
    // BLOCK_CORRECTNESS_EXTRACT
    // --
    {
      let timer_sat_proof = Timer::new("Block Correctness Extract Sat");
      let block_wit_secs = vec![
        &block_vars_verifier,
        &block_w2_verifier,
        &perm_w0_verifier,
        &block_w3_verifier,
        &block_w3_shifted_verifier,
      ];

      let block_challenges = self.block_r1cs_sat_proof.verify(
        block_num_instances,
        block_max_num_proofs,
        block_num_proofs,
        num_vars,
        block_wit_secs,
        block_num_cons,
        &self.block_inst_evals_bound_rp,
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("Block Correctness Extract Eval");
      // Verify Evaluation on BLOCK
      let [_rp, _, rx, ry] = block_challenges;

      for r in &self.block_inst_evals_list {
        append_field_to_transcript(b"ABCr_claim", transcript, *r);
      }

      // Sample random combinations of A, B, C for inst_evals_bound_rp check
      let c0: E = challenge_scalar(transcript, b"challenge_c0");
      let c1: E = challenge_scalar(transcript, b"challenge_c1");
      let c2: E = challenge_scalar(transcript, b"challenge_c2");

      let ABC_evals: Vec<E> = (0..block_num_instances_bound)
        .map(|i| {
          c0 * self.block_inst_evals_list[3 * i]
            + c1 * self.block_inst_evals_list[3 * i + 1]
            + c2 * self.block_inst_evals_list[3 * i + 2]
        })
        .collect();

      for i in 0..block_comm_list.len() {
        self.block_r1cs_eval_proof_list[i].verify::<true>(
          &block_comm_list[i].comm,
          &rx,
          &ry,
          &block_comm_map[i]
            .iter()
            .map(|i| self.block_inst_evals_list[*i])
            .collect(),
          transcript,
        )?;
      }

      // Permute block_inst_evals_list to the correct order for RP evaluation
      let _ABC_evals: Vec<E> = (0..block_num_instances)
        .map(|i| ABC_evals[block_index[i]])
        .collect();

      timer_eval_proof.stop();
    }

    // --
    // PAIRWISE_CHECK
    // --
    {
      let timer_sat_proof = Timer::new("Pairwise Check Sat");

      let pairwise_size = [
        consis_num_proofs,
        total_num_phy_mem_accesses,
        total_num_vir_mem_accesses,
      ]
      .iter()
      .max()
      .unwrap()
      .clone();
      let (pairwise_w0_verifier, inst_map) = VerifierWitnessSecInfo::merge(vec![
        &perm_exec_w3_verifier,
        &addr_phy_mems_verifier,
        &addr_ts_bits_verifier
      ]);
      let (pairwise_w1_verifier, _) = VerifierWitnessSecInfo::merge(vec![
        &perm_exec_w3_shifted_verifier,
        &addr_phy_mems_shifted_verifier,
        &addr_vir_mems_verifier,
      ]);
      let dummy_w2 = VerifierWitnessSecInfo::pad();
      let pairwise_w2_verifier = {
        let mut components = vec![&dummy_w2; inst_map.len()];
        for i in 0..inst_map.len() {
          if inst_map[i] == 2 {
            components[i] = &addr_vir_mems_shifted_verifier;
          }
        }
        VerifierWitnessSecInfo::concat(components)
      };
      let pairwise_num_instances = pairwise_w0_verifier.num_proofs.len();
      let pairwise_num_proofs: Vec<usize> = pairwise_w0_verifier.num_proofs.clone();

      let pairwise_check_challenges = self.pairwise_check_r1cs_sat_proof.verify(
        pairwise_num_instances,
        pairwise_size,
        &pairwise_num_proofs,
        max(8, mem_addr_ts_bits_size),
        vec![
          &pairwise_w0_verifier,
          &pairwise_w1_verifier,
          &pairwise_w2_verifier,
        ],
        pairwise_check_num_cons,
        &self.pairwise_check_inst_evals_bound_rp,
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("Pairwise Check Eval");
      // Verify Evaluation on CONSIS_CHECK
      let [_rp, _, rx, ry] = pairwise_check_challenges;

      for r in &self.pairwise_check_inst_evals_list {
        append_field_to_transcript(b"ABCr_claim", transcript, *r);
      }
      // Sample random combinations of A, B, C for inst_evals_bound_rp check
      let c0: E = challenge_scalar(transcript, b"challenge_c0");
      let c1: E = challenge_scalar(transcript, b"challenge_c1");
      let c2: E = challenge_scalar(transcript, b"challenge_c2");

      let ABC_evals: Vec<E> = (0..3)
        .map(|i| {
          c0 * self.pairwise_check_inst_evals_list[3 * i]
            + c1 * self.pairwise_check_inst_evals_list[3 * i + 1]
            + c2 * self.pairwise_check_inst_evals_list[3 * i + 2]
        })
        .collect();

      self.pairwise_check_r1cs_eval_proof.verify::<false>(
        &pairwise_check_comm.comm,
        &rx,
        &ry,
        &self.pairwise_check_inst_evals_list,
        transcript,
      )?;
      // Permute pairwise_check_inst_evals_list to the correct order for RP evaluation
      let _ABC_evals: Vec<E> = (0..pairwise_num_instances)
        .map(|i| ABC_evals[pairwise_index[i]])
        .collect();

      // Correctness of the shift will be handled in SHIFT_PROOFS
      timer_eval_proof.stop();
    };

    // --
    // PERM_EXEC_ROOT, MEM_ADDR_ROOT
    // --
    {
      let perm_size = [
        consis_num_proofs,
        total_num_init_phy_mem_accesses,
        total_num_init_vir_mem_accesses,
        total_num_phy_mem_accesses,
        total_num_vir_mem_accesses,
      ]
      .iter()
      .max()
      .unwrap()
      .clone();
      let timer_sat_proof = Timer::new("Perm Root Sat");
      let (perm_root_w1_verifier, _) = VerifierWitnessSecInfo::merge(vec![
        &exec_inputs_verifier,
        &init_phy_mems_verifier,
        &init_vir_mems_verifier,
        &addr_phy_mems_verifier,
        &addr_vir_mems_verifier,
      ]);
      let (perm_root_w2_verifier, _) = VerifierWitnessSecInfo::merge(vec![
        &perm_exec_w2_verifier,
        &init_phy_mem_w2_verifier,
        &init_vir_mem_w2_verifier,
        &phy_mem_addr_w2_verifier,
        &vir_mem_addr_w2_verifier,
      ]);
      let (perm_root_w3_verifier, _) = VerifierWitnessSecInfo::merge(vec![
        &perm_exec_w3_verifier,
        &init_phy_mem_w3_verifier,
        &init_vir_mem_w3_verifier,
        &phy_mem_addr_w3_verifier,
        &vir_mem_addr_w3_verifier,
      ]);
      let (perm_root_w3_shifted_verifier, _) = VerifierWitnessSecInfo::merge(vec![
        &perm_exec_w3_shifted_verifier,
        &init_phy_mem_w3_shifted_verifier,
        &init_vir_mem_w3_shifted_verifier,
        &phy_mem_addr_w3_shifted_verifier,
        &vir_mem_addr_w3_shifted_verifier,
      ]);
      let perm_root_num_instances = perm_root_w1_verifier.num_proofs.len();
      let perm_root_num_proofs: Vec<usize> = perm_root_w1_verifier.num_proofs.clone();
      let perm_block_root_challenges = self.perm_root_r1cs_sat_proof.verify(
        perm_root_num_instances,
        perm_size,
        &perm_root_num_proofs,
        num_ios,
        vec![
          &perm_w0_verifier,
          &perm_root_w1_verifier,
          &perm_root_w2_verifier,
          &perm_root_w3_verifier,
          &perm_root_w3_shifted_verifier,
        ],
        perm_root_num_cons,
        &self.perm_root_inst_evals,
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("Perm Root Eval");
      // Verify Evaluation on PERM_BLOCK_ROOT
      let [Ar, Br, Cr] = &self.perm_root_inst_evals;
      for (val, tag) in [(Ar, b"Ar_claim"), (Br, b"Br_claim"), (Cr, b"Cr_claim")].into_iter() {
        append_field_to_transcript(tag, transcript, *val);
      }
      let [_, _, rx, ry] = perm_block_root_challenges;
      self.perm_root_r1cs_eval_proof.verify::<false>(
        &perm_root_comm.comm,
        &rx,
        &ry,
        &self.perm_root_inst_evals.to_vec(),
        transcript,
      )?;
      timer_eval_proof.stop();
    }

    // --
    // PERM_PRODUCT_PROOF
    // --
    /*
    {
      let timer_eval_opening = Timer::new("Perm Product");
      // Verify prod of exec, blocks, mem_block, & mem_addr
      let (perm_poly_w3_verifier, inst_map) = {
        let mut components = vec![
          &perm_exec_w3_verifier,
          &init_phy_mem_w3_verifier,
          &init_vir_mem_w3_verifier,
          &phy_mem_addr_w3_verifier,
          &vir_mem_addr_w3_verifier,
          &block_w3_verifier,
        ];
        if max_block_num_phy_ops > 0 {
          components.push(&block_w3_verifier);
        }
        if max_block_num_vir_ops > 0 {
          components.push(&block_w3_verifier);
        }
        VerifierWitnessSecInfo::merge(components)
      };
      let pm_bl_id = 6;
      let vm_bl_id = if max_block_num_phy_ops > 0 { 7 } else { 6 };

      let perm_poly_num_instances = perm_poly_w3_verifier.num_proofs.len();
      let mut perm_poly_num_proofs: Vec<usize> = perm_poly_w3_verifier.num_proofs.clone();
      perm_poly_num_proofs.extend(vec![
        1;
        perm_poly_num_instances.next_power_of_two()
          - perm_poly_num_instances
      ]);
      let perm_poly_num_inputs: Vec<usize> = vec![8; perm_poly_num_instances];

      // Commitment Opening
      let num_vars_list = (0..perm_poly_num_instances)
        .map(|i| (perm_poly_num_proofs[i] * perm_poly_num_inputs[i]).log_2())
        .collect();
      let two_b = vec![E::ONE, E::ZERO];
      let four_b = vec![E::ONE, E::ZERO, E::ZERO];
      let six_b = vec![E::ONE, E::ONE, E::ZERO];
      let r_list: Vec<&Vec<E>> = inst_map
        .iter()
        .map(|i| {
          if *i == vm_bl_id {
            &six_b
          } else if *i == pm_bl_id {
            &four_b
          } else {
            &two_b
          }
        })
        .collect();
      PolyEvalProof::verify_plain_batched_instances(
        &self.proof_eval_perm_poly_prod_list,
        transcript,
        r_list,
        &self.perm_poly_poly_list,
        &num_vars_list,
      )?;

      // Compute poly for PERM_EXEC, PERM_BLOCK, MEM_BLOCK, MEM_ADDR base on INST_MAP
      let mut perm_block_poly_bound_tau = E::ONE;
      let mut perm_exec_poly_bound_tau = E::ONE;
      let mut phy_mem_block_poly_bound_tau = E::ONE;
      let mut phy_mem_addr_poly_bound_tau = E::ONE;
      let mut vir_mem_block_poly_bound_tau = E::ONE;
      let mut vir_mem_addr_poly_bound_tau = E::ONE;
      // INST_MAP:
      //   0 -> perm_exec,
      //   1 -> init_phy_mem, count towards phy_mem_block
      //   2 -> init_mem, count towards vir_mem_block
      //   3 -> phy_mem_block,
      //   4 -> vir_mem_block,
      //   5 -> perm_block,
      //   6 -> phy_mem_addr,
      //   7 -> vir_mem_addr
      for p in 0..perm_poly_num_instances {
        match inst_map[p] {
          0 => {
            perm_exec_poly_bound_tau = perm_exec_poly_bound_tau * self.perm_poly_poly_list[p];
          }
          1 => {
            phy_mem_block_poly_bound_tau =
              phy_mem_block_poly_bound_tau * self.perm_poly_poly_list[p];
          }
          2 => {
            vir_mem_block_poly_bound_tau =
              vir_mem_block_poly_bound_tau * self.perm_poly_poly_list[p];
          }
          3 => {
            phy_mem_addr_poly_bound_tau = phy_mem_addr_poly_bound_tau * self.perm_poly_poly_list[p];
          }
          4 => {
            vir_mem_addr_poly_bound_tau = vir_mem_addr_poly_bound_tau * self.perm_poly_poly_list[p];
          }
          5 => {
            perm_block_poly_bound_tau = perm_block_poly_bound_tau * self.perm_poly_poly_list[p];
          }
          6 => {
            if max_block_num_phy_ops > 0 {
              phy_mem_block_poly_bound_tau =
                phy_mem_block_poly_bound_tau * self.perm_poly_poly_list[p];
            } else {
              vir_mem_block_poly_bound_tau =
                vir_mem_block_poly_bound_tau * self.perm_poly_poly_list[p];
            }
          }
          7 => {
            vir_mem_block_poly_bound_tau =
              vir_mem_block_poly_bound_tau * self.perm_poly_poly_list[p];
          }
          _ => {}
        }
      }
      timer_eval_opening.stop();

      // Correctness of Permutation
      assert_eq!(perm_block_poly_bound_tau, perm_exec_poly_bound_tau);

      // Correctness of Memory
      assert_eq!(phy_mem_block_poly_bound_tau, phy_mem_addr_poly_bound_tau);
      assert_eq!(vir_mem_block_poly_bound_tau, vir_mem_addr_poly_bound_tau);
    };

    // --
    // SHIFT_PROOFS
    // --
    let timer_proof = Timer::new("Shift Proofs");
    {
      let mut poly_size_list = [
        vec![8 * consis_num_proofs],
        (0..block_num_instances)
          .map(|i| 8 * block_num_proofs[i])
          .collect(),
      ]
      .concat();
      let mut shift_size_list = [vec![8], vec![8; block_num_instances]].concat();
      let mut header_len_list = [vec![6], vec![8; block_num_instances]].concat();
      // init_phy_mem_w3, init_vir_mem_w3
      if total_num_init_phy_mem_accesses > 0 {
        poly_size_list.push(8 * total_num_init_phy_mem_accesses);
        shift_size_list.push(8);
        header_len_list.push(6);
      }
      if total_num_init_vir_mem_accesses > 0 {
        poly_size_list.push(8 * total_num_init_vir_mem_accesses);
        shift_size_list.push(8);
        header_len_list.push(6);
      }
      // addr_phy_mems, phy_mem_addr_w3
      if total_num_phy_mem_accesses > 0 {
        poly_size_list.push(4 * total_num_phy_mem_accesses);
        shift_size_list.push(4);
        header_len_list.push(4);
        poly_size_list.push(8 * total_num_phy_mem_accesses);
        shift_size_list.push(8);
        header_len_list.push(6);
      }
      // addr_vir_mems, vir_mem_addr_w3
      if total_num_vir_mem_accesses > 0 {
        poly_size_list.push(8 * total_num_vir_mem_accesses);
        shift_size_list.push(8);
        header_len_list.push(6);
        poly_size_list.push(8 * total_num_vir_mem_accesses);
        shift_size_list.push(8);
        header_len_list.push(6);
      }

      /*
      self
        .shift_proof
        .verify(poly_size_list, shift_size_list, header_len_list, transcript)?;
      */
    }
    timer_proof.stop();

    // --
    // IO_PROOFS
    // --
    let timer_proof = Timer::new("IO Proofs");
    self.io_proof.verify(
      num_ios,
      num_inputs_unpadded,
      consis_num_proofs,
      input_block_num,
      output_block_num,
      input_liveness,
      input_offset,
      output_offset,
      input,
      output,
      output_exec_num,
      transcript,
    )?;
    timer_proof.stop();
    */

    timer_verify.stop();

    println!("BLOCK SUMCHECK SIZE: {} bytes", block_size);
    println!("PAIRWISE SUMCHECK SIZE: {} bytes", pairwise_size);
    println!("PERM SUMCHECK SIZE: {} bytes", perm_size);
    println!("META SIZE: {} bytes", meta_size);

    Ok(())
  }
}
