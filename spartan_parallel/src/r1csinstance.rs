use rayon::prelude::*;

use std::cmp::{max, min};
use std::collections::HashMap;

use crate::scalar::SpartanExtensionField;
use crate::transcript::AppendToTranscript;

use super::custom_dense_mlpoly::DensePolynomialPqx;
use super::dense_mlpoly::DensePolynomial;
use super::errors::ProofVerifyError;
use super::math::Math;
use super::random::RandomTape;
use super::sparse_mlpoly::{
  MultiSparseMatPolynomialAsDense, SparseMatEntry, SparseMatPolyCommitment, SparseMatPolyEvalProof,
  SparseMatPolynomial,
};
use super::timer::Timer;
use flate2::{write::ZlibEncoder, Compression};
use merlin::Transcript;
use serde::{Deserialize, Serialize};
use std::iter::zip;

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct R1CSInstance<S: SpartanExtensionField> {
  // num_instances DOES NOT need to be a power of 2!
  num_instances: usize,
  // num_cons and num_vars need to be power of 2
  max_num_cons: usize,
  num_cons: Vec<usize>,
  max_num_vars: usize,
  num_vars: Vec<usize>,
  // List of individual A, B, C for matrix multiplication
  A_list: Vec<SparseMatPolynomial<S>>,
  B_list: Vec<SparseMatPolynomial<S>>,
  C_list: Vec<SparseMatPolynomial<S>>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct R1CSCommitment<S: SpartanExtensionField> {
  num_cons: usize,
  num_vars: usize,
  comm: SparseMatPolyCommitment<S>,
}

impl<S: SpartanExtensionField> AppendToTranscript for R1CSCommitment<S> {
  fn append_to_transcript(&self, _label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_u64(b"num_cons", self.num_cons as u64);
    transcript.append_u64(b"num_vars", self.num_vars as u64);
    self.comm.append_to_transcript(b"comm", transcript);
  }
}

pub struct R1CSDecommitment<S: SpartanExtensionField> {
  num_cons: usize,
  num_vars: usize,
  dense: MultiSparseMatPolynomialAsDense<S>,
}

impl<S: SpartanExtensionField> R1CSCommitment<S> {
  pub fn get_num_cons(&self) -> usize {
    self.num_cons
  }

  pub fn get_num_vars(&self) -> usize {
    self.num_vars
  }
}

impl<S: SpartanExtensionField + Send + Sync> R1CSInstance<S> {
  pub fn new(
    num_instances: usize,
    max_num_cons: usize,
    num_cons: Vec<usize>,
    max_num_vars: usize,
    num_vars: Vec<usize>,
    A_list: &Vec<Vec<(usize, usize, S)>>,
    B_list: &Vec<Vec<(usize, usize, S)>>,
    C_list: &Vec<Vec<(usize, usize, S)>>,
  ) -> R1CSInstance<S> {
    Timer::print(&format!("number_of_instances {num_instances}"));
    Timer::print(&format!("number_of_constraints {max_num_cons}"));
    Timer::print(&format!("number_of_variables {max_num_vars}"));
    // Timer::print(&format!("number_non-zero_entries_A {}", A.len()));
    // Timer::print(&format!("number_non-zero_entries_B {}", B.len()));
    // Timer::print(&format!("number_non-zero_entries_C {}", C.len()));

    // check that num_cons is a power of 2
    assert_eq!(max_num_cons.next_power_of_two(), max_num_cons);
    for c in &num_cons {
      assert_eq!(c.next_power_of_two(), *c);
      assert!(*c <= max_num_cons);
    }

    // check that num_vars is a power of 2
    assert_eq!(max_num_vars.next_power_of_two(), max_num_vars);
    for v in &num_vars {
      assert_eq!(v.next_power_of_two(), *v);
      assert!(*v <= max_num_vars);
    }

    // check that length of A_list, B_list, C_list are the same
    assert_eq!(A_list.len(), B_list.len());
    assert_eq!(B_list.len(), C_list.len());

    // no errors, so create polynomials
    let mut poly_A_list = Vec::new();
    let mut poly_B_list = Vec::new();
    let mut poly_C_list = Vec::new();

    let mut mat_A = Vec::new();
    let mut mat_B = Vec::new();
    let mut mat_C = Vec::new();

    for inst in 0..A_list.len() {
      let num_poly_vars_x = num_cons[inst].log_2();
      let num_poly_vars_y = num_vars[inst].log_2();

      let A = &A_list[inst];
      let B = &B_list[inst];
      let C = &C_list[inst];
      let list_A = (0..A.len())
        .map(|i| SparseMatEntry::new(A[i].0, A[i].1, A[i].2))
        .collect::<Vec<SparseMatEntry<S>>>();
      let list_B = (0..B.len())
        .map(|i| SparseMatEntry::new(B[i].0, B[i].1, B[i].2))
        .collect::<Vec<SparseMatEntry<S>>>();
      let list_C = (0..C.len())
        .map(|i| SparseMatEntry::new(C[i].0, C[i].1, C[i].2))
        .collect::<Vec<SparseMatEntry<S>>>();
      poly_A_list.push(SparseMatPolynomial::new(
        num_poly_vars_x,
        num_poly_vars_y,
        list_A,
      ));
      poly_B_list.push(SparseMatPolynomial::new(
        num_poly_vars_x,
        num_poly_vars_y,
        list_B,
      ));
      poly_C_list.push(SparseMatPolynomial::new(
        num_poly_vars_x,
        num_poly_vars_y,
        list_C,
      ));
      let mut list_A = (0..A.len())
        .map(|i| SparseMatEntry::new(inst * max_num_cons + A[i].0, A[i].1, A[i].2))
        .collect::<Vec<SparseMatEntry<S>>>();
      let mut list_B = (0..B.len())
        .map(|i| SparseMatEntry::new(inst * max_num_cons + B[i].0, B[i].1, B[i].2))
        .collect::<Vec<SparseMatEntry<S>>>();
      let mut list_C = (0..C.len())
        .map(|i| SparseMatEntry::new(inst * max_num_cons + C[i].0, C[i].1, C[i].2))
        .collect::<Vec<SparseMatEntry<S>>>();
      mat_A.append(&mut list_A);
      mat_B.append(&mut list_B);
      mat_C.append(&mut list_C);
    }

    R1CSInstance {
      num_instances,
      max_num_cons,
      num_cons: num_cons.clone(),
      max_num_vars,
      num_vars: num_vars.clone(),
      A_list: poly_A_list,
      B_list: poly_B_list,
      C_list: poly_C_list,
    }
  }

  // Sort A_list, B_list, C_list based on index
  // index[i] = j => the original jth entry should now be at the ith position
  pub fn sort(&mut self, num_instances: usize, index: &Vec<usize>) {
    self.num_instances = num_instances;
    self.num_cons = (0..num_instances)
      .map(|i| self.num_cons[index[i]])
      .collect();
    self.A_list = (0..num_instances)
      .map(|i| self.A_list[index[i]].clone())
      .collect();
    self.B_list = (0..num_instances)
      .map(|i| self.B_list[index[i]].clone())
      .collect();
    self.C_list = (0..num_instances)
      .map(|i| self.C_list[index[i]].clone())
      .collect();
  }

  pub fn get_num_instances(&self) -> usize {
    self.num_instances
  }

  pub fn get_num_vars(&self) -> usize {
    self.max_num_vars
  }

  pub fn get_inst_num_vars(&self) -> &Vec<usize> {
    &self.num_vars
  }

  pub fn get_num_cons(&self) -> usize {
    self.max_num_cons
  }

  pub fn get_inst_num_cons(&self) -> &Vec<usize> {
    &self.num_cons
  }

  pub fn get_digest(&self) -> Vec<u8> {
    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
    bincode::serialize_into(&mut encoder, &self).unwrap();
    encoder.finish().unwrap()
  }

  // Az(p, q, x) <- A(p, x) * z(p, q, x), where we require p for A and z are the same
  // Return Az, Bz, Cz as DensePolynomialPqx
  pub fn multiply_vec_block(
    &self,
    num_instances: usize,
    num_proofs: Vec<usize>,
    max_num_proofs: usize,
    max_num_inputs: usize,
    max_num_cons: usize,
    num_cons: Vec<usize>,
    z_mat: &Vec<Vec<Vec<Vec<S>>>>,
  ) -> (
    DensePolynomialPqx<S>,
    DensePolynomialPqx<S>,
    DensePolynomialPqx<S>,
  ) {
    assert!(self.num_instances == 1 || self.num_instances == num_instances);
    assert_eq!(max_num_cons, self.max_num_cons);
    let mut Az = Vec::new();
    let mut Bz = Vec::new();
    let mut Cz = Vec::new();

    // Non-zero instances
    for p in 0..num_instances {
      let p_inst = if self.num_instances == 1 { 0 } else { p };

      let z_list = &z_mat[p];
      assert!(num_proofs[p] <= max_num_proofs);
      Az.push(Vec::new());
      Bz.push(Vec::new());
      Cz.push(Vec::new());

      Az[p] = (0..num_proofs[p])
        .into_par_iter()
        .map(|q| {
          vec![self.A_list[p_inst].multiply_vec_disjoint_rounds(
            num_cons[p_inst].clone(),
            max_num_inputs,
            &z_list[q],
          )]
        })
        .collect();
      Bz[p] = (0..num_proofs[p])
        .into_par_iter()
        .map(|q| {
          vec![self.B_list[p_inst].multiply_vec_disjoint_rounds(
            num_cons[p_inst].clone(),
            max_num_inputs,
            &z_list[q],
          )]
        })
        .collect();
      Cz[p] = (0..num_proofs[p])
        .into_par_iter()
        .map(|q| {
          vec![self.C_list[p_inst].multiply_vec_disjoint_rounds(
            num_cons[p_inst].clone(),
            max_num_inputs,
            &z_list[q],
          )]
        })
        .collect();
    }

    (
      DensePolynomialPqx::new(Az),
      DensePolynomialPqx::new(Bz),
      DensePolynomialPqx::new(Cz),
    )
  }

  pub fn compute_eval_table_sparse(
    &self,
    num_instances: usize,
    num_rows: usize,
    num_cols: usize,
    evals: &[S],
  ) -> (Vec<S>, Vec<S>, Vec<S>) {
    assert!(self.num_instances == 1 || self.num_instances == num_instances);
    assert_eq!(num_rows, self.max_num_cons);
    assert_eq!(num_cols, self.max_num_vars);

    let mut evals_A_list = Vec::new();
    let mut evals_B_list = Vec::new();
    let mut evals_C_list = Vec::new();
    // If num_instances is 1, copy it for num_instances.next_power_of_two()
    if self.num_instances == 1 {
      let evals_A = self.A_list[0].compute_eval_table_sparse(evals, num_rows, num_cols);
      let evals_B = self.B_list[0].compute_eval_table_sparse(evals, num_rows, num_cols);
      let evals_C = self.C_list[0].compute_eval_table_sparse(evals, num_rows, num_cols);
      evals_A_list = vec![evals_A; num_instances.next_power_of_two()].concat();
      evals_B_list = vec![evals_B; num_instances.next_power_of_two()].concat();
      evals_C_list = vec![evals_C; num_instances.next_power_of_two()].concat();
    } else {
      // Non-zero instances
      for p in 0..num_instances {
        let evals_A = self.A_list[p].compute_eval_table_sparse(evals, num_rows, num_cols);
        let evals_B = self.B_list[p].compute_eval_table_sparse(evals, num_rows, num_cols);
        let evals_C = self.C_list[p].compute_eval_table_sparse(evals, num_rows, num_cols);
        evals_A_list.extend(evals_A);
        evals_B_list.extend(evals_B);
        evals_C_list.extend(evals_C);
      }
      // Zero instances
      for _ in num_instances..num_instances.next_power_of_two() {
        evals_A_list.extend(vec![S::field_zero(); num_cols]);
        evals_B_list.extend(vec![S::field_zero(); num_cols]);
        evals_C_list.extend(vec![S::field_zero(); num_cols]);
      }
    }

    (evals_A_list, evals_B_list, evals_C_list)
  }

  // Store the result in a vector divided into num_segs segments
  // output[p][q][w] stores entry w * max_num_cols ~ w * max_num_cols + num_cols of the original vector
  pub fn compute_eval_table_sparse_disjoint_rounds(
    &self,
    num_instances: usize,
    num_rows: &Vec<usize>,
    num_segs: usize,
    max_num_cols: usize,
    num_cols: &Vec<Vec<usize>>,
    evals: &[S],
    // Output in p, q, w, i format, where q section has length 1
  ) -> (
    Vec<Vec<Vec<Vec<S>>>>,
    Vec<Vec<Vec<Vec<S>>>>,
    Vec<Vec<Vec<Vec<S>>>>,
  ) {
    assert!(self.num_instances == 1 || self.num_instances == num_instances);
    assert_eq!(num_rows, &self.num_cons);
    assert_eq!(
      num_segs.next_power_of_two() * max_num_cols,
      self.max_num_vars
    );

    let mut evals_A_list = Vec::new();
    let mut evals_B_list = Vec::new();
    let mut evals_C_list = Vec::new();
    for p in 0..self.num_instances {
      let num_cols = *num_cols[p].iter().max().unwrap();
      let evals_A = self.A_list[p].compute_eval_table_sparse_disjoint_rounds(evals, num_rows[p], num_segs, max_num_cols, num_cols);
      let evals_B = self.B_list[p].compute_eval_table_sparse_disjoint_rounds(evals, num_rows[p], num_segs, max_num_cols, num_cols);
      let evals_C = self.C_list[p].compute_eval_table_sparse_disjoint_rounds(evals, num_rows[p], num_segs, max_num_cols, num_cols);
      evals_A_list.push(vec![evals_A]);
      evals_B_list.push(vec![evals_B]);
      evals_C_list.push(vec![evals_C]);
    }

    (evals_A_list, evals_B_list, evals_C_list)
  }

  // If IS_BLOCK, ry is truncated starting at the third entry
  pub fn multi_evaluate<const IS_BLOCK: bool>(&self, rx: &[S], ry: &[S]) -> Vec<S> {
    let mut eval_list = Vec::new();
    // Evaluate each individual poly on [rx, ry]
    for i in 0..self.num_instances {
      let num_cons = self.num_cons[i];
      let num_vars = self.num_vars[i];
      let rx_header = rx[..rx.len() - min(rx.len(), num_cons.log_2())]
        .iter()
        .fold(S::field_one(), |c, i| c * (S::field_one() - i.clone()));
      let rx_short = &rx[rx.len() - min(rx.len(), num_cons.log_2())..];
      let ry_skip_len = ry.len() - min(ry.len(), num_vars.log_2());
      let (ry_header, ry_short) = {
        if IS_BLOCK {
          let ry_header = ry[3..3 + ry_skip_len]
            .iter()
            .fold(S::field_one(), |c, i| c * (S::field_one() - i.clone()));
          let ry_short = [ry[..3].to_vec(), ry[3 + ry_skip_len..].to_vec()].concat();
          (ry_header, ry_short)
        } else {
          let ry_header = ry[0..ry_skip_len]
            .iter()
            .fold(S::field_one(), |c, i| c * (S::field_one() - i.clone()));
          let ry_short = ry[ry_skip_len..].to_vec();
          (ry_header, ry_short)
        }
      };

      let evals = SparseMatPolynomial::multi_evaluate(
        &[&self.A_list[i], &self.B_list[i], &self.C_list[i]],
        rx_short,
        &ry_short,
      );
      eval_list.extend(evals.into_iter().map(|i| rx_header * ry_header * i));
    }
    eval_list
  }

  pub fn multi_evaluate_bound_rp<const IS_BLOCK: bool>(
    &self,
    rp: &[S],
    rx: &[S],
    ry: &[S],
  ) -> (
    Vec<S>,    // Concatenation of each individual block
    (S, S, S), // Combined, bound to rp
  ) {
    let mut a_evals = Vec::new();
    let mut b_evals = Vec::new();
    let mut c_evals = Vec::new();
    let mut eval_list = Vec::new();
    // Evaluate each individual poly on [rx, ry]
    for i in 0..self.num_instances {
      let num_cons = self.num_cons[i];
      let num_vars = self.num_vars[i];
      let rx_header = rx[..rx.len() - min(rx.len(), num_cons.log_2())]
        .iter()
        .fold(S::field_one(), |c, i| c * (S::field_one() - i.clone()));
      let rx_short = &rx[rx.len() - min(rx.len(), num_cons.log_2())..];
      let ry_skip_len = ry.len() - min(ry.len(), num_vars.log_2());
      let (ry_header, ry_short) = {
        if IS_BLOCK {
          let ry_header = ry[3..3 + ry_skip_len]
            .iter()
            .fold(S::field_one(), |c, i| c * (S::field_one() - i.clone()));
          let ry_short = [ry[..3].to_vec(), ry[3 + ry_skip_len..].to_vec()].concat();
          (ry_header, ry_short)
        } else {
          let ry_header = ry[0..ry_skip_len]
            .iter()
            .fold(S::field_one(), |c, i| c * (S::field_one() - i.clone()));
          let ry_short = ry[ry_skip_len..].to_vec();
          (ry_header, ry_short)
        }
      };

      let evals = SparseMatPolynomial::multi_evaluate(
        &[&self.A_list[i], &self.B_list[i], &self.C_list[i]],
        rx_short,
        &ry_short,
      );
      let evals: Vec<S> = evals
        .into_iter()
        .map(|i| rx_header * ry_header * i)
        .collect();
      eval_list.extend(evals.clone());
      a_evals.push(evals[0]);
      b_evals.push(evals[1]);
      c_evals.push(evals[2]);
    }
    // Bind A, B, C to rp
    let a_eval = DensePolynomial::new(a_evals).evaluate(rp);
    let b_eval = DensePolynomial::new(b_evals).evaluate(rp);
    let c_eval = DensePolynomial::new(c_evals).evaluate(rp);
    let eval_bound_rp = (a_eval, b_eval, c_eval);

    (eval_list, eval_bound_rp)
  }

  // Used if there is only one instance
  pub fn evaluate(&self, rx: &[S], ry: &[S]) -> (S, S, S) {
    assert_eq!(self.num_instances, 1);

    let evals = SparseMatPolynomial::multi_evaluate(
      &[&self.A_list[0], &self.B_list[0], &self.C_list[0]],
      rx,
      ry,
    );
    (evals[0], evals[1], evals[2])
  }

  pub fn multi_commit(
    &self,
  ) -> (
    Vec<Vec<usize>>,
    Vec<R1CSCommitment<S>>,
    Vec<R1CSDecommitment<S>>,
  ) {
    let mut vars_size: HashMap<usize, usize> = HashMap::new();
    let mut label_map: Vec<Vec<usize>> = Vec::new();
    let mut sparse_polys_list: Vec<Vec<&SparseMatPolynomial<S>>> = Vec::new();
    let mut max_num_cons_list: Vec<usize> = Vec::new();
    let mut max_num_vars_list: Vec<usize> = Vec::new();

    // Group the instances based on number of variables, which are already orders of 2^4
    for i in 0..self.num_instances {
      let var_len = self.num_vars[i];
      // A_list, B_list, C_list
      if let Some(index) = vars_size.get(&var_len) {
        label_map[*index].push(3 * i);
        sparse_polys_list[*index].push(&self.A_list[i]);
        label_map[*index].push(3 * i + 1);
        sparse_polys_list[*index].push(&self.B_list[i]);
        label_map[*index].push(3 * i + 2);
        sparse_polys_list[*index].push(&self.C_list[i]);
        max_num_cons_list[*index] = max(max_num_cons_list[*index], self.num_cons[i]);
        max_num_vars_list[*index] = max(max_num_vars_list[*index], self.num_vars[i]);
      } else {
        let next_label = vars_size.len();
        vars_size.insert(var_len, next_label);
        label_map.push(vec![3 * i, 3 * i + 1, 3 * i + 2]);
        sparse_polys_list.push(vec![&self.A_list[i], &self.B_list[i], &self.C_list[i]]);
        max_num_cons_list.push(self.num_cons[i]);
        max_num_vars_list.push(self.num_vars[i]);
      }
    }

    let mut r1cs_comm_list = Vec::new();
    let mut r1cs_decomm_list = Vec::new();
    for ((sparse_polys, max_num_cons), max_num_vars) in
      zip(zip(sparse_polys_list, max_num_cons_list), max_num_vars_list)
    {
      let (comm, dense) = SparseMatPolynomial::multi_commit(&sparse_polys);
      let r1cs_comm = R1CSCommitment {
        num_cons: max_num_cons.next_power_of_two(),
        num_vars: max_num_vars,
        comm,
      };
      let r1cs_decomm = R1CSDecommitment {
        num_cons: max_num_cons.next_power_of_two(),
        num_vars: max_num_vars,
        dense,
      };

      r1cs_comm_list.push(r1cs_comm);
      r1cs_decomm_list.push(r1cs_decomm);
    }

    (label_map, r1cs_comm_list, r1cs_decomm_list)
  }

  // Used if there is only one instance
  pub fn commit(&self) -> (R1CSCommitment<S>, R1CSDecommitment<S>) {
    let mut sparse_polys = Vec::new();
    for i in 0..self.num_instances {
      sparse_polys.push(&self.A_list[i]);
      sparse_polys.push(&self.B_list[i]);
      sparse_polys.push(&self.C_list[i]);
    }

    let (comm, dense) = SparseMatPolynomial::multi_commit(&sparse_polys);
    let r1cs_comm = R1CSCommitment {
      num_cons: self.num_instances * self.max_num_cons,
      num_vars: self.max_num_vars,
      comm,
    };

    let r1cs_decomm = R1CSDecommitment {
      num_cons: self.num_instances * self.max_num_cons,
      num_vars: self.max_num_vars,
      dense,
    };

    (r1cs_comm, r1cs_decomm)
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct R1CSEvalProof<S: SpartanExtensionField> {
  proof: SparseMatPolyEvalProof<S>,
}

impl<S: SpartanExtensionField> R1CSEvalProof<S> {
  // If is BLOCK, separate the first 3 entries of ry out (corresponding to the 5 segments of witnesses)
  pub fn prove<const IS_BLOCK: bool>(
    decomm: &R1CSDecommitment<S>,
    rx: &[S], // point at which the polynomial is evaluated
    ry: &[S],
    evals: &Vec<S>,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape<S>,
  ) -> R1CSEvalProof<S> {
    let timer = Timer::new("R1CSEvalProof::prove");
    let rx_skip_len = rx.len() - min(rx.len(), decomm.num_cons.log_2());
    let rx_header = rx[..rx_skip_len]
      .iter()
      .fold(S::field_one(), |c, i| c * (S::field_one() - i.clone()));
    let rx_short = &rx[rx_skip_len..];
    let ry_skip_len = ry.len() - min(ry.len(), decomm.num_vars.log_2());
    let (ry_header, ry_short) = {
      if IS_BLOCK {
        let ry_header = ry[3..3 + ry_skip_len]
          .iter()
          .fold(S::field_one(), |c, i| c * (S::field_one() - i.clone()));
        let ry_short = [ry[..3].to_vec(), ry[3 + ry_skip_len..].to_vec()].concat();
        (ry_header, ry_short)
      } else {
        let ry_header = ry[0..ry_skip_len]
          .iter()
          .fold(S::field_one(), |c, i| c * (S::field_one() - i.clone()));
        let ry_short = ry[ry_skip_len..].to_vec();
        (ry_header, ry_short)
      }
    };
    // let ry_short = &ry[..min(ry.len(), decomm.num_vars.log_2())];
    let proof = SparseMatPolyEvalProof::prove(
      &decomm.dense,
      rx_header * ry_header,
      rx_short,
      &ry_short,
      evals,
      transcript,
      random_tape,
    );
    timer.stop();

    R1CSEvalProof { proof }
  }

  pub fn verify<const IS_BLOCK: bool>(
    &self,
    comm: &R1CSCommitment<S>,
    rx: &[S], // point at which the R1CS matrix polynomials are evaluated
    ry: &[S],
    evals: &Vec<S>,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    let rx_header = rx[..rx.len() - min(rx.len(), comm.num_cons.log_2())]
      .iter()
      .fold(S::field_one(), |c, i| c * (S::field_one() - i.clone()));
    let rx_short = &rx[rx.len() - min(rx.len(), comm.num_cons.log_2())..];
    let ry_skip_len = ry.len() - min(ry.len(), comm.num_vars.log_2());
    let (ry_header, ry_short) = {
      if IS_BLOCK {
        let ry_header = ry[3..3 + ry_skip_len]
          .iter()
          .fold(S::field_one(), |c, i| c * (S::field_one() - i.clone()));
        let ry_short = [ry[..3].to_vec(), ry[3 + ry_skip_len..].to_vec()].concat();
        (ry_header, ry_short)
      } else {
        let ry_header = ry[0..ry_skip_len]
          .iter()
          .fold(S::field_one(), |c, i| c * (S::field_one() - i.clone()));
        let ry_short = ry[ry_skip_len..].to_vec();
        (ry_header, ry_short)
      }
    };
    self.proof.verify(
      &comm.comm,
      rx_header * ry_header,
      rx_short,
      &ry_short,
      evals,
      transcript,
    )
  }
}
