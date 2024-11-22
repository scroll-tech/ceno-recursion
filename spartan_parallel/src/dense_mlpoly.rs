#![allow(clippy::too_many_arguments)]
use crate::scalar::SpartanExtensionField;

use super::errors::ProofVerifyError;
use super::math::Math;
use super::nizk::DotProductProofLog;
use super::random::RandomTape;
use super::transcript::ProofTranscript;
use core::ops::Index;
use merlin::Transcript;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[cfg(feature = "multicore")]
use rayon::prelude::*;

#[derive(Debug, Clone)]
pub struct DensePolynomial<S: SpartanExtensionField> {
  num_vars: usize, // the number of variables in the multilinear polynomial
  len: usize,
  Z: Vec<S>, // evaluations of the polynomial in all the 2^num_vars Boolean inputs
}

pub struct PolyCommitmentBlinds<S: SpartanExtensionField> {
  pub(crate) blinds: Vec<S>,
}

pub struct EqPolynomial<S: SpartanExtensionField> {
  r: Vec<S>,
}

impl<S: SpartanExtensionField> EqPolynomial<S> {
  pub fn new(r: Vec<S>) -> Self {
    EqPolynomial { r }
  }

  pub fn evaluate(&self, rx: &[S]) -> S {
    assert_eq!(self.r.len(), rx.len());
    (0..rx.len())
      .map(|i| self.r[i] * rx[i] + (S::field_one() - self.r[i]) * (S::field_one() - rx[i]))
      .product()
  }

  pub fn evals(&self) -> Vec<S> {
    let ell = self.r.len();

    let mut evals: Vec<S> = vec![S::field_one(); ell.pow2()];
    let mut size = 1;
    for j in 0..ell {
      // in each iteration, we double the size of chis
      size *= 2;
      for i in (0..size).rev().step_by(2) {
        // copy each element from the prior iteration twice
        let scalar = evals[i / 2];
        evals[i] = scalar * self.r[j];
        evals[i - 1] = scalar - evals[i];
      }
    }
    evals
  }

  // Only bound Eq on the first self.r.len() of the total_len variables
  pub fn evals_front(&self, total_len: usize) -> Vec<S> {
    let ell = self.r.len();

    let mut evals: Vec<S> = vec![S::field_one(); total_len.pow2()];
    let base_size = (total_len - ell).pow2();
    let mut size = base_size;
    for j in 0..ell {
      // in each iteration, we double the size of chis
      size *= 2;
      for i in (0..size).rev().step_by(base_size * 2) {
        // copy each element from the prior iteration twice
        let scalar = evals[i / 2];
        let high = scalar * self.r[j];
        let low = scalar - high;
        for k in 0..base_size {
          evals[i - k] = high;
          evals[i - base_size - k] = low;
        }
      }
    }
    evals
  }

  pub fn compute_factored_lens(ell: usize) -> (usize, usize) {
    (ell / 2, ell - ell / 2)
  }

  pub fn compute_factored_evals(&self) -> (Vec<S>, Vec<S>) {
    let ell = self.r.len();
    let (left_num_vars, _right_num_vars) = EqPolynomial::<S>::compute_factored_lens(ell);

    let L = EqPolynomial::new(self.r[..left_num_vars].to_vec()).evals();
    let R = EqPolynomial::new(self.r[left_num_vars..ell].to_vec()).evals();

    (L, R)
  }
}
pub struct IdentityPolynomial<S: SpartanExtensionField> {
  size_point: usize,
  _phantom: S,
}

impl<S: SpartanExtensionField> IdentityPolynomial<S> {
  pub fn new(size_point: usize) -> Self {
    IdentityPolynomial {
      size_point,
      _phantom: S::field_zero(),
    }
  }

  pub fn evaluate(&self, r: &[S]) -> S {
    let len = r.len();
    assert_eq!(len, self.size_point);
    (0..len)
      .map(|i| S::from((len - i - 1).pow2() as u64) * r[i])
      .sum()
  }
}

impl<S: SpartanExtensionField> DensePolynomial<S> {
  pub fn new(mut Z: Vec<S>) -> Self {
    // If length of Z is not a power of 2, append Z with 0
    let zero = S::field_zero();
    Z.extend(vec![zero; Z.len().next_power_of_two() - Z.len()]);
    DensePolynomial {
      num_vars: Z.len().log_2(),
      len: Z.len(),
      Z,
    }
  }

  pub fn get_num_vars(&self) -> usize {
    self.num_vars
  }

  pub fn len(&self) -> usize {
    self.len
  }

  pub fn clone(&self) -> DensePolynomial<S> {
    DensePolynomial::new(self.Z[0..self.len].to_vec())
  }

  pub fn split(&self, idx: usize) -> (DensePolynomial<S>, DensePolynomial<S>) {
    assert!(idx < self.len());
    (
      DensePolynomial::new(self.Z[..idx].to_vec()),
      DensePolynomial::new(self.Z[idx..2 * idx].to_vec()),
    )
  }

  pub fn bound(&self, L: &[S]) -> Vec<S> {
    let (left_num_vars, right_num_vars) =
      EqPolynomial::<S>::compute_factored_lens(self.get_num_vars());
    let L_size = left_num_vars.pow2();
    let R_size = right_num_vars.pow2();
    (0..R_size)
      .map(|i| (0..L_size).map(|j| L[j] * self.Z[j * R_size + i]).sum())
      .collect()
  }

  pub fn bound_poly_var_top(&mut self, r: &S) {
    let n = self.len() / 2;
    for i in 0..n {
      self.Z[i] = self.Z[i] + *r * (self.Z[i + n] - self.Z[i]);
    }
    self.num_vars -= 1;
    self.len = n;
  }

  // Bound_var_top but the polynomial is in (x, q, p) form and certain (p, q) pair is invalid
  pub fn bound_poly_var_top_disjoint_rounds(
    &mut self,
    r: &S,
    proof_space: usize,
    instance_space: usize,
    cons_len: usize,
    proof_len: usize,
    instance_len: usize,
    num_proofs: &Vec<usize>,
  ) {
    let n = self.len() / 2;
    assert_eq!(n, cons_len * proof_len * instance_len);

    for p in 0..instance_len {
      // Certain p, q combinations within the boolean hypercube always evaluate to 0
      let max_q = if proof_len != proof_space {
        proof_len
      } else {
        num_proofs[p]
      };
      for q in 0..max_q {
        for x in 0..cons_len {
          let i = x * proof_space * instance_space + q * instance_space + p;
          self.Z[i] = self.Z[i] + *r * (self.Z[i + n] - self.Z[i]);
        }
      }
    }
    self.num_vars -= 1;
    self.len = n;
  }

  // The polynomial is in (q, p, x) form and certain (p, q) pair is invalid
  // Binding the entire "q" section and q is in reverse order
  // Use "num_proofs" to record how many "q"s need to process for each "p"
  pub fn bound_poly_var_front_rq(
    &mut self,
    r_q: &Vec<S>,
    mut max_proof_space: usize,
    instance_space: usize,
    cons_space: usize,
    mut num_proofs: Vec<usize>,
  ) {
    let mut n = self.len();
    assert_eq!(n, max_proof_space * instance_space * cons_space);

    for r in r_q {
      n /= 2;
      max_proof_space /= 2;

      for p in 0..instance_space {
        if num_proofs[p] == 1 {
          // q = 0
          for x in 0..cons_space {
            let i = p * cons_space + x;
            self.Z[i] = (S::field_one() - *r) * self.Z[i];
          }
        } else {
          num_proofs[p] /= 2;
          let step = max_proof_space / num_proofs[p];
          for q in (0..max_proof_space).step_by(step) {
            for x in 0..cons_space {
              let i = q * instance_space * cons_space + p * cons_space + x;
              self.Z[i] = self.Z[i] + *r * (self.Z[i + n] - self.Z[i]);
            }
          }
        }
      }
      self.num_vars -= 1;
      self.len = n;
    }
  }

  pub fn bound_poly_var_bot(&mut self, r: &S) {
    let n = self.len() / 2;
    for i in 0..n {
      self.Z[i] = self.Z[2 * i] + *r * (self.Z[2 * i + 1] - self.Z[2 * i]);
    }
    self.num_vars -= 1;
    self.len = n;
  }

  // returns Z(r) in O(n) time
  pub fn evaluate(&self, r: &[S]) -> S {
    // r must have a value for each variable
    assert_eq!(r.len(), self.get_num_vars());
    let chis = EqPolynomial::new(r.to_vec()).evals();
    assert_eq!(chis.len(), self.Z.len());
    DotProductProofLog::compute_dotproduct(&self.Z, &chis)
  }

  fn vec(&self) -> &Vec<S> {
    &self.Z
  }

  pub fn extend(&mut self, other: &DensePolynomial<S>) {
    // TODO: allow extension even when some vars are bound
    assert_eq!(self.Z.len(), self.len);
    let other_vec = other.vec();
    assert_eq!(other_vec.len(), self.len);
    self.Z.extend(other_vec);
    self.num_vars += 1;
    self.len *= 2;
    assert_eq!(self.Z.len(), self.len);
  }

  pub fn merge<'a, I>(polys: I) -> DensePolynomial<S>
  where
    I: IntoIterator<Item = DensePolynomial<S>>,
  {
    let mut Z: Vec<S> = Vec::new();
    for poly in polys.into_iter() {
      Z.extend(poly.vec());
    }

    // pad the polynomial with zero polynomial at the end
    Z.resize(Z.len().next_power_of_two(), S::field_zero());

    DensePolynomial::new(Z)
  }

  pub fn from_usize(Z: &[usize]) -> Self {
    DensePolynomial::new(
      (0..Z.len())
        .map(|i| S::from(Z[i] as u64))
        .collect::<Vec<S>>(),
    )
  }
}

impl<S: SpartanExtensionField> Index<usize> for DensePolynomial<S> {
  type Output = S;

  #[inline(always)]
  fn index(&self, _index: usize) -> &S {
    &(self.Z[_index])
  }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PolyEvalProof<S: SpartanExtensionField> {
  proof: DotProductProofLog<S>,
}

impl<S: SpartanExtensionField> PolyEvalProof<S> {
  fn protocol_name() -> &'static [u8] {
    b"polynomial evaluation proof"
  }

  pub fn prove(
    poly: &DensePolynomial<S>,
    blinds_opt: Option<&PolyCommitmentBlinds<S>>,
    r: &[S],                  // point at which the polynomial is evaluated
    Zr: &S,                   // evaluation of \widetilde{Z}(r)
    blind_Zr_opt: Option<&S>, // specifies a blind for Zr
    transcript: &mut Transcript,
    random_tape: &mut RandomTape<S>,
  ) -> PolyEvalProof<S> {
    <Transcript as ProofTranscript<S>>::append_protocol_name(
      transcript,
      PolyEvalProof::<S>::protocol_name(),
    );

    // assert vectors are of the right size
    assert_eq!(poly.get_num_vars(), r.len());

    let (left_num_vars, right_num_vars) = EqPolynomial::<S>::compute_factored_lens(r.len());
    let L_size = left_num_vars.pow2();
    let R_size = right_num_vars.pow2();

    let default_blinds = PolyCommitmentBlinds {
      blinds: vec![S::field_zero(); L_size],
    };
    let blinds = blinds_opt.map_or(&default_blinds, |p| p);

    assert_eq!(blinds.blinds.len(), L_size);

    let zero = S::field_zero();
    let blind_Zr = blind_Zr_opt.map_or(&zero, |p| p);

    // compute the L and R vectors
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();
    assert_eq!(L.len(), L_size);
    assert_eq!(R.len(), R_size);

    // compute the vector underneath L*Z and the L*blinds
    // compute vector-matrix product between L and Z viewed as a matrix
    let LZ = poly.bound(&L);
    let LZ_blind: S = (0..L.len()).map(|i| blinds.blinds[i] * L[i]).sum();

    // a dot product proof of size R_size
    let proof =
      DotProductProofLog::prove(transcript, random_tape, &LZ, &LZ_blind, &R, Zr, blind_Zr);

    PolyEvalProof { proof }
  }

  pub fn verify(
    &self,
    _transcript: &mut Transcript,
    _r: &[S], // point at which the polynomial is evaluated
  ) -> Result<(), ProofVerifyError> {
    // TODO: Alternative PCS Verification
    Ok(())
  }

  pub fn verify_plain(
    &self,
    _transcript: &mut Transcript,
    _r: &[S], // point at which the polynomial is evaluated
    _Zr: &S,  // evaluation \widetilde{Z}(r)
  ) -> Result<(), ProofVerifyError> {
    // TODO: Alternative PCS Verification
    Ok(())
  }

  // Evaluation of multiple points on the same instance
  pub fn prove_batched_points(
    poly: &DensePolynomial<S>,
    blinds_opt: Option<&PolyCommitmentBlinds<S>>,
    r_list: Vec<Vec<S>>,      // point at which the polynomial is evaluated
    Zr_list: Vec<S>,          // evaluation of \widetilde{Z}(r) on each point
    blind_Zr_opt: Option<&S>, // specifies a blind for Zr
    transcript: &mut Transcript,
    random_tape: &mut RandomTape<S>,
  ) -> Vec<PolyEvalProof<S>> {
    <Transcript as ProofTranscript<S>>::append_protocol_name(
      transcript,
      PolyEvalProof::<S>::protocol_name(),
    );

    // assert vectors are of the right size
    assert_eq!(r_list.len(), Zr_list.len());
    for r in &r_list {
      assert_eq!(poly.get_num_vars(), r.len());
    }

    let (left_num_vars, right_num_vars) = EqPolynomial::<S>::compute_factored_lens(r_list[0].len());
    let L_size = left_num_vars.pow2();
    let R_size = right_num_vars.pow2();

    let default_blinds = PolyCommitmentBlinds {
      blinds: vec![S::field_zero(); L_size],
    };
    let blinds = blinds_opt.map_or(&default_blinds, |p| p);

    assert_eq!(blinds.blinds.len(), L_size);

    let zero = S::field_zero();
    let blind_Zr = blind_Zr_opt.map_or(&zero, |p| p);

    // compute the L and R vectors
    // We can perform batched opening if L is the same, so we regroup the proofs by L vector
    // Map from the left half of the r to index in L_list
    let mut index_map: HashMap<Vec<S>, usize> = HashMap::new();
    let mut L_list: Vec<Vec<S>> = Vec::new();
    let mut R_list: Vec<Vec<S>> = Vec::new();
    let mut Zc_list: Vec<S> = Vec::new();

    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = S::field_one();
    for i in 0..r_list.len() {
      let eq = EqPolynomial::new(r_list[i].to_vec());
      let (Li, Ri) = eq.compute_factored_evals();
      assert_eq!(Li.len(), L_size);
      assert_eq!(Ri.len(), R_size);
      if let Some(index) = index_map.get(&r_list[i][..left_num_vars]) {
        // L already exist
        // generate coefficient for RLC
        c = c * c_base;
        R_list[*index] = (0..R_size).map(|j| R_list[*index][j] + c * Ri[j]).collect();
        Zc_list[*index] = Zc_list[*index] + c * Zr_list[i];
      } else {
        let next_index = L_list.len();
        index_map.insert(r_list[i][..left_num_vars].to_vec(), next_index);
        L_list.push(Li);
        R_list.push(Ri);
        Zc_list.push(Zr_list[i]);
      }
    }

    let mut proof_list = Vec::new();
    for i in 0..L_list.len() {
      let L = &L_list[i];
      let R = &R_list[i];
      // compute the vector underneath L*Z and the L*blinds
      // compute vector-matrix product between L and Z viewed as a matrix
      let LZ = poly.bound(L);
      let LZ_blind: S = (0..L.len()).map(|i| blinds.blinds[i] * L[i]).sum();

      // a dot product proof of size R_size
      let proof = DotProductProofLog::prove(
        transcript,
        random_tape,
        &LZ,
        &LZ_blind,
        R,
        &Zc_list[i],
        blind_Zr,
      );
      proof_list.push(proof);
    }

    proof_list
      .iter()
      .map(|proof| PolyEvalProof {
        proof: proof.clone(),
      })
      .collect()
  }

  pub fn verify_plain_batched_points(
    proof_list: &Vec<PolyEvalProof<S>>,
    transcript: &mut Transcript,
    r_list: Vec<Vec<S>>, // point at which the polynomial is evaluated
    Zr_list: Vec<S>,     // commitment to \widetilde{Z}(r) on each point
  ) -> Result<(), ProofVerifyError> {
    <Transcript as ProofTranscript<S>>::append_protocol_name(
      transcript,
      PolyEvalProof::<S>::protocol_name(),
    );

    let (left_num_vars, _) = EqPolynomial::<S>::compute_factored_lens(r_list[0].len());

    // compute the L and R
    // We can perform batched opening if L is the same, so we regroup the proofs by L vector
    // Map from the left half of the r to index in L_list
    let mut index_map: HashMap<Vec<S>, usize> = HashMap::new();
    let mut L_list: Vec<Vec<S>> = Vec::new();
    let mut R_list: Vec<Vec<S>> = Vec::new();
    let mut Zc_list: Vec<S> = Vec::new();

    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = S::field_one();
    for i in 0..r_list.len() {
      let eq = EqPolynomial::new(r_list[i].to_vec());
      let (Li, Ri) = eq.compute_factored_evals();
      if let Some(index) = index_map.get(&r_list[i][..left_num_vars]) {
        // L already exist
        // generate coefficient for RLC
        c = c * c_base;
        R_list[*index] = (0..Ri.len())
          .map(|j| R_list[*index][j] + c * Ri[j])
          .collect();
        Zc_list[*index] = Zc_list[*index] + c * Zr_list[i];
      } else {
        let next_index = L_list.len();
        index_map.insert(r_list[i][..left_num_vars].to_vec(), next_index);
        L_list.push(Li);
        R_list.push(Ri);
        Zc_list.push(Zr_list[i]);
      }
    }
    assert_eq!(L_list.len(), proof_list.len());

    Ok(())
  }

  // Evaluation on multiple instances, each at different point
  // Size of each instance might be different, but all are larger than the evaluation point
  pub fn prove_batched_instances(
    poly_list: &Vec<DensePolynomial<S>>, // list of instances
    blinds_opt: Option<&PolyCommitmentBlinds<S>>,
    r_list: Vec<&Vec<S>>,     // point at which the polynomial is evaluated
    Zr_list: &Vec<S>,         // evaluation of \widetilde{Z}(r) on each instance
    blind_Zr_opt: Option<&S>, // specifies a blind for Zr
    transcript: &mut Transcript,
    random_tape: &mut RandomTape<S>,
  ) -> Vec<PolyEvalProof<S>> {
    <Transcript as ProofTranscript<S>>::append_protocol_name(
      transcript,
      PolyEvalProof::<S>::protocol_name(),
    );

    // assert vectors are of the right size
    assert_eq!(poly_list.len(), r_list.len());
    assert_eq!(poly_list.len(), Zr_list.len());

    // We need one proof per poly size & R
    let mut index_map: HashMap<(usize, Vec<S>), usize> = HashMap::new();
    let mut LZ_list: Vec<Vec<S>> = Vec::new();
    let mut Zc_list = Vec::new();
    let mut L_list: Vec<Vec<S>> = Vec::new();
    let mut R_list: Vec<Vec<S>> = Vec::new();

    // generate coefficient for RLC
    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = S::field_one();
    let zero = S::field_zero();
    for i in 0..poly_list.len() {
      let poly = &poly_list[i];
      let num_vars = poly.get_num_vars();

      // compute L and R
      let (L, R) = {
        let r = r_list[i];
        // pad or trim r to correct length
        let r = {
          if num_vars >= r.len() {
            [vec![zero; num_vars - r.len()], r.to_vec()].concat()
          } else {
            r[r.len() - num_vars..].to_vec()
          }
        };
        let eq = EqPolynomial::new(r);
        eq.compute_factored_evals()
      };

      if let Some(index) = index_map.get(&(num_vars, R.clone())) {
        c = c * c_base;
        let LZ = poly.bound(&L);
        LZ_list[*index] = (0..LZ.len())
          .map(|j| LZ_list[*index][j] + c * LZ[j])
          .collect();
        Zc_list[*index] = Zc_list[*index] + c * Zr_list[i];
      } else {
        index_map.insert((num_vars, R.clone()), LZ_list.len());
        Zc_list.push(Zr_list[i]);
        // compute a weighted sum of commitments and L
        let LZ = poly.bound(&L);
        L_list.push(L);
        R_list.push(R);
        LZ_list.push(LZ);
      }
    }

    let mut proof_list = Vec::new();
    for i in 0..LZ_list.len() {
      let L = &L_list[i];
      let L_size = L.len();

      let default_blinds = PolyCommitmentBlinds {
        blinds: vec![S::field_zero(); L_size],
      };
      let blinds = blinds_opt.map_or(&default_blinds, |p| p);
      assert_eq!(blinds.blinds.len(), L_size);
      let blind_Zr = blind_Zr_opt.map_or(&zero, |p| p);
      let LZ_blind: S = (0..L.len()).map(|i| blinds.blinds[i] * L[i]).sum();

      // a dot product proof of size R_size
      let proof = DotProductProofLog::prove(
        transcript,
        random_tape,
        &LZ_list[i],
        &LZ_blind,
        &R_list[i],
        &Zc_list[i],
        blind_Zr,
      );
      proof_list.push(PolyEvalProof { proof });
    }

    proof_list
  }

  pub fn verify_plain_batched_instances(
    proof_list: &Vec<PolyEvalProof<S>>,
    transcript: &mut Transcript,
    r_list: Vec<&Vec<S>>,       // point at which the polynomial is evaluated
    Zr_list: &Vec<S>,           // commitment to \widetilde{Z}(r) of each instance
    num_vars_list: &Vec<usize>, // size of each polynomial
  ) -> Result<(), ProofVerifyError> {
    <Transcript as ProofTranscript<S>>::append_protocol_name(
      transcript,
      PolyEvalProof::<S>::protocol_name(),
    );

    // We need one proof per poly size + L size
    let mut index_map: HashMap<(usize, Vec<S>), usize> = HashMap::new();
    let mut Zc_list = Vec::new();
    let mut L_list: Vec<Vec<S>> = Vec::new();
    let mut R_list: Vec<Vec<S>> = Vec::new();

    // generate coefficient for RLC
    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = S::field_one();
    let zero = S::field_zero();

    for i in 0..r_list.len() {
      let num_vars = num_vars_list[i];

      // compute L and R
      let (L, R) = {
        let r = r_list[i];
        // pad or trim r to correct length
        let r = {
          if num_vars >= r.len() {
            [vec![zero; num_vars - r.len()], r.to_vec()].concat()
          } else {
            r[r.len() - num_vars..].to_vec()
          }
        };
        let eq = EqPolynomial::new(r);
        eq.compute_factored_evals()
      };

      if let Some(index) = index_map.get(&(num_vars, R.clone())) {
        c = c * c_base;
        Zc_list[*index] = Zc_list[*index] + c * Zr_list[i];
      } else {
        Zc_list.push(Zr_list[i]);
        // compute a weighted sum of commitments and L
        L_list.push(L);
        R_list.push(R);
      }
    }

    Ok(())
  }

  // Like prove_batched_instances, but r is divided into rq ++ ry
  // Each polynomial is supplemented with num_proofs and num_inputs
  pub fn prove_batched_instances_disjoint_rounds(
    poly_list: &Vec<&DensePolynomial<S>>,
    num_proofs_list: &Vec<usize>,
    num_inputs_list: &Vec<usize>,
    blinds_opt: Option<&PolyCommitmentBlinds<S>>,
    rq: &[S],
    ry: &[S],
    Zr_list: &Vec<S>,
    blind_Zr_opt: Option<&S>,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape<S>,
  ) -> Vec<PolyEvalProof<S>> {
    <Transcript as ProofTranscript<S>>::append_protocol_name(
      transcript,
      PolyEvalProof::<S>::protocol_name(),
    );

    // assert vectors are of the right size
    assert_eq!(poly_list.len(), Zr_list.len());

    // We need one proof per (num_proofs, num_inputs) pair
    let mut index_map: HashMap<(usize, usize), usize> = HashMap::new();
    let mut LZ_list: Vec<Vec<S>> = Vec::new();
    let mut Zc_list = Vec::new();
    let mut L_list: Vec<Vec<S>> = Vec::new();
    let mut R_list = Vec::new();

    // generate coefficient for RLC
    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = S::field_one();
    let zero = S::field_zero();
    for i in 0..poly_list.len() {
      let poly = poly_list[i];
      let num_proofs = num_proofs_list[i];
      let num_inputs = num_inputs_list[i];
      if let Some(index) = index_map.get(&(num_proofs, num_inputs)) {
        c = c * c_base;
        let L = &L_list[*index].to_vec();
        let LZ = poly.bound(&L);
        LZ_list[*index] = (0..LZ.len())
          .map(|j| LZ_list[*index][j] + c * LZ[j])
          .collect();
        Zc_list[*index] = Zc_list[*index] + c * Zr_list[i];
      } else {
        index_map.insert((num_proofs, num_inputs), LZ_list.len());
        Zc_list.push(Zr_list[i]);
        let num_vars_q = num_proofs.log_2();
        let num_vars_y = num_inputs.log_2();
        // pad or trim rq and ry to correct length
        let (L, R) = {
          let ry_short = {
            if num_vars_y >= ry.len() {
              let ry_pad = &vec![zero; num_vars_y - ry.len()];
              [ry_pad, ry].concat()
            }
            // Else ry_short is the last w.num_inputs[p].log_2() entries of ry
            // thus, to obtain the actual ry, need to multiply by (1 - ry2)(1 - ry3)..., which is ry_factors[num_rounds_y - w.num_inputs[p]]
            else {
              ry[ry.len() - num_vars_y..].to_vec()
            }
          };
          let rq_short = rq[rq.len() - num_vars_q..].to_vec();
          let r = [rq_short, ry_short.clone()].concat();
          let eq = EqPolynomial::new(r);
          eq.compute_factored_evals()
        };
        // compute a weighted sum of commitments and L
        let LZ = poly.bound(&L);
        L_list.push(L);
        R_list.push(R);
        LZ_list.push(LZ);
      }
    }

    let mut proof_list = Vec::new();
    for i in 0..LZ_list.len() {
      let L = &L_list[i];
      let L_size = L.len();
      let default_blinds = PolyCommitmentBlinds {
        blinds: vec![S::field_zero(); L_size],
      };
      let blinds = blinds_opt.map_or(&default_blinds, |p| p);

      assert_eq!(blinds.blinds.len(), L_size);

      let blind_Zr = blind_Zr_opt.map_or(&zero, |p| p);
      let LZ_blind: S = (0..L.len()).map(|i| blinds.blinds[i] * L[i]).sum();

      // a dot product proof of size R_size
      let proof = DotProductProofLog::prove(
        transcript,
        random_tape,
        &LZ_list[i],
        &LZ_blind,
        &R_list[i],
        &Zc_list[i],
        blind_Zr,
      );
      proof_list.push(PolyEvalProof { proof });
    }
    proof_list
  }

  pub fn verify_batched_instances_disjoint_rounds(
    proof_list: &Vec<PolyEvalProof<S>>,
    num_proofs_list: &Vec<usize>,
    num_inputs_list: &Vec<usize>,
    transcript: &mut Transcript,
    rq: &[S],
    ry: &[S],
  ) -> Result<(), ProofVerifyError> {
    <Transcript as ProofTranscript<S>>::append_protocol_name(
      transcript,
      PolyEvalProof::<S>::protocol_name(),
    );

    // We need one proof per poly size
    let mut index_map: HashMap<(usize, usize), usize> = HashMap::new();
    let mut L_list = Vec::new();
    let mut R_list = Vec::new();

    // generate coefficient for RLC
    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = S::field_one();
    let zero = S::field_zero();

    for i in 0..num_proofs_list.len() {
      let num_proofs = num_proofs_list[i];
      let num_inputs = num_inputs_list[i];
      if let Some(index) = index_map.get(&(num_proofs, num_inputs)) {
        c = c * c_base;
        let _L = &L_list[*index];
      } else {
        let num_vars_q = num_proofs.log_2();
        let num_vars_y = num_inputs.log_2();
        // pad or trim rq and ry to correct length
        let (L, R) = {
          let ry_short = {
            if num_vars_y >= ry.len() {
              let ry_pad = &vec![zero; num_vars_y - ry.len()];
              [ry_pad, ry].concat()
            }
            // Else ry_short is the last w.num_inputs[p].log_2() entries of ry
            // thus, to obtain the actual ry, need to multiply by (1 - ry2)(1 - ry3)..., which is ry_factors[num_rounds_y - w.num_inputs[p]]
            else {
              ry[ry.len() - num_vars_y..].to_vec()
            }
          };
          let rq_short = rq[rq.len() - num_vars_q..].to_vec();
          let r = [rq_short, ry_short.clone()].concat();
          let eq = EqPolynomial::new(r);
          eq.compute_factored_evals()
        };
        // compute a weighted sum of commitments and L
        L_list.push(L);
        R_list.push(R);
      }
    }

    Ok(())
  }

  // Treat the polynomial(s) as univariate and open on a single point
  pub fn prove_uni_batched_instances(
    poly_list: &Vec<&DensePolynomial<S>>,
    r: &S,       // point at which the polynomial is evaluated
    Zr: &Vec<S>, // evaluation of \widetilde{Z}(r)
    transcript: &mut Transcript,
    random_tape: &mut RandomTape<S>,
  ) -> PolyEvalProof<S> {
    <Transcript as ProofTranscript<S>>::append_protocol_name(
      transcript,
      PolyEvalProof::<S>::protocol_name(),
    );

    let max_num_vars = poly_list.iter().fold(0, |m, p| {
      if p.get_num_vars() > m {
        p.get_num_vars()
      } else {
        m
      }
    });
    let zero = S::field_zero();

    // L differs depending on size of the polynomial, but R always stay the same
    let (_, right_num_vars) = EqPolynomial::<S>::compute_factored_lens(max_num_vars);
    let R_size = right_num_vars.pow2();

    // compute R = <1, r, r^2, ...>
    let R = {
      let mut r_base = S::field_one();
      let mut R = Vec::new();
      for _ in 0..R_size {
        R.push(r_base);
        r_base = r_base * *r;
      }
      R
    };
    let mut L_map: HashMap<usize, Vec<S>> = HashMap::new();

    // compute the vector underneath L*Z
    // compute vector-matrix product between L and Z viewed as a matrix
    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = S::field_one();
    let mut LZ_comb = vec![zero; R_size];
    let mut Zr_comb = zero;

    for i in 0..poly_list.len() {
      let poly = &poly_list[i];
      let num_vars = poly.get_num_vars();
      let L = if let Some(L) = L_map.get(&num_vars) {
        L
      } else {
        let (left_num_vars, right_num_vars) = EqPolynomial::<S>::compute_factored_lens(num_vars);
        let L_size = left_num_vars.pow2();
        let R_size = right_num_vars.pow2();
        let r_base = (0..R_size).fold(S::field_one(), |p, _| p * *r);
        // L is 1, r^k, r^2k, ...
        let mut l_base = S::field_one();
        let mut L = Vec::new();
        for _ in 0..L_size {
          L.push(l_base);
          l_base = l_base * r_base;
        }
        L_map.insert(num_vars, L.clone());
        L_map.get(&num_vars).unwrap()
      };

      let LZ = poly.bound(&L);
      LZ_comb = (0..R_size)
        .map(|i| LZ_comb[i] + if i < LZ.len() { c * LZ[i] } else { zero })
        .collect();
      Zr_comb = Zr_comb + c * Zr[i];
      c = c * c_base;
    }

    // a dot product proof of size R_size
    let proof = DotProductProofLog::prove(
      transcript,
      random_tape,
      &LZ_comb,
      &zero,
      &R,
      &Zr_comb,
      &zero,
    );

    PolyEvalProof { proof }
  }

  pub fn verify_uni_batched_instances(
    &self,
    transcript: &mut Transcript,
    r: &S, // point at which the polynomial is evaluated
    poly_size: Vec<usize>,
  ) -> Result<(), ProofVerifyError> {
    <Transcript as ProofTranscript<S>>::append_protocol_name(
      transcript,
      PolyEvalProof::<S>::protocol_name(),
    );

    let max_poly_size = poly_size.iter().fold(0, |m, i| if *i > m { *i } else { m });
    // compute L and R
    let (_, right_num_vars) =
      EqPolynomial::<S>::compute_factored_lens(max_poly_size.next_power_of_two().log_2());
    let R_size = right_num_vars.pow2();

    // compute R = <1, r, r^2, ...>
    let R = {
      let mut r_base = S::field_one();
      let mut R = Vec::new();
      for _ in 0..R_size {
        R.push(r_base);
        r_base = r_base * *r;
      }
      R
    };
    let mut L_map: HashMap<usize, Vec<S>> = HashMap::new();

    // compute a weighted sum of commitments and L
    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = S::field_one();

    for i in 0..poly_size.len() {
      let num_vars = poly_size[i].next_power_of_two().log_2();
      let L = if let Some(L) = L_map.get(&num_vars) {
        L
      } else {
        let (left_num_vars, right_num_vars) = EqPolynomial::<S>::compute_factored_lens(num_vars);
        let L_size = left_num_vars.pow2();
        let R_size = right_num_vars.pow2();
        let r_base = (0..R_size).fold(S::field_one(), |p, _| p * *r);
        // L is 1, r^k, r^2k, ...
        let mut l_base = S::field_one();
        let mut L = Vec::new();
        for _ in 0..L_size {
          L.push(l_base);
          l_base = l_base * r_base;
        }
        L_map.insert(num_vars, L.clone());
        L_map.get(&num_vars).unwrap()
      };

      c = c * c_base;
    }

    self.proof.verify(R.len(), transcript, &R)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use rand::rngs::OsRng;
  use crate::scalar::Scalar;

  fn evaluate_with_LR(Z: &[Scalar], r: &[Scalar]) -> Scalar {
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();

    let ell = r.len();
    // ensure ell is even
    assert!(ell % 2 == 0);
    // compute n = 2^\ell
    let n = ell.pow2();
    // compute m = sqrt(n) = 2^{\ell/2}
    let m = n.square_root();

    // compute vector-matrix product between L and Z viewed as a matrix
    let LZ = (0..m)
      .map(|i| (0..m).map(|j| L[j] * Z[j * m + i]).sum())
      .collect::<Vec<Scalar>>();

    // compute dot product between LZ and R
    DotProductProofLog::compute_dotproduct(&LZ, &R)
  }

  #[test]
  fn check_polynomial_evaluation() {
    // Z = [1, 2, 1, 4]
    let Z = vec![
      Scalar::one(),
      Scalar::from(2_usize),
      Scalar::from(1_usize),
      Scalar::from(4_usize),
    ];

    // r = [4,3]
    let r = vec![Scalar::from(4_usize), Scalar::from(3_usize)];

    let eval_with_LR = evaluate_with_LR(&Z, &r);
    let poly = DensePolynomial::new(Z);

    let eval = poly.evaluate(&r);
    assert_eq!(eval, Scalar::from(28_usize));
    assert_eq!(eval_with_LR, eval);
  }

  pub fn compute_factored_chis_at_r(r: &[Scalar]) -> (Vec<Scalar>, Vec<Scalar>) {
    let mut L: Vec<Scalar> = Vec::new();
    let mut R: Vec<Scalar> = Vec::new();

    let ell = r.len();
    assert!(ell % 2 == 0); // ensure ell is even
    let n = ell.pow2();
    let m = n.square_root();

    // compute row vector L
    for i in 0..m {
      let mut chi_i = Scalar::one();
      for j in 0..ell / 2 {
        let bit_j = ((m * i) & (1 << (r.len() - j - 1))) > 0;
        if bit_j {
          chi_i *= r[j];
        } else {
          chi_i *= Scalar::one() - r[j];
        }
      }
      L.push(chi_i);
    }

    // compute column vector R
    for i in 0..m {
      let mut chi_i = Scalar::one();
      for j in ell / 2..ell {
        let bit_j = (i & (1 << (r.len() - j - 1))) > 0;
        if bit_j {
          chi_i *= r[j];
        } else {
          chi_i *= Scalar::one() - r[j];
        }
      }
      R.push(chi_i);
    }
    (L, R)
  }

  pub fn compute_chis_at_r(r: &[Scalar]) -> Vec<Scalar> {
    let ell = r.len();
    let n = ell.pow2();
    let mut chis: Vec<Scalar> = Vec::new();
    for i in 0..n {
      let mut chi_i = Scalar::one();
      for j in 0..r.len() {
        let bit_j = (i & (1 << (r.len() - j - 1))) > 0;
        if bit_j {
          chi_i *= r[j];
        } else {
          chi_i *= Scalar::one() - r[j];
        }
      }
      chis.push(chi_i);
    }
    chis
  }

  pub fn compute_outerproduct(L: Vec<Scalar>, R: Vec<Scalar>) -> Vec<Scalar> {
    assert_eq!(L.len(), R.len());
    (0..L.len())
      .map(|i| (0..R.len()).map(|j| L[i] * R[j]).collect::<Vec<Scalar>>())
      .collect::<Vec<Vec<Scalar>>>()
      .into_iter()
      .flatten()
      .collect::<Vec<Scalar>>()
  }

  #[test]
  fn check_memoized_chis() {
    let mut csprng: OsRng = OsRng;

    let s = 10;
    let mut r: Vec<Scalar> = Vec::new();
    for _i in 0..s {
      r.push(Scalar::random(&mut csprng));
    }
    let chis = tests::compute_chis_at_r(&r);
    let chis_m = EqPolynomial::new(r).evals();
    assert_eq!(chis, chis_m);
  }

  #[test]
  fn check_factored_chis() {
    let mut csprng: OsRng = OsRng;

    let s = 10;
    let mut r: Vec<Scalar> = Vec::new();
    for _i in 0..s {
      r.push(Scalar::random(&mut csprng));
    }
    let chis = EqPolynomial::new(r.clone()).evals();
    let (L, R) = EqPolynomial::new(r).compute_factored_evals();
    let O = compute_outerproduct(L, R);
    assert_eq!(chis, O);
  }

  #[test]
  fn check_memoized_factored_chis() {
    let mut csprng: OsRng = OsRng;

    let s = 10;
    let mut r: Vec<Scalar> = Vec::new();
    for _i in 0..s {
      r.push(Scalar::random(&mut csprng));
    }
    let (L, R) = tests::compute_factored_chis_at_r(&r);
    let eq = EqPolynomial::new(r);
    let (L2, R2) = eq.compute_factored_evals();
    assert_eq!(L, L2);
    assert_eq!(R, R2);
  }
}
