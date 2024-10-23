#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
use crate::custom_dense_mlpoly::DensePolynomialPqx;
use crate::math::Math;

use super::commitments::{Commitments, MultiCommitGens};
use super::dense_mlpoly::DensePolynomial;
use super::errors::ProofVerifyError;
use super::group::{CompressedGroup, GroupElement, VartimeMultiscalarMul};
use super::nizk::DotProductProof;
use super::random::RandomTape;
use super::scalar::Scalar;
use super::transcript::{AppendToTranscript, ProofTranscript};
use super::unipoly::{CompressedUniPoly, UniPoly};
use core::iter;
use itertools::izip;
use merlin::Transcript;
use serde::{Deserialize, Serialize};
use std::cmp::min;

const ZERO: Scalar = Scalar::zero();
const MODE_P: usize = 1;
const MODE_Q: usize = 2;
const MODE_W: usize = 3;
const MODE_X: usize = 4;

#[derive(Serialize, Deserialize, Debug)]
pub struct SumcheckInstanceProof {
  compressed_polys: Vec<CompressedUniPoly>,
}

impl SumcheckInstanceProof {
  pub fn new(compressed_polys: Vec<CompressedUniPoly>) -> SumcheckInstanceProof {
    SumcheckInstanceProof { compressed_polys }
  }

  pub fn verify(
    &self,
    claim: Scalar,
    num_rounds: usize,
    degree_bound: usize,
    transcript: &mut Transcript,
  ) -> Result<(Scalar, Vec<Scalar>), ProofVerifyError> {
    let mut e = claim;
    let mut r: Vec<Scalar> = Vec::new();

    // verify that there is a univariate polynomial for each round
    assert_eq!(self.compressed_polys.len(), num_rounds);
    for i in 0..self.compressed_polys.len() {
      let poly = self.compressed_polys[i].decompress(&e);

      // verify degree bound
      assert_eq!(poly.degree(), degree_bound);

      // check if G_k(0) + G_k(1) = e
      assert_eq!(poly.eval_at_zero() + poly.eval_at_one(), e);

      // append the prover's message to the transcript
      poly.append_to_transcript(b"poly", transcript);

      // derive the verifier's challenge for the next round
      let r_i = transcript.challenge_scalar(b"challenge_nextround");

      r.push(r_i);

      // evaluate the claimed degree-ell polynomial at r_i
      e = poly.evaluate(&r_i);
    }

    Ok((e, r))
  }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct ZKSumcheckInstanceProof {
  comm_polys: Vec<CompressedGroup>,
  comm_evals: Vec<CompressedGroup>,
  proofs: Vec<DotProductProof>,
}

impl ZKSumcheckInstanceProof {
  pub fn new(
    comm_polys: Vec<CompressedGroup>,
    comm_evals: Vec<CompressedGroup>,
    proofs: Vec<DotProductProof>,
  ) -> Self {
    ZKSumcheckInstanceProof {
      comm_polys,
      comm_evals,
      proofs,
    }
  }

  pub fn verify(
    &self,
    comm_claim: &CompressedGroup,
    num_rounds: usize,
    degree_bound: usize,
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
  ) -> Result<(CompressedGroup, Vec<Scalar>), ProofVerifyError> {
    // verify degree bound
    assert_eq!(gens_n.n, degree_bound + 1);

    // verify that there is a univariate polynomial for each round
    assert_eq!(self.comm_polys.len(), num_rounds);
    assert_eq!(self.comm_evals.len(), num_rounds);

    let mut r: Vec<Scalar> = Vec::new();
    for i in 0..self.comm_polys.len() {
      let comm_poly = &self.comm_polys[i];

      // append the prover's polynomial to the transcript
      comm_poly.append_to_transcript(b"comm_poly", transcript);

      // derive the verifier's challenge for the next round
      let r_i = transcript.challenge_scalar(b"challenge_nextround");

      // verify the proof of sum-check and evals
      let res = {
        let comm_claim_per_round = if i == 0 {
          comm_claim
        } else {
          &self.comm_evals[i - 1]
        };
        let comm_eval = &self.comm_evals[i];

        // add two claims to transcript
        comm_claim_per_round.append_to_transcript(b"comm_claim_per_round", transcript);
        comm_eval.append_to_transcript(b"comm_eval", transcript);

        // produce two weights
        let w = transcript.challenge_vector(b"combine_two_claims_to_one", 2);

        // compute a weighted sum of the RHS
        let comm_target = GroupElement::vartime_multiscalar_mul(
          w.iter(),
          iter::once(&comm_claim_per_round)
            .chain(iter::once(&comm_eval))
            .map(|pt| pt.decompress().unwrap())
            .collect::<Vec<GroupElement>>(),
        )
        .compress();

        let a = {
          // the vector to use to decommit for sum-check test
          let a_sc = {
            let mut a = vec![Scalar::one(); degree_bound + 1];
            a[0] += Scalar::one();
            a
          };

          // the vector to use to decommit for evaluation
          let a_eval = {
            let mut a = vec![Scalar::one(); degree_bound + 1];
            for j in 1..a.len() {
              a[j] = a[j - 1] * r_i;
            }
            a
          };

          // take weighted sum of the two vectors using w
          assert_eq!(a_sc.len(), a_eval.len());
          (0..a_sc.len())
            .map(|i| w[0] * a_sc[i] + w[1] * a_eval[i])
            .collect::<Vec<Scalar>>()
        };

        self.proofs[i]
          .verify(
            gens_1,
            gens_n,
            transcript,
            &a,
            &self.comm_polys[i],
            &comm_target,
          )
          .is_ok()
      };
      if !res {
        return Err(ProofVerifyError::InternalError);
      }

      r.push(r_i);
    }

    Ok((self.comm_evals[self.comm_evals.len() - 1], r))
  }
}

impl SumcheckInstanceProof {
  pub fn prove_cubic<F>(
    claim: &Scalar,
    num_rounds: usize,
    poly_A: &mut DensePolynomial,
    poly_B: &mut DensePolynomial,
    poly_C: &mut DensePolynomial,
    comb_func: F,
    transcript: &mut Transcript,
  ) -> (Self, Vec<Scalar>, Vec<Scalar>)
  where
    F: Fn(&Scalar, &Scalar, &Scalar) -> Scalar,
  {
    let mut e = *claim;
    let mut r: Vec<Scalar> = Vec::new();
    let mut cubic_polys: Vec<CompressedUniPoly> = Vec::new();
    for _j in 0..num_rounds {
      let mut eval_point_0 = ZERO;
      let mut eval_point_2 = ZERO;
      let mut eval_point_3 = ZERO;

      let len = poly_A.len() / 2;
      for i in 0..len {
        // eval 0: bound_func is A(low)
        eval_point_0 += comb_func(&poly_A[i], &poly_B[i], &poly_C[i]);

        // eval 2: bound_func is -A(low) + 2*A(high)
        let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
        let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
        let poly_C_bound_point = poly_C[len + i] + poly_C[len + i] - poly_C[i];
        eval_point_2 += comb_func(
          &poly_A_bound_point,
          &poly_B_bound_point,
          &poly_C_bound_point,
        );

        // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
        let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
        let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
        let poly_C_bound_point = poly_C_bound_point + poly_C[len + i] - poly_C[i];

        eval_point_3 += comb_func(
          &poly_A_bound_point,
          &poly_B_bound_point,
          &poly_C_bound_point,
        );
      }

      let evals = vec![eval_point_0, e - eval_point_0, eval_point_2, eval_point_3];
      let poly = UniPoly::from_evals(&evals);

      // append the prover's message to the transcript
      poly.append_to_transcript(b"poly", transcript);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"challenge_nextround");
      r.push(r_j);
      // bound all tables to the verifier's challenege
      poly_A.bound_poly_var_top(&r_j);
      poly_B.bound_poly_var_top(&r_j);
      poly_C.bound_poly_var_top(&r_j);
      e = poly.evaluate(&r_j);
      cubic_polys.push(poly.compress());
    }

    (
      SumcheckInstanceProof::new(cubic_polys),
      r,
      vec![poly_A[0], poly_B[0], poly_C[0]],
    )
  }

  pub fn prove_cubic_batched<F>(
    claim: &Scalar,
    num_rounds: usize,
    poly_vec_par: (
      &mut Vec<&mut DensePolynomial>,
      &mut Vec<&mut DensePolynomial>,
      &mut DensePolynomial,
    ),
    poly_vec_seq: (
      &mut Vec<&mut DensePolynomial>,
      &mut Vec<&mut DensePolynomial>,
      &mut Vec<&mut DensePolynomial>,
    ),
    coeffs: &[Scalar],
    comb_func: F,
    transcript: &mut Transcript,
  ) -> (
    Self,
    Vec<Scalar>,
    (Vec<Scalar>, Vec<Scalar>, Scalar),
    (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>),
  )
  where
    F: Fn(&Scalar, &Scalar, &Scalar) -> Scalar,
  {
    let (poly_A_vec_par, poly_B_vec_par, poly_C_par) = poly_vec_par;
    let (poly_A_vec_seq, poly_B_vec_seq, poly_C_vec_seq) = poly_vec_seq;

    //let (poly_A_vec_seq, poly_B_vec_seq, poly_C_vec_seq) = poly_vec_seq;
    let mut e = *claim;
    let mut r: Vec<Scalar> = Vec::new();
    let mut cubic_polys: Vec<CompressedUniPoly> = Vec::new();

    for _j in 0..num_rounds {
      let mut evals: Vec<(Scalar, Scalar, Scalar)> = Vec::new();

      for (poly_A, poly_B) in poly_A_vec_par.iter().zip(poly_B_vec_par.iter()) {
        let mut eval_point_0 = ZERO;
        let mut eval_point_2 = ZERO;
        let mut eval_point_3 = ZERO;

        let len = poly_A.len() / 2;
        for i in 0..len {
          // eval 0: bound_func is A(low)
          eval_point_0 += comb_func(&poly_A[i], &poly_B[i], &poly_C_par[i]);

          // eval 2: bound_func is -A(low) + 2*A(high)
          let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C_par[len + i] + poly_C_par[len + i] - poly_C_par[i];
          eval_point_2 += comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
          );

          // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
          let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C_bound_point + poly_C_par[len + i] - poly_C_par[i];

          eval_point_3 += comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
          );
        }

        evals.push((eval_point_0, eval_point_2, eval_point_3));
      }

      for (poly_A, poly_B, poly_C) in izip!(
        poly_A_vec_seq.iter(),
        poly_B_vec_seq.iter(),
        poly_C_vec_seq.iter()
      ) {
        let mut eval_point_0 = ZERO;
        let mut eval_point_2 = ZERO;
        let mut eval_point_3 = ZERO;
        let len = poly_A.len() / 2;
        for i in 0..len {
          // eval 0: bound_func is A(low)
          eval_point_0 += comb_func(&poly_A[i], &poly_B[i], &poly_C[i]);
          // eval 2: bound_func is -A(low) + 2*A(high)
          let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C[len + i] + poly_C[len + i] - poly_C[i];
          eval_point_2 += comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
          );
          // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
          let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C_bound_point + poly_C[len + i] - poly_C[i];
          eval_point_3 += comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
          );
        }
        evals.push((eval_point_0, eval_point_2, eval_point_3));
      }

      let evals_combined_0 = (0..evals.len()).map(|i| evals[i].0 * coeffs[i]).sum();
      let evals_combined_2 = (0..evals.len()).map(|i| evals[i].1 * coeffs[i]).sum();
      let evals_combined_3 = (0..evals.len()).map(|i| evals[i].2 * coeffs[i]).sum();

      let evals = vec![
        evals_combined_0,
        e - evals_combined_0,
        evals_combined_2,
        evals_combined_3,
      ];
      let poly = UniPoly::from_evals(&evals);

      // append the prover's message to the transcript
      poly.append_to_transcript(b"poly", transcript);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"challenge_nextround");
      r.push(r_j);

      // bound all tables to the verifier's challenege
      for (poly_A, poly_B) in poly_A_vec_par.iter_mut().zip(poly_B_vec_par.iter_mut()) {
        poly_A.bound_poly_var_top(&r_j);
        poly_B.bound_poly_var_top(&r_j);
      }
      poly_C_par.bound_poly_var_top(&r_j);

      for (poly_A, poly_B, poly_C) in izip!(
        poly_A_vec_seq.iter_mut(),
        poly_B_vec_seq.iter_mut(),
        poly_C_vec_seq.iter_mut()
      ) {
        poly_A.bound_poly_var_top(&r_j);
        poly_B.bound_poly_var_top(&r_j);
        poly_C.bound_poly_var_top(&r_j);
      }

      e = poly.evaluate(&r_j);
      cubic_polys.push(poly.compress());
    }

    let poly_A_par_final = (0..poly_A_vec_par.len())
      .map(|i| poly_A_vec_par[i][0])
      .collect();
    let poly_B_par_final = (0..poly_B_vec_par.len())
      .map(|i| poly_B_vec_par[i][0])
      .collect();
    let claims_prod = (poly_A_par_final, poly_B_par_final, poly_C_par[0]);

    let poly_A_seq_final = (0..poly_A_vec_seq.len())
      .map(|i| poly_A_vec_seq[i][0])
      .collect();
    let poly_B_seq_final = (0..poly_B_vec_seq.len())
      .map(|i| poly_B_vec_seq[i][0])
      .collect();
    let poly_C_seq_final = (0..poly_C_vec_seq.len())
      .map(|i| poly_C_vec_seq[i][0])
      .collect();
    let claims_dotp = (poly_A_seq_final, poly_B_seq_final, poly_C_seq_final);

    (
      SumcheckInstanceProof::new(cubic_polys),
      r,
      claims_prod,
      claims_dotp,
    )
  }
}

impl ZKSumcheckInstanceProof {
  // pub fn prove_quad<F>(
  //   claim: &Scalar,
  //   blind_claim: &Scalar,
  //   num_rounds: usize,
  //   poly_A: &mut DensePolynomial,
  //   poly_B: &mut DensePolynomial,
  //   comb_func: F,
  //   gens_1: &MultiCommitGens,
  //   gens_n: &MultiCommitGens,
  //   transcript: &mut Transcript,
  //   random_tape: &mut RandomTape,
  // ) -> (Self, Vec<Scalar>, Vec<Scalar>, Scalar)
  // where
  //   F: Fn(&Scalar, &Scalar) -> Scalar,
  // {
  //   let (blinds_poly, blinds_evals) = (
  //     random_tape.random_vector(b"blinds_poly", num_rounds),
  //     random_tape.random_vector(b"blinds_evals", num_rounds),
  //   );
  //   let mut claim_per_round = *claim;
  //   let mut comm_claim_per_round = claim_per_round.commit(blind_claim, gens_1).compress();

  //   let mut r: Vec<Scalar> = Vec::new();
  //   let mut comm_polys: Vec<CompressedGroup> = Vec::new();
  //   let mut comm_evals: Vec<CompressedGroup> = Vec::new();
  //   let mut proofs: Vec<DotProductProof> = Vec::new();

  //   for j in 0..num_rounds {
  //     let (poly, comm_poly) = {
  //       let mut eval_point_0 = Scalar::zero();
  //       let mut eval_point_2 = Scalar::zero();

  //       let len = poly_A.len() / 2;
  //       for i in 0..len {
  //         // eval 0: bound_func is A(low)
  //         eval_point_0 += comb_func(&poly_A[i], &poly_B[i]);

  //         // eval 2: bound_func is -A(low) + 2*A(high)
  //         let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
  //         let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
  //         eval_point_2 += comb_func(&poly_A_bound_point, &poly_B_bound_point);
  //       }

  //       let evals = vec![eval_point_0, claim_per_round - eval_point_0, eval_point_2];
  //       let poly = UniPoly::from_evals(&evals);
  //       let comm_poly = poly.commit(gens_n, &blinds_poly[j]).compress();
  //       (poly, comm_poly)
  //     };

  //     // append the prover's message to the transcript
  //     comm_poly.append_to_transcript(b"comm_poly", transcript);
  //     comm_polys.push(comm_poly);

  //     //derive the verifier's challenge for the next round
  //     let r_j = transcript.challenge_scalar(b"challenge_nextround");

  //     // bound all tables to the verifier's challenege
  //     poly_A.bound_poly_var_top(&r_j);
  //     poly_B.bound_poly_var_top(&r_j);

  //     // produce a proof of sum-check and of evaluation
  //     let (proof, claim_next_round, comm_claim_next_round) = {
  //       let eval = poly.evaluate(&r_j);
  //       let comm_eval = eval.commit(&blinds_evals[j], gens_1).compress();

  //       // we need to prove the following under homomorphic commitments:
  //       // (1) poly(0) + poly(1) = claim_per_round
  //       // (2) poly(r_j) = eval

  //       // Our technique is to leverage dot product proofs:
  //       // (1) we can prove: <poly_in_coeffs_form, (2, 1, 1, 1)> = claim_per_round
  //       // (2) we can prove: <poly_in_coeffs_form, (1, r_j, r^2_j, ..) = eval
  //       // for efficiency we batch them using random weights

  //       // add two claims to transcript
  //       comm_claim_per_round.append_to_transcript(b"comm_claim_per_round", transcript);
  //       comm_eval.append_to_transcript(b"comm_eval", transcript);

  //       // produce two weights
  //       let w = transcript.challenge_vector(b"combine_two_claims_to_one", 2);

  //       // compute a weighted sum of the RHS
  //       let target = w[0] * claim_per_round + w[1] * eval;
  //       let comm_target = GroupElement::vartime_multiscalar_mul(
  //         w.iter(),
  //         iter::once(&comm_claim_per_round)
  //           .chain(iter::once(&comm_eval))
  //           .map(|pt| pt.decompress().unwrap())
  //           .collect::<Vec<GroupElement>>(),
  //       )
  //       .compress();

  //       let blind = {
  //         let blind_sc = if j == 0 {
  //           blind_claim
  //         } else {
  //           &blinds_evals[j - 1]
  //         };

  //         let blind_eval = &blinds_evals[j];

  //         w[0] * blind_sc + w[1] * blind_eval
  //       };
  //       assert_eq!(target.commit(&blind, gens_1).compress(), comm_target);

  //       let a = {
  //         // the vector to use to decommit for sum-check test
  //         let a_sc = {
  //           let mut a = vec![Scalar::one(); poly.degree() + 1];
  //           a[0] += Scalar::one();
  //           a
  //         };

  //         // the vector to use to decommit for evaluation
  //         let a_eval = {
  //           let mut a = vec![Scalar::one(); poly.degree() + 1];
  //           for j in 1..a.len() {
  //             a[j] = a[j - 1] * r_j;
  //           }
  //           a
  //         };

  //         // take weighted sum of the two vectors using w
  //         assert_eq!(a_sc.len(), a_eval.len());
  //         (0..a_sc.len())
  //           .map(|i| w[0] * a_sc[i] + w[1] * a_eval[i])
  //           .collect::<Vec<Scalar>>()
  //       };

  //       let (proof, _comm_poly, _comm_sc_eval) = DotProductProof::prove(
  //         gens_1,
  //         gens_n,
  //         transcript,
  //         random_tape,
  //         &poly.as_vec(),
  //         &blinds_poly[j],
  //         &a,
  //         &target,
  //         &blind,
  //       );

  //       (proof, eval, comm_eval)
  //     };

  //     claim_per_round = claim_next_round;
  //     comm_claim_per_round = comm_claim_next_round;

  //     proofs.push(proof);
  //     r.push(r_j);
  //     comm_evals.push(comm_claim_per_round);
  //   }

  //   (
  //     ZKSumcheckInstanceProof::new(comm_polys, comm_evals, proofs),
  //     r,
  //     vec![poly_A[0], poly_B[0]],
  //     blinds_evals[num_rounds - 1],
  //   )
  // }

  // pub fn prove_cubic_with_additive_term<F>(
  //   claim: &Scalar,
  //   blind_claim: &Scalar,
  //   num_rounds: usize,
  //   poly_A: &mut DensePolynomial,
  //   poly_B: &mut DensePolynomial,
  //   poly_C: &mut DensePolynomial,
  //   poly_D: &mut DensePolynomial,
  //   comb_func: F,
  //   gens_1: &MultiCommitGens,
  //   gens_n: &MultiCommitGens,
  //   transcript: &mut Transcript,
  //   random_tape: &mut RandomTape,
  // ) -> (Self, Vec<Scalar>, Vec<Scalar>, Scalar)
  // where
  //   F: Fn(&Scalar, &Scalar, &Scalar, &Scalar) -> Scalar,
  // {
  //   let (blinds_poly, blinds_evals) = (
  //     random_tape.random_vector(b"blinds_poly", num_rounds),
  //     random_tape.random_vector(b"blinds_evals", num_rounds),
  //   );

  //   let mut claim_per_round = *claim;
  //   let mut comm_claim_per_round = claim_per_round.commit(blind_claim, gens_1).compress();

  //   let mut r: Vec<Scalar> = Vec::new();
  //   let mut comm_polys: Vec<CompressedGroup> = Vec::new();
  //   let mut comm_evals: Vec<CompressedGroup> = Vec::new();
  //   let mut proofs: Vec<DotProductProof> = Vec::new();

  //   for j in 0..num_rounds {
  //     let (poly, comm_poly) = {
  //       let mut eval_point_0 = Scalar::zero();
  //       let mut eval_point_2 = Scalar::zero();
  //       let mut eval_point_3 = Scalar::zero();

  //       let len = poly_A.len() / 2;
  //       for i in 0..len {
  //         // eval 0: bound_func is A(low)
  //         eval_point_0 += comb_func(&poly_A[i], &poly_B[i], &poly_C[i], &poly_D[i]);

  //         // eval 2: bound_func is -A(low) + 2*A(high)
  //         let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
  //         let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
  //         let poly_C_bound_point = poly_C[len + i] + poly_C[len + i] - poly_C[i];
  //         let poly_D_bound_point = poly_D[len + i] + poly_D[len + i] - poly_D[i];
  //         eval_point_2 += comb_func(
  //           &poly_A_bound_point,
  //           &poly_B_bound_point,
  //           &poly_C_bound_point,
  //           &poly_D_bound_point,
  //         );

  //         // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
  //         let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
  //         let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
  //         let poly_C_bound_point = poly_C_bound_point + poly_C[len + i] - poly_C[i];
  //         let poly_D_bound_point = poly_D_bound_point + poly_D[len + i] - poly_D[i];
  //         eval_point_3 += comb_func(
  //           &poly_A_bound_point,
  //           &poly_B_bound_point,
  //           &poly_C_bound_point,
  //           &poly_D_bound_point,
  //         );
  //       }

  //       let evals = vec![
  //         eval_point_0,
  //         claim_per_round - eval_point_0,
  //         eval_point_2,
  //         eval_point_3,
  //       ];
  //       let poly = UniPoly::from_evals(&evals);
  //       let comm_poly = poly.commit(gens_n, &blinds_poly[j]).compress();
  //       (poly, comm_poly)
  //     };

  //     // append the prover's message to the transcript
  //     comm_poly.append_to_transcript(b"comm_poly", transcript);
  //     comm_polys.push(comm_poly);

  //     //derive the verifier's challenge for the next round
  //     let r_j = transcript.challenge_scalar(b"challenge_nextround");

  //     // bound all tables to the verifier's challenege
  //     poly_A.bound_poly_var_top(&r_j);
  //     poly_B.bound_poly_var_top(&r_j);
  //     poly_C.bound_poly_var_top(&r_j);
  //     poly_D.bound_poly_var_top(&r_j);

  //     // produce a proof of sum-check and of evaluation
  //     let (proof, claim_next_round, comm_claim_next_round) = {
  //       let eval = poly.evaluate(&r_j);
  //       let comm_eval = eval.commit(&blinds_evals[j], gens_1).compress();

  //       // we need to prove the following under homomorphic commitments:
  //       // (1) poly(0) + poly(1) = claim_per_round
  //       // (2) poly(r_j) = eval

  //       // Our technique is to leverage dot product proofs:
  //       // (1) we can prove: <poly_in_coeffs_form, (2, 1, 1, 1)> = claim_per_round
  //       // (2) we can prove: <poly_in_coeffs_form, (1, r_j, r^2_j, ..) = eval
  //       // for efficiency we batch them using random weights

  //       // add two claims to transcript
  //       comm_claim_per_round.append_to_transcript(b"comm_claim_per_round", transcript);
  //       comm_eval.append_to_transcript(b"comm_eval", transcript);

  //       // produce two weights
  //       let w = transcript.challenge_vector(b"combine_two_claims_to_one", 2);

  //       // compute a weighted sum of the RHS
  //       let target = w[0] * claim_per_round + w[1] * eval;
  //       let comm_target = GroupElement::vartime_multiscalar_mul(
  //         w.iter(),
  //         iter::once(&comm_claim_per_round)
  //           .chain(iter::once(&comm_eval))
  //           .map(|pt| pt.decompress().unwrap())
  //           .collect::<Vec<GroupElement>>(),
  //       )
  //       .compress();

  //       let blind = {
  //         let blind_sc = if j == 0 {
  //           blind_claim
  //         } else {
  //           &blinds_evals[j - 1]
  //         };

  //         let blind_eval = &blinds_evals[j];

  //         w[0] * blind_sc + w[1] * blind_eval
  //       };

  //       assert_eq!(target.commit(&blind, gens_1).compress(), comm_target);

  //       let a = {
  //         // the vector to use to decommit for sum-check test
  //         let a_sc = {
  //           let mut a = vec![Scalar::one(); poly.degree() + 1];
  //           a[0] += Scalar::one();
  //           a
  //         };

  //         // the vector to use to decommit for evaluation
  //         let a_eval = {
  //           let mut a = vec![Scalar::one(); poly.degree() + 1];
  //           for j in 1..a.len() {
  //             a[j] = a[j - 1] * r_j;
  //           }
  //           a
  //         };

  //         // take weighted sum of the two vectors using w
  //         assert_eq!(a_sc.len(), a_eval.len());
  //         (0..a_sc.len())
  //           .map(|i| w[0] * a_sc[i] + w[1] * a_eval[i])
  //           .collect::<Vec<Scalar>>()
  //       };

  //       let (proof, _comm_poly, _comm_sc_eval) = DotProductProof::prove(
  //         gens_1,
  //         gens_n,
  //         transcript,
  //         random_tape,
  //         &poly.as_vec(),
  //         &blinds_poly[j],
  //         &a,
  //         &target,
  //         &blind,
  //       );

  //       (proof, eval, comm_eval)
  //     };

  //     proofs.push(proof);
  //     claim_per_round = claim_next_round;
  //     comm_claim_per_round = comm_claim_next_round;
  //     r.push(r_j);
  //     comm_evals.push(comm_claim_per_round);
  //   }

  //   (
  //     ZKSumcheckInstanceProof::new(comm_polys, comm_evals, proofs),
  //     r,
  //     vec![poly_A[0], poly_B[0], poly_C[0], poly_D[0]],
  //     blinds_evals[num_rounds - 1],
  //   )
  // }

  pub fn prove_cubic_disjoint_rounds<F>(
    claim: &Scalar,
    blind_claim: &Scalar,
    num_rounds: usize,
    num_rounds_y_max: usize,
    num_rounds_w: usize,
    num_rounds_p: usize,
    single_inst: bool, // indicates whether poly_B only has one instance
    num_witness_secs: usize,
    mut num_inputs: Vec<usize>,
    poly_A: &mut DensePolynomial,
    poly_B: &mut DensePolynomialPqx,
    poly_C: &mut DensePolynomialPqx,
    comb_func: F,
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (Self, Vec<Scalar>, Vec<Scalar>, Scalar)
  where
    F: Fn(&Scalar, &Scalar, &Scalar) -> Scalar,
  {
    // NOTE: if single_inst, number of instances in poly_B is 1, might not match with instance_len!
    // NOTE: num_proofs must be 1!
    // We perform sumcheck in y -> w -> p order, but all polynomials have parameters (p, w, y)
    // poly_A is the EQ polynomial of size P * W * Y_max
    assert_eq!(num_rounds, num_rounds_y_max + num_rounds_w + num_rounds_p);

    let (blinds_poly, blinds_evals) = (
      random_tape.random_vector(b"blinds_poly", num_rounds),
      random_tape.random_vector(b"blinds_evals", num_rounds),
    );

    let mut claim_per_round = *claim;
    let mut comm_claim_per_round = claim_per_round.commit(blind_claim, gens_1).compress();

    let mut r: Vec<Scalar> = Vec::new();
    let mut comm_polys: Vec<CompressedGroup> = Vec::new();
    let mut comm_evals: Vec<CompressedGroup> = Vec::new();
    let mut proofs: Vec<DotProductProof> = Vec::new();

    let mut inputs_len = num_rounds_y_max.pow2();
    let mut witness_secs_len = num_rounds_w.pow2();
    let mut instance_len: usize = num_rounds_p.pow2();

    for j in 0..num_rounds {
      /* For debugging only */
      /* If the value is not 0, the instance / input is wrong */
      /*
      if j == 0 {
        println!("\nNEW INSTANCE");
        let mut expected = ZERO;
        for p in 0..min(instance_len, num_inputs.len()) {
          let p_inst = if single_inst { 0 } else { p };
          for w in 0..min(witness_secs_len, num_witness_secs) {
            for y_rev in 0..inputs_len {
              let val = poly_A[p] * poly_B.index(p_inst, 0, w, y_rev) * poly_C.index(p, 0, w, y_rev);
              expected += val;
            }
          }
        }
        println!("CLAIM: {:?}", claim_per_round);
        println!("EXPECTED: {:?}", expected);
      }
      */

      // Use mode to decide which variable we are working with
      // Mode = 1 ==> p
      // Mode = 3 ==> w
      // Mode = 4 ==> x (y)
      let mode = if j < num_rounds_y_max {
        MODE_X
      } else if j < num_rounds_y_max + num_rounds_w {
        MODE_W
      } else {
        MODE_P
      };

      if inputs_len > 1 {
        inputs_len /= 2
      } else if witness_secs_len > 1 {
        witness_secs_len /= 2
      } else {
        instance_len /= 2
      };

      let (poly, comm_poly) = {
        let mut eval_point_0 = ZERO;
        let mut eval_point_2 = ZERO;
        let mut eval_point_3 = ZERO;

        // We are guaranteed initially instance_len < num_inputs.len() < instance_len x 2
        // So min(instance_len, num_proofs.len()) suffices
        for p in 0..min(instance_len, num_inputs.len()) {
          let p_inst = if single_inst { 0 } else { p };
          if mode == MODE_X && num_inputs[p] > 1 {
            num_inputs[p] /= 2;
          }
          for w in 0..min(witness_secs_len, num_witness_secs) {
            for y in 0..num_inputs[p] {
              // evaluate A on p, w, y
              let poly_A_index_p_w_y = poly_A[p];

              // evaluate A on p_high, q_high, x_high
              let poly_A_index_high_p_w_y = match mode {
                MODE_P => poly_A[p + instance_len],
                MODE_W => poly_A[p],
                MODE_X => poly_A[p],
                _ => {
                  panic!(
                    "DensePolynomialPqx bound failed: unrecognized mode {}!",
                    mode
                  );
                }
              };

              // eval 0: bound_func is A(low)
              eval_point_0 += comb_func(
                &poly_A_index_p_w_y,
                &poly_B.index(p_inst, 0, w, y),
                &poly_C.index(p, 0, w, y),
              ); // Az[0, x, x, x, ...]

              // eval 2: bound_func is -A(low) + 2*A(high)
              let poly_A_bound_point =
                poly_A_index_high_p_w_y + poly_A_index_high_p_w_y - poly_A_index_p_w_y;
              let poly_B_bound_point = poly_B.index_high(p_inst, 0, w, y, mode)
                + poly_B.index_high(p_inst, 0, w, y, mode)
                - poly_B.index(p_inst, 0, w, y); // Az[2, x, x, ...]
              let poly_C_bound_point = poly_C.index_high(p, 0, w, y, mode)
                + poly_C.index_high(p, 0, w, y, mode)
                - poly_C.index(p, 0, w, y);
              eval_point_2 += comb_func(
                &poly_A_bound_point,
                &poly_B_bound_point,
                &poly_C_bound_point,
              );

              // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
              let poly_A_bound_point =
                poly_A_bound_point + poly_A_index_high_p_w_y - poly_A_index_p_w_y;
              let poly_B_bound_point = poly_B_bound_point
                + poly_B.index_high(p_inst, 0, w, y, mode)
                - poly_B.index(p_inst, 0, w, y); // Az[3, x, x, ...]
              let poly_C_bound_point =
                poly_C_bound_point + poly_C.index_high(p, 0, w, y, mode) - poly_C.index(p, 0, w, y);
              eval_point_3 += comb_func(
                &poly_A_bound_point,
                &poly_B_bound_point,
                &poly_C_bound_point,
              );
            }
          }
        }

        let evals = vec![
          eval_point_0,
          claim_per_round - eval_point_0,
          eval_point_2,
          eval_point_3,
        ];
        let poly = UniPoly::from_evals(&evals);
        let comm_poly = poly.commit(gens_n, &blinds_poly[j]).compress();
        (poly, comm_poly)
      };

      // append the prover's message to the transcript
      comm_poly.append_to_transcript(b"comm_poly", transcript);
      comm_polys.push(comm_poly);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"challenge_nextround");

      // bound all tables to the verifier's challenege
      if mode == MODE_P {
        poly_A.bound_poly_var_top(&r_j);
      }
      if mode != MODE_P || !single_inst {
        poly_B.bound_poly(&r_j, mode);
      }
      poly_C.bound_poly(&r_j, mode);

      // produce a proof of sum-check and of evaluation
      let (proof, claim_next_round, comm_claim_next_round) = {
        let eval = poly.evaluate(&r_j);
        let comm_eval = eval.commit(&blinds_evals[j], gens_1).compress();

        // we need to prove the following under homomorphic commitments:
        // (1) poly(0) + poly(1) = claim_per_round
        // (2) poly(r_j) = eval

        // Our technique is to leverage dot product proofs:
        // (1) we can prove: <poly_in_coeffs_form, (2, 1, 1, 1)> = claim_per_round
        // (2) we can prove: <poly_in_coeffs_form, (1, r_j, r^2_j, ..) = eval
        // for efficiency we batch them using random weights

        // add two claims to transcript
        comm_claim_per_round.append_to_transcript(b"comm_claim_per_round", transcript);
        comm_eval.append_to_transcript(b"comm_eval", transcript);

        // produce two weights
        let w = transcript.challenge_vector(b"combine_two_claims_to_one", 2);

        // compute a weighted sum of the RHS
        let target = w[0] * claim_per_round + w[1] * eval;
        let comm_target = GroupElement::vartime_multiscalar_mul(
          w.iter(),
          iter::once(&comm_claim_per_round)
            .chain(iter::once(&comm_eval))
            .map(|pt| pt.decompress().unwrap())
            .collect::<Vec<GroupElement>>(),
        )
        .compress();

        let blind = {
          let blind_sc = if j == 0 {
            blind_claim
          } else {
            &blinds_evals[j - 1]
          };

          let blind_eval = &blinds_evals[j];

          w[0] * blind_sc + w[1] * blind_eval
        };
        assert_eq!(target.commit(&blind, gens_1).compress(), comm_target);

        let a = {
          // the vector to use to decommit for sum-check test
          let a_sc = {
            let mut a = vec![Scalar::one(); poly.degree() + 1];
            a[0] += Scalar::one();
            a
          };
          // the vector to use to decommit for evaluation
          let a_eval = {
            let mut a = vec![Scalar::one(); poly.degree() + 1];
            for j in 1..a.len() {
              a[j] = a[j - 1] * r_j;
            }
            a
          };
          // take weighted sum of the two vectors using w
          assert_eq!(a_sc.len(), a_eval.len());
          (0..a_sc.len())
            .map(|i| w[0] * a_sc[i] + w[1] * a_eval[i])
            .collect::<Vec<Scalar>>()
        };
        let (proof, _comm_poly, _comm_sc_eval) = DotProductProof::prove(
          gens_1,
          gens_n,
          transcript,
          random_tape,
          &poly.as_vec(),
          &blinds_poly[j],
          &a,
          &target,
          &blind,
        );
        (proof, eval, comm_eval)
      };
      proofs.push(proof);
      claim_per_round = claim_next_round;
      comm_claim_per_round = comm_claim_next_round;
      r.push(r_j);
      comm_evals.push(comm_claim_per_round);
    }
    (
      ZKSumcheckInstanceProof::new(comm_polys, comm_evals, proofs),
      r,
      vec![
        poly_A[0],
        poly_B.index(0, 0, 0, 0),
        poly_C.index(0, 0, 0, 0),
      ],
      blinds_evals[num_rounds - 1],
    )
  }

  pub fn prove_cubic_with_additive_term_disjoint_rounds<F>(
    claim: &Scalar,
    blind_claim: &Scalar,
    num_rounds: usize,
    num_rounds_x_max: usize,
    num_rounds_q_max: usize,
    num_rounds_p: usize,
    mut num_proofs: Vec<usize>,
    mut num_cons: Vec<usize>,
    poly_Ap: &mut DensePolynomial,
    poly_Aq: &mut DensePolynomial,
    poly_Ax: &mut DensePolynomial,
    poly_B: &mut DensePolynomialPqx,
    poly_C: &mut DensePolynomialPqx,
    poly_D: &mut DensePolynomialPqx,
    comb_func: F,
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (Self, Vec<Scalar>, Vec<Scalar>, Scalar)
  where
    F: Fn(&Scalar, &Scalar, &Scalar, &Scalar) -> Scalar,
  {
    // Note: num_witness_secs must be 1!
    // We perform sumcheck in x -> q_rev -> p order, but all polynomials have parameters (p, q, x)
    // poly_A is the EQ polynomial of size P * Q_max * X
    // poly_BCD are the AzBzCz polynomials, with size Q_sum * X
    // Thus, we need to separate the rounds into rounds for X, Q_rev, and P
    assert_eq!(
      num_rounds,
      num_rounds_x_max + num_rounds_q_max + num_rounds_p
    );
    assert_eq!(poly_B.num_witness_secs, 1);
    assert_eq!(poly_C.num_witness_secs, 1);
    assert_eq!(poly_D.num_witness_secs, 1);

    let (blinds_poly, blinds_evals) = (
      random_tape.random_vector(b"blinds_poly", num_rounds),
      random_tape.random_vector(b"blinds_evals", num_rounds),
    );

    let mut claim_per_round = *claim;
    let mut comm_claim_per_round = claim_per_round.commit(blind_claim, gens_1).compress();

    let mut r: Vec<Scalar> = Vec::new();
    let mut comm_polys: Vec<CompressedGroup> = Vec::new();
    let mut comm_evals: Vec<CompressedGroup> = Vec::new();
    let mut proofs: Vec<DotProductProof> = Vec::new();

    let mut cons_len = num_rounds_x_max.pow2();
    let mut proof_len = num_rounds_q_max.pow2();
    let mut instance_len: usize = num_rounds_p.pow2();

    for j in 0..num_rounds {
      /* For debugging only */
      /* If the value is not 0, the instance / input is wrong */
      /*
      if j == 0 {
        println!("\nNEW INSTANCE");
        let mut expected = ZERO;
        for p in 0..min(instance_len, num_proofs.len()) {
          let step_q = proof_len / num_proofs[p];
          let step_x = cons_len / num_cons[p];
          for q_rev in 0..num_proofs[p] {
            for x_rev in 0..num_cons[p] {
              let val = poly_Ap[p] * poly_Aq[q_rev * step_q] * poly_Ax[x_rev * step_x] * (poly_B.index(p, q_rev, 0, x_rev) * poly_C.index(p, q_rev, 0, x_rev) - poly_D.index(p, q_rev, 0, x_rev));
              let q = rev_bits(q_rev * step_q, proof_len);
              let x = rev_bits(x_rev * step_x, cons_len);
              if val != ZERO { println!("p: {}, q: {}, x: {}, val: {:?}", p, q, x, val); }
              expected += val;
            }
          }
        }
        println!("CLAIM: {:?}", claim_per_round);
        println!("EXPECTED: {:?}", expected);
      }
      */

      // Use mode to decide which variable we are working with
      // Mode = 1 ==> p
      // Mode = 2 ==> q
      // Mode = 4 ==> x
      let mode = if j < num_rounds_x_max {
        MODE_X
      } else if j < num_rounds_x_max + num_rounds_q_max {
        MODE_Q
      } else {
        MODE_P
      };

      if cons_len > 1 {
        cons_len /= 2
      } else if proof_len > 1 {
        proof_len /= 2
      } else {
        instance_len /= 2
      };

      let (poly, comm_poly) = {
        let mut eval_point_0 = ZERO;
        let mut eval_point_2 = ZERO;
        let mut eval_point_3 = ZERO;

        // We are guaranteed initially instance_len < num_proofs.len() < instance_len x 2
        // So min(instance_len, num_proofs.len()) suffices
        for p in 0..min(instance_len, num_proofs.len()) {
          if mode == MODE_X && num_cons[p] > 1 {
            num_cons[p] /= 2;
          }
          // If q > num_proofs[p], the polynomials always evaluate to 0
          if mode == MODE_Q && num_proofs[p] > 1 {
            num_proofs[p] /= 2;
          }
          for q in 0..num_proofs[p] {
            let step_q = proof_len / num_proofs[p];
            let step_x = cons_len / num_cons[p];
            for x in 0..num_cons[p] {
              // evaluate Ap, Aq, Ax on p, q, x
              let poly_A_index_p_q_x = poly_Ap[p] * poly_Aq[q * step_q] * poly_Ax[x * step_x];

              // evaluate Ap, Aq, Ax on p_high, q_high, x_high
              let poly_A_index_high_p_q_x = match mode {
                MODE_P => poly_Ap[p + instance_len] * poly_Aq[q * step_q] * poly_Ax[x * step_x],
                MODE_Q => poly_Ap[p] * poly_Aq[q * step_q + proof_len] * poly_Ax[x * step_x],
                MODE_X => poly_Ap[p] * poly_Aq[q * step_q] * poly_Ax[x * step_x + cons_len],
                _ => {
                  panic!(
                    "DensePolynomialPqx bound failed: unrecognized mode {}!",
                    mode
                  );
                }
              };

              // eval 0: bound_func is A(low)
              eval_point_0 += comb_func(
                &poly_A_index_p_q_x,
                &poly_B.index(p, q, 0, x),
                &poly_C.index(p, q, 0, x),
                &poly_D.index(p, q, 0, x),
              ); // Az[0, x, x, x, ...]

              // eval 2: bound_func is -A(low) + 2*A(high)
              let poly_A_bound_point =
                poly_A_index_high_p_q_x + poly_A_index_high_p_q_x - poly_A_index_p_q_x;
              let poly_B_bound_point = poly_B.index_high(p, q, 0, x, mode)
                + poly_B.index_high(p, q, 0, x, mode)
                - poly_B.index(p, q, 0, x); // Az[2, x, x, ...]
              let poly_C_bound_point = poly_C.index_high(p, q, 0, x, mode)
                + poly_C.index_high(p, q, 0, x, mode)
                - poly_C.index(p, q, 0, x);
              let poly_D_bound_point = poly_D.index_high(p, q, 0, x, mode)
                + poly_D.index_high(p, q, 0, x, mode)
                - poly_D.index(p, q, 0, x);
              eval_point_2 += comb_func(
                &poly_A_bound_point,
                &poly_B_bound_point,
                &poly_C_bound_point,
                &poly_D_bound_point,
              );

              // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
              let poly_A_bound_point =
                poly_A_bound_point + poly_A_index_high_p_q_x - poly_A_index_p_q_x;
              let poly_B_bound_point =
                poly_B_bound_point + poly_B.index_high(p, q, 0, x, mode) - poly_B.index(p, q, 0, x); // Az[3, x, x, ...]
              let poly_C_bound_point =
                poly_C_bound_point + poly_C.index_high(p, q, 0, x, mode) - poly_C.index(p, q, 0, x);
              let poly_D_bound_point =
                poly_D_bound_point + poly_D.index_high(p, q, 0, x, mode) - poly_D.index(p, q, 0, x);
              eval_point_3 += comb_func(
                &poly_A_bound_point,
                &poly_B_bound_point,
                &poly_C_bound_point,
                &poly_D_bound_point,
              );
            }
          }
        }

        let evals = vec![
          eval_point_0,
          claim_per_round - eval_point_0,
          eval_point_2,
          eval_point_3,
        ];
        let poly = UniPoly::from_evals(&evals);
        let comm_poly = poly.commit(gens_n, &blinds_poly[j]).compress();
        (poly, comm_poly)
      };

      // append the prover's message to the transcript
      comm_poly.append_to_transcript(b"comm_poly", transcript);
      comm_polys.push(comm_poly);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"challenge_nextround");

      // bound all tables to the verifier's challenege
      if mode == 1 {
        poly_Ap.bound_poly_var_top(&r_j);
      } else if mode == 2 {
        poly_Aq.bound_poly_var_top(&r_j);
      } else {
        poly_Ax.bound_poly_var_top(&r_j);
      }
      poly_B.bound_poly(&r_j, mode);
      poly_C.bound_poly(&r_j, mode);
      poly_D.bound_poly(&r_j, mode);

      // produce a proof of sum-check and of evaluation
      let (proof, claim_next_round, comm_claim_next_round) = {
        let eval = poly.evaluate(&r_j);
        let comm_eval = eval.commit(&blinds_evals[j], gens_1).compress();

        // we need to prove the following under homomorphic commitments:
        // (1) poly(0) + poly(1) = claim_per_round
        // (2) poly(r_j) = eval

        // Our technique is to leverage dot product proofs:
        // (1) we can prove: <poly_in_coeffs_form, (2, 1, 1, 1)> = claim_per_round
        // (2) we can prove: <poly_in_coeffs_form, (1, r_j, r^2_j, ..) = eval
        // for efficiency we batch them using random weights

        // add two claims to transcript
        comm_claim_per_round.append_to_transcript(b"comm_claim_per_round", transcript);
        comm_eval.append_to_transcript(b"comm_eval", transcript);

        // produce two weights
        let w = transcript.challenge_vector(b"combine_two_claims_to_one", 2);

        // compute a weighted sum of the RHS
        let target = w[0] * claim_per_round + w[1] * eval;
        let comm_target = GroupElement::vartime_multiscalar_mul(
          w.iter(),
          iter::once(&comm_claim_per_round)
            .chain(iter::once(&comm_eval))
            .map(|pt| pt.decompress().unwrap())
            .collect::<Vec<GroupElement>>(),
        )
        .compress();

        let blind = {
          let blind_sc = if j == 0 {
            blind_claim
          } else {
            &blinds_evals[j - 1]
          };

          let blind_eval = &blinds_evals[j];

          w[0] * blind_sc + w[1] * blind_eval
        };

        assert_eq!(target.commit(&blind, gens_1).compress(), comm_target);

        let a = {
          // the vector to use to decommit for sum-check test
          let a_sc = {
            let mut a = vec![Scalar::one(); poly.degree() + 1];
            a[0] += Scalar::one();
            a
          };

          // the vector to use to decommit for evaluation
          let a_eval = {
            let mut a = vec![Scalar::one(); poly.degree() + 1];
            for j in 1..a.len() {
              a[j] = a[j - 1] * r_j;
            }
            a
          };

          // take weighted sum of the two vectors using w
          assert_eq!(a_sc.len(), a_eval.len());
          (0..a_sc.len())
            .map(|i| w[0] * a_sc[i] + w[1] * a_eval[i])
            .collect::<Vec<Scalar>>()
        };

        let (proof, _comm_poly, _comm_sc_eval) = DotProductProof::prove(
          gens_1,
          gens_n,
          transcript,
          random_tape,
          &poly.as_vec(),
          &blinds_poly[j],
          &a,
          &target,
          &blind,
        );

        (proof, eval, comm_eval)
      };

      proofs.push(proof);
      claim_per_round = claim_next_round;
      comm_claim_per_round = comm_claim_next_round;
      r.push(r_j);
      comm_evals.push(comm_claim_per_round);
    }

    (
      ZKSumcheckInstanceProof::new(comm_polys, comm_evals, proofs),
      r,
      vec![
        poly_Ap[0] * poly_Aq[0] * poly_Ax[0],
        poly_B.index(0, 0, 0, 0),
        poly_C.index(0, 0, 0, 0),
        poly_D.index(0, 0, 0, 0),
      ],
      blinds_evals[num_rounds - 1],
    )
  }
}
