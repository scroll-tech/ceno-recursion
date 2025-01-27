#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
use crate::custom_dense_mlpoly::DensePolynomialPqx;
use crate::math::Math;
use ff_ext::ExtensionField;

use super::dense_mlpoly::DensePolynomial;
use super::errors::ProofVerifyError;
use super::transcript::{Transcript, challenge_scalar};
use super::unipoly::{CompressedUniPoly, UniPoly};
use itertools::izip;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use serde::{Deserialize, Serialize};
use std::cmp::min;

const MODE_P: usize = 1;
const MODE_Q: usize = 2;
const MODE_W: usize = 3;
const MODE_X: usize = 4;

#[derive(Serialize, Deserialize, Debug)]
pub struct SumcheckInstanceProof<E: ExtensionField> {
  compressed_polys: Vec<CompressedUniPoly<E>>,
}

impl<E: ExtensionField> SumcheckInstanceProof<E> {
  pub fn new(compressed_polys: Vec<CompressedUniPoly<E>>) -> SumcheckInstanceProof<E> {
    SumcheckInstanceProof { compressed_polys }
  }

  pub fn verify(
    &self,
    claim: E,
    num_rounds: usize,
    degree_bound: usize,
    transcript: &mut Transcript<E>,
  ) -> Result<(E, Vec<E>), ProofVerifyError> {
    let mut e = claim;
    let mut r: Vec<E> = Vec::new();

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
      let r_i = challenge_scalar(transcript, b"challenge_nextround");

      // scalar_debug
      // println!("=> SumcheckInstanceProof-verify, challenge round {:?} - {:?}", i, r_i);

      r.push(r_i);

      // evaluate the claimed degree-ell polynomial at r_i
      e = poly.evaluate(&r_i);
    }

    Ok((e, r))
  }
}

impl<E: ExtensionField> SumcheckInstanceProof<E> {
  pub fn prove_cubic<F>(
    claim: &E,
    num_rounds: usize,
    poly_A: &mut DensePolynomial<E>,
    poly_B: &mut DensePolynomial<E>,
    poly_C: &mut DensePolynomial<E>,
    comb_func: F,
    transcript: &mut Transcript<E>,
  ) -> (Self, Vec<E>, Vec<E>)
  where
    F: Fn(&E, &E, &E) -> E,
  {
    let mut e = *claim;
    let mut r: Vec<E> = Vec::new();
    let mut cubic_polys: Vec<CompressedUniPoly<E>> = Vec::new();
    for _j in 0..num_rounds {
      let mut eval_point_0 = E::ZERO;
      let mut eval_point_2 = E::ZERO;
      let mut eval_point_3 = E::ZERO;

      let len = poly_A.len() / 2;
      for i in 0..len {
        // eval 0: bound_func is A(low)
        eval_point_0 += comb_func(&poly_A[i], &poly_B[i], &poly_C[i]);

        // eval 2: bound_func is -A(low) + 2*A(high)
        let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
        let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
        let poly_C_bound_point = poly_C[len + i] + poly_C[len + i] - poly_C[i];
        eval_point_2 = eval_point_2
          + comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
          );

        // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
        let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
        let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
        let poly_C_bound_point = poly_C_bound_point + poly_C[len + i] - poly_C[i];

        eval_point_3 = eval_point_3
          + comb_func(
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
      let r_j = challenge_scalar(transcript, b"challenge_nextround");
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
    claim: &E,
    num_rounds: usize,
    poly_vec_par: (
      &mut Vec<&mut DensePolynomial<E>>,
      &mut Vec<&mut DensePolynomial<E>>,
      &mut DensePolynomial<E>,
    ),
    poly_vec_seq: (
      &mut Vec<&mut DensePolynomial<E>>,
      &mut Vec<&mut DensePolynomial<E>>,
      &mut Vec<&mut DensePolynomial<E>>,
    ),
    coeffs: &[E],
    comb_func: F,
    transcript: &mut Transcript<E>,
  ) -> (Self, Vec<E>, (Vec<E>, Vec<E>, E), (Vec<E>, Vec<E>, Vec<E>))
  where
    F: Fn(&E, &E, &E) -> E,
  {
    let (poly_A_vec_par, poly_B_vec_par, poly_C_par) = poly_vec_par;
    let (poly_A_vec_seq, poly_B_vec_seq, poly_C_vec_seq) = poly_vec_seq;

    //let (poly_A_vec_seq, poly_B_vec_seq, poly_C_vec_seq) = poly_vec_seq;
    let mut e = *claim;
    let mut r: Vec<E> = Vec::new();
    let mut cubic_polys: Vec<CompressedUniPoly<E>> = Vec::new();

    for _j in 0..num_rounds {
      let mut evals: Vec<(E, E, E)> = Vec::new();

      for (poly_A, poly_B) in poly_A_vec_par.iter().zip(poly_B_vec_par.iter()) {
        let mut eval_point_0 = E::ZERO;
        let mut eval_point_2 = E::ZERO;
        let mut eval_point_3 = E::ZERO;

        let len = poly_A.len() / 2;
        for i in 0..len {
          // eval 0: bound_func is A(low)
          eval_point_0 = eval_point_0 + comb_func(&poly_A[i], &poly_B[i], &poly_C_par[i]);

          // eval 2: bound_func is -A(low) + 2*A(high)
          let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C_par[len + i] + poly_C_par[len + i] - poly_C_par[i];
          eval_point_2 = eval_point_2
            + comb_func(
              &poly_A_bound_point,
              &poly_B_bound_point,
              &poly_C_bound_point,
            );

          // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
          let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C_bound_point + poly_C_par[len + i] - poly_C_par[i];

          eval_point_3 = eval_point_3
            + comb_func(
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
        let mut eval_point_0 = E::ZERO;
        let mut eval_point_2 = E::ZERO;
        let mut eval_point_3 = E::ZERO;
        let len = poly_A.len() / 2;
        for i in 0..len {
          // eval 0: bound_func is A(low)
          eval_point_0 = eval_point_0 + comb_func(&poly_A[i], &poly_B[i], &poly_C[i]);
          // eval 2: bound_func is -A(low) + 2*A(high)
          let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C[len + i] + poly_C[len + i] - poly_C[i];
          eval_point_2 = eval_point_2
            + comb_func(
              &poly_A_bound_point,
              &poly_B_bound_point,
              &poly_C_bound_point,
            );
          // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
          let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C_bound_point + poly_C[len + i] - poly_C[i];
          eval_point_3 = eval_point_3
            + comb_func(
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
      let r_j = challenge_scalar(transcript, b"challenge_nextround");

      // scalar_debug
      // println!("=> prove_cubic_batched, challenge round {:?} - {:?}", _j, r_j);

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
  
  pub fn prove_cubic_disjoint_rounds<F>(
    claim: &E,
    num_rounds: usize,
    num_rounds_y_max: usize,
    num_rounds_w: usize,
    num_rounds_p: usize,
    single_inst: bool, // indicates whether poly_B only has one instance
    num_witness_secs: usize,
    mut num_inputs: Vec<Vec<usize>>,
    poly_A: &mut DensePolynomial<E>,
    poly_B: &mut DensePolynomialPqx<E>,
    poly_C: &mut DensePolynomialPqx<E>,
    comb_func: F,
    transcript: &mut Transcript<E>,
  ) -> (Self, Vec<E>, Vec<E>, Vec<Vec<E>>)
  where
    F: Fn(&E, &E, &E) -> E,
  {
    let ZERO = E::ZERO;

    // NOTE: if single_inst, number of instances in poly_B is 1, might not match with instance_len!
    // NOTE: num_proofs must be 1!
    // We perform sumcheck in y -> w -> p order, but all polynomials have parameters (p, w, y)
    // poly_A is the EQ polynomial of size P * W * Y_max
    assert_eq!(num_rounds, num_rounds_y_max + num_rounds_w + num_rounds_p);

    let mut claim_per_round = *claim;

    let mut r: Vec<E> = Vec::new();
    let mut polys: Vec<CompressedUniPoly<E>> = Vec::new();

    let mut inputs_len = num_rounds_y_max.pow2();
    let mut witness_secs_len = num_rounds_w.pow2();
    let mut instance_len: usize = num_rounds_p.pow2();

    // Every variable binded to ry
    let mut claimed_vars_at_ry = Vec::new();
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
            for y in 0..min(num_inputs[p_inst][w], num_inputs[p][w]) {
              let val = poly_A[p] * poly_B.index(p_inst, 0, w, y) * poly_C.index(p, 0, w, y);
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
      if j == num_rounds_y_max {
        for p in 0..poly_C.num_instances {
          claimed_vars_at_ry.push(Vec::new());
          for w in 0..poly_C.num_witness_secs {
            claimed_vars_at_ry[p].push(poly_C.index(p, 0, w, 0));
          }
        }
      }

      if inputs_len > 1 {
        inputs_len /= 2
      } else if witness_secs_len > 1 {
        witness_secs_len /= 2
      } else {
        instance_len /= 2
      };

      let poly = {
        let mut eval_point_0 = ZERO;
        let mut eval_point_2 = ZERO;
        let mut eval_point_3 = ZERO;

        // We are guaranteed initially instance_len < num_inputs.len() < instance_len x 2
        // So min(instance_len, num_proofs.len()) suffices
        for p in 0..min(instance_len, num_inputs.len()) {
          let p_inst = if single_inst { 0 } else { p };
          for w in 0..min(witness_secs_len, num_witness_secs) {
            if mode == MODE_X && num_inputs[p][w] > 1 {
              num_inputs[p][w] /= 2;
            }
            for y in 0..num_inputs[p][w] {
              // evaluate A, B, C on p, w, y
              let (poly_A_low, poly_A_high) = match mode {
                MODE_X => (poly_A[p], poly_A[p]),
                MODE_W => (poly_A[p], poly_A[p]),
                MODE_P => (poly_A[2 * p], poly_A[2 * p + 1]),
                _ => unreachable!()
              };
              let poly_B_low = poly_B.index_low(p_inst, 0, w, y, mode);
              let poly_B_high = poly_B.index_high(p_inst, 0, w, y, mode);
              let poly_C_low = poly_C.index_low(p, 0, w, y, mode);
              let poly_C_high = poly_C.index_high(p, 0, w, y, mode);

              // eval 0: bound_func is A(low)
              eval_point_0 = eval_point_0 + comb_func(&poly_A_low, &poly_B_low, &poly_C_low); // Az[x, x, x, ..., 0]

              // eval 2: bound_func is -A(low) + 2*A(high)
              let poly_A_bound_point = poly_A_high + poly_A_high - poly_A_low;
              let poly_B_bound_point = poly_B_high + poly_B_high - poly_B_low;
              let poly_C_bound_point = poly_C_high + poly_C_high - poly_C_low;
              eval_point_2 = eval_point_2
                + comb_func(
                  &poly_A_bound_point,
                  &poly_B_bound_point,
                  &poly_C_bound_point,
                ); // Az[x, x, ..., 2]

              // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
              let poly_A_bound_point = poly_A_bound_point + poly_A_high - poly_A_low;
              let poly_B_bound_point = poly_B_bound_point + poly_B_high - poly_B_low;
              let poly_C_bound_point = poly_C_bound_point + poly_C_high - poly_C_low;
              eval_point_3 = eval_point_3
                + comb_func(
                  &poly_A_bound_point,
                  &poly_B_bound_point,
                  &poly_C_bound_point,
                ); // Az[x, x, ..., 3]
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

        poly
      };

      // append the prover's message to the transcript
      poly.append_to_transcript(b"poly", transcript);

      //derive the verifier's challenge for the next round
      let r_j = challenge_scalar(transcript, b"challenge_nextround");
      r.push(r_j);

      // bound all tables to the verifier's challenege
      if mode == MODE_P {
        poly_A.bound_poly_var_bot(&r_j);
      }
      if mode != MODE_P || !single_inst {
        poly_B.bound_poly(&r_j, mode);
      }
      poly_C.bound_poly(&r_j, mode);
      claim_per_round = poly.evaluate(&r_j);
      polys.push(poly.compress());
    }

    (
      SumcheckInstanceProof::new(polys),
      r,
      vec![
        poly_A[0],
        poly_B.index(0, 0, 0, 0),
        poly_C.index(0, 0, 0, 0),
      ],
      claimed_vars_at_ry,
    )
  }

  pub fn prove_cubic_with_additive_term_disjoint_rounds<F>(
    claim: &E,
    num_rounds: usize,
    num_rounds_x_max: usize,
    num_rounds_q_max: usize,
    num_rounds_p: usize,
    mut num_proofs: Vec<usize>,
    mut num_cons: Vec<usize>,
    poly_Ap: &mut DensePolynomial<E>,
    poly_Aq: &mut DensePolynomial<E>,
    poly_Ax: &mut DensePolynomial<E>,
    poly_B: &mut DensePolynomialPqx<E>,
    poly_C: &mut DensePolynomialPqx<E>,
    poly_D: &mut DensePolynomialPqx<E>,
    comb_func: F,
    transcript: &mut Transcript<E>,
  ) -> (Self, Vec<E>, Vec<E>)
  where
    F: Fn(&E, &E, &E, &E) -> E + std::marker::Sync,
  {
    let ZERO = E::ZERO;

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

    let mut claim_per_round = *claim;

    let mut r: Vec<E> = Vec::new();
    let mut polys: Vec<CompressedUniPoly<E>> = Vec::new();

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
          for q in 0..num_proofs[p] {
            for x in 0..num_cons[p] {
              let val = poly_Ap[p] * poly_Aq[q] * poly_Ax[x] * (poly_B.index(p, q, 0, x) * poly_C.index(p, q, 0, x) - poly_D.index(p, q, 0, x));
              // if val != ZERO { println!("p: {}, q: {}, x: {}, val: {:?}", p, q, x, val); }
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
        cons_len = cons_len.div_ceil(2);
        MODE_X
      } else if j < num_rounds_x_max + num_rounds_q_max {
        proof_len = proof_len.div_ceil(2);
        MODE_Q
      } else {
        instance_len = instance_len.div_ceil(2);
        MODE_P
      };

      let poly = {
        if mode == MODE_X {
          // Multicore evaluation in MODE_X
          let mut eval_point_0 = ZERO;
          let mut eval_point_2 = ZERO;
          let mut eval_point_3 = ZERO;

          // We are guaranteed initially instance_len < num_proofs.len() < instance_len x 2
          // So min(instance_len, num_proofs.len()) suffices
          for p in 0..min(instance_len, num_proofs.len()) {
            num_cons[p] = num_cons[p].div_ceil(2);
            (eval_point_0, eval_point_2, eval_point_3) = (0..num_proofs[p]).into_par_iter().map(|q| {
              let mut eval_point_0 = ZERO;
              let mut eval_point_2 = ZERO;
              let mut eval_point_3 = ZERO;
              for x in 0..num_cons[p] {
                // evaluate A, B, C, D on p, q, x
                let poly_A_low = poly_Ap[p] * poly_Aq[q] * poly_Ax[2 * x];
                let poly_A_high = poly_Ap[p] * poly_Aq[q] * poly_Ax[2 * x + 1];
                let poly_B_low = poly_B.index_low(p, q, 0, x, mode);
                let poly_B_high = poly_B.index_high(p, q, 0, x, mode);
                let poly_C_low = poly_C.index_low(p, q, 0, x, mode);
                let poly_C_high = poly_C.index_high(p, q, 0, x, mode);
                let poly_D_low = poly_D.index_low(p, q, 0, x, mode);
                let poly_D_high = poly_D.index_high(p, q, 0, x, mode);

                // eval 0: bound_func is A(low)
                eval_point_0 = eval_point_0
                  + comb_func(
                    &poly_A_low,
                    &poly_B_low,
                    &poly_C_low,
                    &poly_D_low,
                  ); // Az[x, x, x, ..., 0]

                // eval 2: bound_func is -A(low) + 2*A(high)
                let poly_A_bound_point = poly_A_high + poly_A_high - poly_A_low;
                let poly_B_bound_point = poly_B_high + poly_B_high - poly_B_low; 
                let poly_C_bound_point = poly_C_high + poly_C_high - poly_C_low; 
                let poly_D_bound_point = poly_D_high + poly_D_high - poly_D_low; 
                eval_point_2 = eval_point_2
                  + comb_func(
                    &poly_A_bound_point,
                    &poly_B_bound_point,
                    &poly_C_bound_point,
                    &poly_D_bound_point,
                  ); // Az[x, x, ..., 2]

                // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
                let poly_A_bound_point = poly_A_bound_point + poly_A_high - poly_A_low;
                let poly_B_bound_point = poly_B_bound_point + poly_B_high - poly_B_low;
                let poly_C_bound_point = poly_C_bound_point + poly_C_high - poly_C_low;
                let poly_D_bound_point = poly_D_bound_point + poly_D_high - poly_D_low;
                eval_point_3 = eval_point_3
                  + comb_func(
                    &poly_A_bound_point,
                    &poly_B_bound_point,
                    &poly_C_bound_point,
                    &poly_D_bound_point,
                  );  // Az[x, x, ..., 3]
              }
              (eval_point_0, eval_point_2, eval_point_3)
            }).collect::<Vec<(E, E, E)>>().into_iter().fold((eval_point_0, eval_point_2, eval_point_3), |(e0, e2, e3), (a0, a2, a3)| (e0 + a0, e2 + a2, e3 + a3));
          }

          let evals = vec![
            eval_point_0,
            claim_per_round - eval_point_0,
            eval_point_2,
            eval_point_3,
          ];
          let poly = UniPoly::from_evals(&evals);
          poly
        } else {
          // Singlecore evaluation in other Modes
          let mut eval_point_0 = ZERO;
          let mut eval_point_2 = ZERO;
          let mut eval_point_3 = ZERO;

          // We are guaranteed initially instance_len < num_proofs.len() < instance_len x 2
          // So min(instance_len, num_proofs.len()) suffices
          for p in 0..min(instance_len, num_proofs.len()) {
            // If q > num_proofs[p], the polynomials always evaluate to 0
            if mode == MODE_Q { num_proofs[p] = num_proofs[p].div_ceil(2); }
            for q in 0..num_proofs[p] {
              for x in 0..num_cons[p] {
                // evaluate A, B, C, D on p, q, x
                let (poly_A_low, poly_A_high) = match mode {
                  MODE_Q => (
                    poly_Ap[p] * poly_Aq[2 * q] * poly_Ax[x],
                    poly_Ap[p] * poly_Aq[2 * q + 1] * poly_Ax[x],
                  ),
                  MODE_P => (
                    poly_Ap[2 * p] * poly_Aq[q] * poly_Ax[x],
                    poly_Ap[2 * p + 1] * poly_Aq[q] * poly_Ax[x],
                  ),
                  _ => unreachable!()
                };
                let poly_B_low = poly_B.index_low(p, q, 0, x, mode);
                let poly_B_high = poly_B.index_high(p, q, 0, x, mode);
                let poly_C_low = poly_C.index_low(p, q, 0, x, mode);
                let poly_C_high = poly_C.index_high(p, q, 0, x, mode);
                let poly_D_low = poly_D.index_low(p, q, 0, x, mode);
                let poly_D_high = poly_D.index_high(p, q, 0, x, mode);

                // eval 0: bound_func is A(low)
                eval_point_0 = eval_point_0
                  + comb_func(
                    &poly_A_low,
                    &poly_B_low,
                    &poly_C_low,
                    &poly_D_low,
                  ); // Az[x, x, x, ..., 0]

                // eval 2: bound_func is -A(low) + 2*A(high)
                let poly_A_bound_point = poly_A_high + poly_A_high - poly_A_low;
                let poly_B_bound_point = poly_B_high + poly_B_high - poly_B_low; 
                let poly_C_bound_point = poly_C_high + poly_C_high - poly_C_low; 
                let poly_D_bound_point = poly_D_high + poly_D_high - poly_D_low; 
                eval_point_2 = eval_point_2
                  + comb_func(
                    &poly_A_bound_point,
                    &poly_B_bound_point,
                    &poly_C_bound_point,
                    &poly_D_bound_point,
                  ); // Az[x, x, ..., 2]

                // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
                let poly_A_bound_point = poly_A_bound_point + poly_A_high - poly_A_low;
                let poly_B_bound_point = poly_B_bound_point + poly_B_high - poly_B_low;
                let poly_C_bound_point = poly_C_bound_point + poly_C_high - poly_C_low;
                let poly_D_bound_point = poly_D_bound_point + poly_D_high - poly_D_low;
                eval_point_3 = eval_point_3
                  + comb_func(
                    &poly_A_bound_point,
                    &poly_B_bound_point,
                    &poly_C_bound_point,
                    &poly_D_bound_point,
                  );  // Az[x, x, ..., 3]
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
          poly
        }
      };

      // append the prover's message to the transcript
      poly.append_to_transcript(b"poly", transcript);

      //derive the verifier's challenge for the next round
      let r_j = challenge_scalar(transcript, b"challenge_nextround");
      r.push(r_j);

      // bound all tables to the verifier's challenege
      if mode == MODE_X {
        poly_Ax.bound_poly_var_bot(&r_j);
      } else if mode == MODE_Q {
        poly_Aq.bound_poly_var_bot(&r_j);
      } else if mode == MODE_P {
        poly_Ap.bound_poly_var_bot(&r_j);
      } else {
        unreachable!()
      }
      poly_B.bound_poly(&r_j, mode);
      poly_C.bound_poly(&r_j, mode);
      poly_D.bound_poly(&r_j, mode);
      claim_per_round = poly.evaluate(&r_j);
      polys.push(poly.compress());
    }

    (
      SumcheckInstanceProof::new(polys),
      r,
      vec![
        poly_Ap[0] * poly_Aq[0] * poly_Ax[0],
        poly_B.index(0, 0, 0, 0),
        poly_C.index(0, 0, 0, 0),
        poly_D.index(0, 0, 0, 0),
      ],
    )
  }
}
