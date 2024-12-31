#![allow(clippy::too_many_arguments)]
use super::custom_dense_mlpoly::DensePolynomialPqx;
use super::dense_mlpoly::{DensePolynomial, EqPolynomial};
use super::errors::ProofVerifyError;
use super::math::Math;
use super::r1csinstance::R1CSInstance;
use super::sumcheck::SumcheckInstanceProof;
use super::timer::Timer;
use super::transcript::ProofTranscript;
use crate::scalar::SpartanExtensionField;
use crate::{ProverWitnessSecInfo, VerifierWitnessSecInfo};
use goldilocks::GoldilocksExt2;
use merlin::Transcript;
use serde::Serialize;
use std::cmp::min;
use std::iter::zip;
use std::sync::Arc;
use multilinear_extensions::{
  mle::IntoMLE,
  virtual_poly::VPAuxInfo,
  virtual_poly_v2::ArcMultilinearExtension,
};
use ceno_zkvm::virtual_polys::VirtualPolynomials;
use sumcheck::structs::{IOPProof, IOPProverStateV2, IOPVerifierState};
use ff::Field;
use halo2curves::serde::SerdeObject;
use transcript::BasicTranscript;

#[derive(Serialize, Debug)]
pub struct R1CSProof<S: SpartanExtensionField> {
  sc_proof_phase1_proof: IOPProof<GoldilocksExt2>,
  sc_proof_phase2_proof: IOPProof<GoldilocksExt2>,
  claims_phase2: (S, S, S),
  // Need to commit vars for short and long witnesses separately
  // The long version must exist, the short version might not
  eval_vars_at_ry_list: Vec<Vec<S>>,
  eval_vars_at_ry: S,
  // proof_eval_vars_at_ry_list: Vec<PolyEvalProof<S>>,
  max_num_vars: usize,
  claim_phase1: GoldilocksExt2,
  max_num_vars_phase2: usize,
  claim_phase2: GoldilocksExt2,
}

impl<'a, S: SpartanExtensionField + Send + Sync> R1CSProof<S> {
  fn prove_phase_one(
    num_rounds: usize,
    num_rounds_x_max: usize,
    num_rounds_q_max: usize,
    num_rounds_p: usize,
    num_proofs: &Vec<usize>,
    num_cons: &Vec<usize>,
    evals_tau_p: &mut DensePolynomial<S>,
    evals_tau_q: &mut DensePolynomial<S>,
    evals_tau_x: &mut DensePolynomial<S>,
    evals_Az: &mut DensePolynomialPqx<S>,
    evals_Bz: &mut DensePolynomialPqx<S>,
    evals_Cz: &mut DensePolynomialPqx<S>,
    transcript: &mut Transcript,
  ) -> (SumcheckInstanceProof<S>, Vec<S>, Vec<S>) {
    let comb_func = |poly_A_comp: &S, poly_B_comp: &S, poly_C_comp: &S, poly_D_comp: &S| -> S {
      *poly_A_comp * (*poly_B_comp * *poly_C_comp - *poly_D_comp)
    };

    let (sc_proof_phase_one, r, claims) =
      SumcheckInstanceProof::<S>::prove_cubic_with_additive_term_disjoint_rounds(
        &S::field_zero(), // claim is zero
        num_rounds,
        num_rounds_x_max,
        num_rounds_q_max,
        num_rounds_p,
        num_proofs.clone(),
        num_cons.clone(),
        evals_tau_p,
        evals_tau_q,
        evals_tau_x,
        evals_Az,
        evals_Bz,
        evals_Cz,
        comb_func,
        transcript,
      );

    (sc_proof_phase_one, r, claims)
  }

  fn prove_phase_two(
    num_rounds: usize,
    num_rounds_y_max: usize,
    num_rounds_w: usize,
    num_rounds_p: usize,
    single_inst: bool,
    num_witness_secs: usize,
    num_inputs: Vec<Vec<usize>>,
    claim: &S,
    evals_eq: &mut DensePolynomial<S>,
    evals_ABC: &mut DensePolynomialPqx<S>,
    evals_z: &mut DensePolynomialPqx<S>,
    transcript: &mut Transcript,
  ) -> (SumcheckInstanceProof<S>, Vec<S>, Vec<S>) {
    let comb_func = |poly_A_comp: &S, poly_B_comp: &S, poly_C_comp: &S| -> S {
      *poly_A_comp * *poly_B_comp * *poly_C_comp
    };
    let (sc_proof_phase_two, r, claims) = SumcheckInstanceProof::<S>::prove_cubic_disjoint_rounds(
      claim,
      num_rounds,
      num_rounds_y_max,
      num_rounds_w,
      num_rounds_p,
      single_inst,
      num_witness_secs,
      num_inputs,
      evals_eq,
      evals_ABC,
      evals_z,
      comb_func,
      transcript,
    );

    (sc_proof_phase_two, r, claims)
  }

  fn protocol_name() -> &'static [u8] {
    b"R1CS proof"
  }

  // A generic R1CS prover that enables data-parallelism on instances
  pub fn prove(
    num_instances: usize,
    max_num_proofs: usize,
    num_proofs: &Vec<usize>,
    // Number of inputs of the combined Z matrix
    max_num_inputs: usize,
    // WITNESS_SECS
    // How many sections does each Z vector have?
    // num_witness_secs can be between 1 - 8
    // if num_witness_secs is not a power of 2, the remaining secs are simply 0's
    // For each witness sec, record the following:
    // IS_SINGLE: does it have just one copy across all blocks?
    // IS_SHORT: does it have only one copy per block? A single witness sect must also be short
    // NUM_INPUTS: number of inputs per block
    // W_MAT: num_instances x num_proofs x num_inputs hypermatrix for all values
    // POLY_W: one dense polynomial per instance
    witness_secs: Vec<&ProverWitnessSecInfo<S>>,
    // INSTANCES
    inst: &R1CSInstance<S>,
    transcript: &mut Transcript,
  ) -> (R1CSProof<S>, [Vec<S>; 4]) {
    let ZERO = S::field_zero();
    let ONE = S::field_one();

    let timer_prove = Timer::new("R1CSProof::prove");
    <Transcript as ProofTranscript<S>>::append_protocol_name(
      transcript,
      R1CSProof::<S>::protocol_name(),
    );

    let num_witness_secs = witness_secs.len();

    // Assert everything is a power of 2, except num_instances
    assert_eq!(max_num_proofs, max_num_proofs.next_power_of_two());
    for p in num_proofs {
      assert_eq!(*p, p.next_power_of_two());
      assert!(*p <= max_num_proofs);
    }
    // Construct num_inputs as P x W
    // Note: w.num_inputs[p_w] might exceed max_num_inputs, but only the first max_num_inputs entries are used
    let mut num_inputs: Vec<Vec<usize>> = (0..num_instances).map(|p| witness_secs.iter().map(|w| {
      let p_w = if w.num_inputs.len() == 1 { 0 } else { p };
      min(w.num_inputs[p_w], max_num_inputs)
    }).collect()).collect();
    // Number of inputs must be in decreasing order between witness segments
    for p in 0..num_instances {
      for w in (1..witness_secs.len()).rev() {
        if num_inputs[p][w - 1] < num_inputs[p][w] {
          num_inputs[p][w - 1] = num_inputs[p][w]
        }
      }
    }
    // Number of instances is either one or matches num_instances
    assert!(inst.get_num_instances() == 1 || inst.get_num_instances() == num_instances);

    // Assert num_witness_secs is valid
    assert!((1..=16).contains(&num_witness_secs));
    for w in &witness_secs {
      // assert size of w_mat
      assert!(w.w_mat.len() == 1 || w.w_mat.len() == num_instances);
      for p in 0..w.w_mat.len() {
        assert!(w.w_mat[p].len() == 1 || w.w_mat[p].len() == num_proofs[p]);
        for q in 0..w.w_mat[p].len() {
          assert_eq!(w.w_mat[p][q].len(), w.num_inputs[p]);
        }
      }
    }

    // --
    // PHASE 1
    // --
    let num_cons = inst.get_num_cons();
    let block_num_cons = if inst.get_num_instances() == 1 {
      vec![inst.get_inst_num_cons()[0]; num_instances]
    } else {
      inst.get_inst_num_cons().clone()
    };
    let timer_sc_proof_phase1 = Timer::new("prove_sc_phase_one");

    // append input to variables to create a single vector z
    let timer_tmp = Timer::new("prove_z_mat_gen");
    
    let z_mat = (0..num_instances).map(|p| {
      (0..num_proofs[p]).into_par_iter().map(|q| {
        (0..witness_secs.len()).map(|w| {
          let ws = witness_secs[w];
          let p_w = if ws.w_mat.len() == 1 { 0 } else { p };
          let q_w = if ws.w_mat[p_w].len() == 1 { 0 } else { q };

          let r_w = if ws.num_inputs[p_w] < num_inputs[p][w] {
            let padding = std::iter::repeat(S::field_zero()).take(num_inputs[p][w] - ws.num_inputs[p_w]).collect::<Vec<S>>();
            let mut r = ws.w_mat[p_w][q_w].clone();
            r.extend(padding);
            r
          } else {
            ws.w_mat[p_w][q_w].iter().take(num_inputs[p][w]).cloned().collect::<Vec<S>>()
          };
          r_w
        }).collect::<Vec<Vec<S>>>()
      }).collect::<Vec<Vec<Vec<S>>>>()
    }).collect::<Vec<Vec<Vec<Vec<S>>>>>();
    timer_tmp.stop();

    // derive the verifier's challenge \tau
    let timer_tmp = Timer::new("prove_vec_mult");
    let (num_rounds_p, num_rounds_q, num_rounds_x, num_rounds_w, num_rounds_y) = (
      num_instances.next_power_of_two().log_2(),
      max_num_proofs.log_2(),
      num_cons.log_2(),
      num_witness_secs.log_2(),
      max_num_inputs.log_2(),
    );

    /*
    let tau_p: Vec<S> = transcript.challenge_vector(b"challenge_tau_p", num_rounds_p);
    let tau_q: Vec<S> = transcript.challenge_vector(b"challenge_tau_q", num_rounds_q);
    let tau_x: Vec<S> = transcript.challenge_vector(b"challenge_tau_x", num_rounds_x);

    // compute the initial evaluation table for R(\tau, x)
    let mut poly_tau_p = DensePolynomial::new(EqPolynomial::new(tau_p).evals());
    let mut poly_tau_q = DensePolynomial::new(EqPolynomial::new(tau_q).evals());
    let mut poly_tau_x = DensePolynomial::new(EqPolynomial::new(tau_x).evals());
    */
    let tau: Vec<S> = transcript.challenge_vector(b"challenge_tau", num_rounds_p + num_rounds_q + num_rounds_x);
    let poly_tau = DensePolynomial::new(EqPolynomial::new(tau).evals());
    let (poly_Az, poly_Bz, poly_Cz) = inst.multiply_vec_block(
      num_instances,
      num_proofs.clone(),
      max_num_proofs,
      max_num_inputs,
      num_cons,
      block_num_cons.clone(),
      &z_mat,
    );
    timer_tmp.stop();

    // == test: ceno_verifier_bench ==
    let A = poly_tau;
    let B = poly_Az.to_dense_poly();
    let C = poly_Bz.to_dense_poly();
    let D = poly_Cz.to_dense_poly();

    println!(
      "=> poly_A,B,C,D num_variables: {:?}, {:?}, {:?}, {:?}",
      A.get_num_vars(),
      B.get_num_vars(),
      C.get_num_vars(),
      D.get_num_vars(),
    );

    let arc_A: ArcMultilinearExtension<'a, GoldilocksExt2>  = Arc::new(
      A.Z.iter().cloned().map(|s| 
        GoldilocksExt2::from_raw_bytes_unchecked(&s.inner().to_raw_bytes())
      )
      .collect::<Vec<GoldilocksExt2>>()
      .into_mle()
    );

    let arc_B: ArcMultilinearExtension<'a, GoldilocksExt2> = Arc::new(
      B.Z.iter().cloned().map(|s| 
        GoldilocksExt2::from_raw_bytes_unchecked(&s.inner().to_raw_bytes())
      )
      .collect::<Vec<GoldilocksExt2>>()
      .into_mle()
    );

    let arc_C: ArcMultilinearExtension<'a, GoldilocksExt2> = Arc::new(
      C.Z.iter().cloned().map(|s| 
        GoldilocksExt2::from_raw_bytes_unchecked(&s.inner().to_raw_bytes())
      )
      .collect::<Vec<GoldilocksExt2>>()
      .into_mle()
    );

    let arc_D: ArcMultilinearExtension<'a, GoldilocksExt2> = Arc::new(
      D.Z.iter().cloned().map(|s| 
        GoldilocksExt2::from_raw_bytes_unchecked(&s.inner().to_raw_bytes())
      )
      .collect::<Vec<GoldilocksExt2>>()
      .into_mle()
    );

    let max_num_vars = A.get_num_vars();
    let num_threads = 32;

    let mut virtual_polys =
        VirtualPolynomials::new(num_threads, max_num_vars);

    virtual_polys.add_mle_list(vec![&arc_A, &arc_B, &arc_C], GoldilocksExt2::ONE);
    virtual_polys.add_mle_list(vec![&arc_A, &arc_D], GoldilocksExt2::ZERO - GoldilocksExt2::ONE);

    let mut ceno_transcript = BasicTranscript::new(b"test");

    let timer_tmp = Timer::new("=> prove_sum_check with ceno (phase 1): IOPProverStateV2::prove_batch_polys");
    let (sc_proof_phase1_proof, sc_proof_phase1_state): (
      IOPProof<GoldilocksExt2>,
      IOPProverStateV2<GoldilocksExt2>
    ) = IOPProverStateV2::prove_batch_polys(
      num_threads,
      virtual_polys.get_batched_polys(),
      &mut ceno_transcript,
    );
    timer_tmp.stop();
    let sc_proof_phase1_state_evals = sc_proof_phase1_state.get_mle_final_evaluations();
    let (tau_claim, Az_claim, Bz_claim, Cz_claim): (GoldilocksExt2, GoldilocksExt2, GoldilocksExt2, GoldilocksExt2) = (
      sc_proof_phase1_state_evals[0],
      sc_proof_phase1_state_evals[1],
      sc_proof_phase1_state_evals[2],
      sc_proof_phase1_state_evals[3],
    );

    let _tau_claim: S = S::InnerType::from_raw_bytes(&tau_claim.to_raw_bytes()).unwrap().into();
    let Az_claim: S = S::InnerType::from_raw_bytes(&Az_claim.to_raw_bytes()).unwrap().into();
    let Bz_claim: S = S::InnerType::from_raw_bytes(&Bz_claim.to_raw_bytes()).unwrap().into();
    let Cz_claim: S = S::InnerType::from_raw_bytes(&Cz_claim.to_raw_bytes()).unwrap().into();
    
    let rx: Vec<S> = 
      sc_proof_phase1_proof.point.iter().map(|c| 
        S::InnerType::from_raw_bytes(&c.to_raw_bytes()).unwrap().into()
      ).rev().collect::<Vec<S>>();
    timer_sc_proof_phase1.stop();
    // == test: ceno_verifier_bench ==

    let fn_eval = |fs: &[ArcMultilinearExtension<GoldilocksExt2>; 4]| -> GoldilocksExt2 {
      let mut evals = vec![GoldilocksExt2::ZERO; 1 << fs[0].num_vars()];
      let A = fs[0].get_ext_field_vec();
      let B = fs[1].get_ext_field_vec();
      let C = fs[2].get_ext_field_vec();
      let D = fs[3].get_ext_field_vec();

      for ((((e, a), b), c), d) in evals.iter_mut().zip(A).zip(B).zip(C).zip(D) {
        *e += *a * b * c - *a * d;
      }
      
      evals.iter().sum::<GoldilocksExt2>()
    };
    let claim_phase1 = fn_eval(&[arc_A.clone(), arc_B.clone(), arc_C.clone(), arc_D.clone()]);

    /*
    // Sumcheck 1: (Az * Bz - Cz) * eq(x, q, p) = 0
    let timer_tmp = Timer::new("prove_sum_check");
    let (sc_proof_phase1, rx_rev, _claims_phase1) = R1CSProof::prove_phase_one(
      num_rounds_x + num_rounds_q + num_rounds_p,
      num_rounds_x,
      num_rounds_q,
      num_rounds_p,
      num_proofs,
      &block_num_cons,
      &mut poly_tau_p,
      &mut poly_tau_q,
      &mut poly_tau_x,
      &mut poly_Az,
      &mut poly_Bz,
      &mut poly_Cz,
      transcript,
    );

    assert_eq!(poly_tau_p.len(), 1);
    assert_eq!(poly_tau_q.len(), 1);
    assert_eq!(poly_tau_x.len(), 1);
    assert_eq!(poly_Az.len(), 1);
    assert_eq!(poly_Bz.len(), 1);
    assert_eq!(poly_Cz.len(), 1);
    timer_tmp.stop();

    let (_tau_claim, Az_claim, Bz_claim, Cz_claim) = (
      &(poly_tau_p[0] * poly_tau_q[0] * poly_tau_x[0]),
      &poly_Az.index(0, 0, 0, 0),
      &poly_Bz.index(0, 0, 0, 0),
      &poly_Cz.index(0, 0, 0, 0),
    );

    S::append_field_to_transcript(b"Az_claim", transcript, *Az_claim);
    S::append_field_to_transcript(b"Bz_claim", transcript, *Bz_claim);
    S::append_field_to_transcript(b"Cz_claim", transcript, *Cz_claim);

    // Separate the result rx into rp, rq, and rx
    let (rx_rev, rq_rev) = rx_rev.split_at(num_rounds_x);
    let (rq_rev, rp_rev) = rq_rev.split_at(num_rounds_q);
    let rx: Vec<S> = rx_rev.iter().copied().rev().collect();
    let rq: Vec<S> = rq_rev.iter().copied().rev().collect();
    let rp = rp.to_vec();
    */

    S::append_field_to_transcript(b"Az_claim", transcript, Az_claim);
    S::append_field_to_transcript(b"Bz_claim", transcript, Bz_claim);
    S::append_field_to_transcript(b"Cz_claim", transcript, Cz_claim);

    // Separate the result rx into rp, rq, and rx
    let (rp, rq) = rx.split_at(num_rounds_p);
    let (rq, rx) = rq.split_at(num_rounds_q);
    let rq = rq.to_vec();
    let rq_rev: Vec<S> = rq.iter().copied().rev().collect();
    let rp = rp.to_vec();

    // --
    // PHASE 2
    // --
    let timer_sc_proof_phase2 = Timer::new("prove_sc_phase_two");
    // combine the three claims into a single claim
    let r_A: S = transcript.challenge_scalar(b"challenge_Az");
    let r_B: S = transcript.challenge_scalar(b"challenge_Bz");
    let r_C: S = transcript.challenge_scalar(b"challenge_Cz");
    let claim_phase2 = GoldilocksExt2::from_raw_bytes(&(r_A * Az_claim + r_B * Bz_claim + r_C * Cz_claim).inner().to_raw_bytes()).unwrap();

    let timer_tmp = Timer::new("prove_abc_gen");
    let evals_ABC = {
      // compute the initial evaluation table for R(\tau, x)
      let evals_rx = EqPolynomial::new(rx.to_vec()).evals();
      let (evals_A, evals_B, evals_C) = inst.compute_eval_table_sparse_disjoint_rounds(
        num_instances,
        inst.get_inst_num_cons(),
        num_witness_secs,
        max_num_inputs,
        &num_inputs,
        &evals_rx,
      );

      let mut evals_ABC = Vec::new();
      for p in 0..inst.get_num_instances() {
        evals_ABC.push(vec![Vec::new()]);
        for w in 0..num_witness_secs {
          evals_ABC[p][0].push(Vec::new());
          // If single instance, need to find the maximum num_inputs
          let num_inputs = if inst.get_num_instances() == 1 { 
            num_inputs.iter().map(|n| n[w]).max().unwrap()
          } else { num_inputs[p][w] };
          for i in 0..num_inputs {
            evals_ABC[p][0][w].push(
              r_A * evals_A[p][0][w][i] + r_B * evals_B[p][0][w][i] + r_C * evals_C[p][0][w][i],
            );
          }
        }
      }
      evals_ABC
    };
    let ABC_poly = DensePolynomialPqx::new_rev(
      &evals_ABC,
      vec![1; num_instances],
      1,
      num_inputs.clone(),
      max_num_inputs,
    );
    timer_tmp.stop();

    let timer_tmp = Timer::new("prove_z_gen");
    // Construct a p * q * len(z) matrix Z and bound it to r_q
    let mut Z_poly = DensePolynomialPqx::new(z_mat);
    timer_tmp.stop();
    let timer_tmp = Timer::new("prove_z_bind");
    Z_poly.bound_poly_vars_rq_parallel(&rq_rev);
    timer_tmp.stop();

    // == test ceno_verifier_bench
    let ABC_poly = ABC_poly.to_dense_poly();
    let Z_poly = Z_poly.to_dense_poly();

    // An Eq function to match p with rp
    let max_num_vars_phase2 = ABC_poly.get_num_vars();
    // rp.extend(std::iter::repeat(S::field_one()).take(max_num_vars_phase2 - rp.len()));
    // let rp = rp.into_iter().rev().collect();
    let tmp_rp_poly = EqPolynomial::new(rp).evals();
    // Every entry of tmp_rp_poly needs to be repeated "scale" times
    let scale = ABC_poly.len() / tmp_rp_poly.len();
    let eq_p_rp_poly = DensePolynomial::new(
      tmp_rp_poly.into_iter().map(|i| vec![i; scale]).collect::<Vec<Vec<S>>>().concat()
    );

    let mut claimed_sum = S::field_zero();
    let mut claimed_partial_sum = S::field_zero();
    let mut a_sum = S::field_zero();
    let mut b_sum = S::field_zero();
    let mut c_sum = S::field_zero();
    for (a, (b, c)) in zip(&eq_p_rp_poly.Z, zip(&ABC_poly.Z, &Z_poly.Z)) {
      claimed_sum += a.clone() * b.clone() * c.clone();
      claimed_partial_sum += b.clone() * c.clone();
      a_sum += a.clone();
      b_sum += b.clone();
      c_sum += c.clone();
    }

    println!(
      "=> ABC_poly, Z_poly, eq_p_rp_poly num_variables: {:?}, {:?}, {:?}",
      ABC_poly.get_num_vars(),
      Z_poly.get_num_vars(),
      eq_p_rp_poly.get_num_vars(),
    );

    let arc_A: ArcMultilinearExtension<'a, GoldilocksExt2>  = Arc::new(
      ABC_poly.Z.iter().cloned().map(|s| 
        GoldilocksExt2::from_raw_bytes_unchecked(&s.inner().to_raw_bytes())
      )
      .collect::<Vec<GoldilocksExt2>>()
      .into_mle()
    );

    let arc_B: ArcMultilinearExtension<'a, GoldilocksExt2> = Arc::new(
      Z_poly.Z.iter().cloned().map(|s| 
        GoldilocksExt2::from_raw_bytes_unchecked(&s.inner().to_raw_bytes())
      )
      .collect::<Vec<GoldilocksExt2>>()
      .into_mle()
    );

    let arc_C: ArcMultilinearExtension<'a, GoldilocksExt2> = Arc::new(
      eq_p_rp_poly.Z.iter().clone().map(|s| 
        GoldilocksExt2::from_raw_bytes_unchecked(&s.inner().to_raw_bytes())
      )
      .collect::<Vec<GoldilocksExt2>>()
      .into_mle()
    );
    
    let num_threads_phase2 = 32;

    let mut virtual_polys =
        VirtualPolynomials::new(num_threads_phase2, max_num_vars_phase2);

    virtual_polys.add_mle_list(vec![&arc_A, &arc_B, &arc_C], GoldilocksExt2::ONE);

    let mut ceno_transcript = BasicTranscript::new(b"test");

    let timer_tmp = Timer::new("=> prove_sum_check with ceno (phase 2): IOPProverStateV2::prove_batch_polys");
    let (sc_proof_phase2_proof, _sc_proof_phase2_state): (
      IOPProof<GoldilocksExt2>,
      IOPProverStateV2<GoldilocksExt2>
    ) = IOPProverStateV2::prove_batch_polys(
      num_threads,
      virtual_polys.get_batched_polys(),
      &mut ceno_transcript,
    );
    timer_tmp.stop();

    let ry: Vec<S> = 
      sc_proof_phase2_proof.point.iter().map(|c| 
        S::InnerType::from_raw_bytes(&c.to_raw_bytes()).unwrap().into()
      ).rev().collect::<Vec<S>>();
    // == test ceno_verifier_bench

    /*
    // Sumcheck 2: (rA + rB + rC) * Z * eq(p) = e
    let timer_tmp = Timer::new("prove_sum_check");
    let (sc_proof_phase2, ry_rev, _claims_phase2) = R1CSProof::prove_phase_two(
      num_rounds_y + num_rounds_w + num_rounds_p,
      num_rounds_y,
      num_rounds_w,
      num_rounds_p,
      inst.get_num_instances() == 1,
      num_witness_secs,
      num_inputs.clone(),
      &claim_phase2,
      &mut eq_p_rp_poly,
      &mut ABC_poly,
      &mut Z_poly,
      transcript,
    );
    */
    timer_sc_proof_phase2.stop();

    // Separate ry into rp, rw, and ry
    /*
    let (ry_rev, rw) = ry.split_at(num_rounds_y);
    let (rw, rp) = rw.split_at(num_rounds_w);
    let rp = rp.to_vec();
    let rw = rw.to_vec();
    let ry: Vec<S> = ry_rev.iter().copied().rev().collect();
    */
    let (rp, ry) = ry.split_at(num_rounds_p);
    let (rw, ry) = ry.split_at(num_rounds_w);
    let rp = rp.to_vec();
    let rw = rw.to_vec();
    let ry = ry.to_vec();

    // --
    // POLY COMMIT
    // --
    // Commit each witness by instance
    let timer_polyeval = Timer::new("polyeval");

    // For every possible wit_sec.num_inputs, compute ry_factor = prodX(1 - ryX)...
    let mut ry_factors = vec![ONE; num_rounds_y + 1];
    for i in 0..num_rounds_y {
      ry_factors[i + 1] = ry_factors[i] * (ONE - ry[i]);
    }

    let mut poly_list = Vec::new();
    let mut num_proofs_list = Vec::new();
    let mut num_inputs_list = Vec::new();
    // List of all evaluations
    let mut Zr_list = Vec::new();
    // List of evaluations separated by witness_secs
    let mut eval_vars_at_ry_list = vec![Vec::new(); num_witness_secs];
    let mut raw_eval_vars_at_ry_list = vec![Vec::new(); num_witness_secs]; // Does not multiply ry_factor
    for i in 0..num_witness_secs {
      let w = witness_secs[i];
      let wit_sec_num_instance = w.w_mat.len();
      eval_vars_at_ry_list.push(Vec::new());

      for p in 0..wit_sec_num_instance {
        if w.num_inputs[p] > 1 {
          poly_list.push(&w.poly_w[p]);
          num_proofs_list.push(w.w_mat[p].len());
          num_inputs_list.push(w.num_inputs[p]);
          // Depending on w.num_inputs[p], ry_short can be two different values
          let ry_short = {
            // if w.num_inputs[p] >= num_inputs, need to pad 0's to the front of ry
            if w.num_inputs[p] >= max_num_inputs {
              let ry_pad = vec![ZERO; w.num_inputs[p].log_2() - max_num_inputs.log_2()];
              [ry_pad, ry.clone()].concat()
            }
            // Else ry_short is the last w.num_inputs[p].log_2() entries of ry
            // thus, to obtain the actual ry, need to multiply by (1 - ry0)(1 - ry1)..., which is ry_factors[num_rounds_y - w.num_inputs[p]]
            else {
              ry[num_rounds_y - w.num_inputs[p].log_2()..].to_vec()
            }
          };
          let rq_short = rq[num_rounds_q - num_proofs_list[num_proofs_list.len() - 1].log_2()..].to_vec();
          let r = &[rq_short, ry_short.clone()].concat();
          let eval_vars_at_ry = poly_list[poly_list.len() - 1].evaluate(r);
          Zr_list.push(eval_vars_at_ry);
          if w.num_inputs[p] >= max_num_inputs {
            eval_vars_at_ry_list[i].push(eval_vars_at_ry);
          } else {
            eval_vars_at_ry_list[i].push(eval_vars_at_ry * ry_factors[num_rounds_y - w.num_inputs[p].log_2()]);
          }
          raw_eval_vars_at_ry_list[i].push(eval_vars_at_ry);
        } else {
          eval_vars_at_ry_list[i].push(ZERO);
          raw_eval_vars_at_ry_list[i].push(ZERO);
        }
      }
    }

    /*
    let proof_eval_vars_at_ry_list = PolyEvalProof::prove_batched_instances_disjoint_rounds(
      &poly_list,
      &num_proofs_list,
      &num_inputs_list,
      &rq,
      &ry,
      &Zr_list,
      transcript,
      random_tape,
    );
    */

    // Bind the resulting witness list to rp
    // poly_vars stores the result of each witness matrix bounded to (rq_short ++ ry)
    // but we want to bound them to (rq ++ ry)
    // So we need to multiply each entry by (1 - rq0)(1 - rq1)
    let mut eval_vars_comb_list = Vec::new();
    for p in 0..num_instances {
      let wit_sec_p = |i: usize| {
        if witness_secs[i].w_mat.len() == 1 {
          0
        } else {
          p
        }
      };
      let e = |i: usize| eval_vars_at_ry_list[i][wit_sec_p(i)];
      let prefix_list = match num_witness_secs.next_power_of_two() {
        1 => {
          vec![ONE]
        }
        2 => {
          vec![(ONE - rw[0]), rw[0]]
        }
        4 => {
          vec![
            (ONE - rw[0]) * (ONE - rw[1]),
            (ONE - rw[0]) * rw[1],
            rw[0] * (ONE - rw[1]),
            rw[0] * rw[1],
          ]
        }
        8 => {
          vec![
            (ONE - rw[0]) * (ONE - rw[1]) * (ONE - rw[2]),
            (ONE - rw[0]) * (ONE - rw[1]) * rw[2],
            (ONE - rw[0]) * rw[1] * (ONE - rw[2]),
            (ONE - rw[0]) * rw[1] * rw[2],
            rw[0] * (ONE - rw[1]) * (ONE - rw[2]),
            rw[0] * (ONE - rw[1]) * rw[2],
            rw[0] * rw[1] * (ONE - rw[2]),
            rw[0] * rw[1] * rw[2],
          ]
        }
        _ => {
          panic!("Unsupported num_witness_secs: {}", num_witness_secs);
        }
      };
      let mut eval_vars_comb =
        (0..num_witness_secs).fold(ZERO, |s, i| s + prefix_list[i] * e(i));
      for q in 0..(num_rounds_q - num_proofs[p].log_2()) {
        eval_vars_comb = eval_vars_comb * (ONE - rq[q]);
      }
      eval_vars_comb_list.push(eval_vars_comb);
    }
    timer_polyeval.stop();

    let poly_vars = DensePolynomial::new(eval_vars_comb_list);
    let eval_vars_at_ry = poly_vars.evaluate(&rp);

    timer_prove.stop();

    (
      R1CSProof {
        sc_proof_phase1_proof,
        // sc_proof_phase1,
        sc_proof_phase2_proof,
        claims_phase2: (Az_claim, Bz_claim, Cz_claim),
        eval_vars_at_ry_list: raw_eval_vars_at_ry_list,
        eval_vars_at_ry,
        // proof_eval_vars_at_ry_list,
        max_num_vars,
        claim_phase1,
        max_num_vars_phase2,
        claim_phase2,
      },
      [rp, rq_rev, rx.to_vec(), [rw, ry].concat()],
    )
  }

  pub fn verify(
    &self,
    num_instances: usize,
    max_num_proofs: usize,
    num_proofs: &Vec<usize>,
    max_num_inputs: usize,

    // NUM_WITNESS_SECS
    // How many sections does each Z vector have?
    // num_witness_secs can be between 1 - 8
    // if num_witness_secs is not a power of 2, the remaining secs are simply 0's
    // For each witness sec, record the following:
    // IS_SINGLE: does it have just one copy across all blocks?
    // IS_SHORT: does it have only one copy per block? A single witness sect must also be short
    // NUM_INPUTS: number of inputs per block
    // W_MAT: num_instances x num_proofs x num_inputs hypermatrix for all values
    // COMM_W: one commitment per instance
    witness_secs: Vec<&VerifierWitnessSecInfo>,

    num_cons: usize,
    evals: &[S; 3],
    transcript: &mut Transcript,
  ) -> Result<[Vec<S>; 4], ProofVerifyError> {
    let ZERO = S::field_zero();
    let ONE = S::field_one();

    <Transcript as ProofTranscript<S>>::append_protocol_name(
      transcript,
      R1CSProof::<S>::protocol_name(),
    );

    let num_witness_secs = witness_secs.len();

    // Assert num_witness_secs is valid
    assert!((1..=16).contains(&num_witness_secs));

    let (num_rounds_p, num_rounds_q, num_rounds_x, num_rounds_w, num_rounds_y) = (
      num_instances.next_power_of_two().log_2(),
      max_num_proofs.log_2(),
      num_cons.log_2(),
      num_witness_secs.log_2(),
      max_num_inputs.log_2(),
    );

    // derive the verifier's challenge tau
    /*
    let tau_p: Vec<S> = transcript.challenge_vector(b"challenge_tau_p", num_rounds_p);
    let tau_q: Vec<S> = transcript.challenge_vector(b"challenge_tau_q", num_rounds_q);
    let tau_x: Vec<S> = transcript.challenge_vector(b"challenge_tau_x", num_rounds_x);
    */
    let tau: Vec<S> = transcript.challenge_vector(b"challenge_tau", num_rounds_p + num_rounds_q + num_rounds_x);

    // == test: ceno_verifier_bench ==
    let mut ceno_transcript = BasicTranscript::new(b"test");
    let subclaim = IOPVerifierState::<GoldilocksExt2>::verify(
        self.claim_phase1,
        &self.sc_proof_phase1_proof,
        &VPAuxInfo {
            max_degree: 3,
            num_variables: self.max_num_vars,
            phantom: std::marker::PhantomData,
        },
        &mut ceno_transcript,
    );
    let rx: Vec<S> = 
      subclaim.point.iter().map(|c| 
        S::InnerType::from_raw_bytes(&c.elements.to_raw_bytes()).unwrap().into()
      ).rev().collect::<Vec<S>>();
    let claim_post_phase_1 = S::InnerType::from_raw_bytes(&subclaim.expected_evaluation.to_raw_bytes()).unwrap().into();
    // == test: ceno_verifier_bench ==

    /*
    // let (claim_post_phase_1, rx) = self.sc_proof_phase1.verify(
    //   S::field_zero(),
    //   num_rounds_x + num_rounds_q + num_rounds_p,
    //   3,
    //   transcript,
    // )?;

    // taus_bound_rx is really taus_bound_rx_rq_rp
    let taus_bound_rp: S = (0..rp_round1.len())
      .map(|i| rp_round1[i] * tau_p[i] + (ONE - rp_round1[i]) * (ONE - tau_p[i]))
      .product();
    let taus_bound_rq: S = (0..rq.len())
      .map(|i| rq[i] * tau_q[i] + (ONE - rq[i]) * (ONE - tau_q[i]))
      .product();
    let taus_bound_rx: S = (0..rx.len())
      .map(|i| rx[i] * tau_x[i] + (ONE - rx[i]) * (ONE - tau_x[i]))
      .product();
    let taus_bound_rx = taus_bound_rp * taus_bound_rq * taus_bound_rx;
    */
    let taus_bound_rx: S = (0..num_rounds_p + num_rounds_q + num_rounds_x)
    .map(|i| {
      rx[i] * tau[i] + (S::field_one() - rx[i]) * (S::field_one() - tau[i])
    })
    .product();

    // Separate the result rx into rp_round1, rq, and rx
    let (rp_round1, rq) = rx.split_at(num_rounds_p);
    let (rq, rx) = rq.split_at(num_rounds_q);
    let rx = rx.to_vec();
    let rq = rq.to_vec();
    let rq_rev: Vec<S> = rq.iter().copied().rev().collect();
    let rp_round1 = rp_round1.to_vec();

    // perform the intermediate sum-check test with claimed Az, Bz, and Cz
    let (Az_claim, Bz_claim, Cz_claim) = self.claims_phase2;
    S::append_field_to_transcript(b"Az_claim", transcript, Az_claim);
    S::append_field_to_transcript(b"Bz_claim", transcript, Bz_claim);
    S::append_field_to_transcript(b"Cz_claim", transcript, Cz_claim);
    assert_eq!(taus_bound_rx * (Az_claim * Bz_claim - Cz_claim), claim_post_phase_1);

    // derive three public challenges and then derive a joint claim
    let r_A: S = transcript.challenge_scalar(b"challenge_Az");
    let r_B: S = transcript.challenge_scalar(b"challenge_Bz");
    let r_C: S = transcript.challenge_scalar(b"challenge_Cz");
    let claim_phase2 = GoldilocksExt2::from_raw_bytes(&(r_A * Az_claim + r_B * Bz_claim + r_C * Cz_claim).inner().to_raw_bytes()).unwrap();

    // == test: ceno_verifier_bench ==
    let mut ceno_transcript = BasicTranscript::new(b"test");
    let subclaim = IOPVerifierState::<GoldilocksExt2>::verify(
        claim_phase2,
        &self.sc_proof_phase2_proof,
        &VPAuxInfo {
            max_degree: 3,
            num_variables: self.max_num_vars_phase2,
            phantom: std::marker::PhantomData,
        },
        &mut ceno_transcript,
    );
    let ry: Vec<S> = 
      subclaim.point.iter().map(|c| 
        S::InnerType::from_raw_bytes(&c.elements.to_raw_bytes()).unwrap().into()
      ).rev().collect::<Vec<S>>();
    let claim_post_phase_2: S = S::InnerType::from_raw_bytes(&subclaim.expected_evaluation.to_raw_bytes()).unwrap().into();
    // == test: ceno_verifier_bench ==

    /*
    // verify the joint claim with a sum-check protocol
    let (claim_post_phase_2, ry_rev) = self.sc_proof_phase2.verify(
      claim_phase2,
      num_rounds_y + num_rounds_w + num_rounds_p,
      3,
      transcript,
    )?;

    // Separate ry into rp, rw, and ry
    let (ry_rev, rw_rev) = ry_rev.split_at(num_rounds_y);
    let (rw_rev, rp_rev) = rw_rev.split_at(num_rounds_w);
    let rp: Vec<S> = rp_rev.iter().copied().rev().collect();
    let rw: Vec<S> = rw_rev.iter().copied().rev().collect();
    let ry: Vec<S> = ry_rev.iter().copied().rev().collect();
    */

    // Separate ry into rp, rw, and ry
    let (rp, ry) = ry.split_at(num_rounds_p);
    let (rw, ry) = ry.split_at(num_rounds_w);
    let rp = rp.to_vec();
    let rw = rw.to_vec();
    let ry: Vec<S> = ry_rev.iter().copied().rev().collect();
    */

    // Separate ry into rp, rw, and ry
    let (rp, ry) = ry.split_at(num_rounds_p);
    let (rw, ry) = ry.split_at(num_rounds_w);
    let rp = rp.to_vec();
    let rw = rw.to_vec();
    let ry = ry.to_vec();

    // An Eq function to match p with rp
    let p_rp_poly_bound_ry: S = (0..rp.len())
      .map(|i| rp[i] * rp_round1[i] + (ONE - rp[i]) * (ONE - rp_round1[i]))
      .product();

    // verify Z(rp, rq, ry) proof against the initial commitment
    // First by witness & by instance on ry
    // For every possible wit_sec.num_inputs, compute ry_factor = prodX(1 - ryX)...
    // If there are 2 witness secs, then ry_factors[0] = 1, ry_factors[1] = 1, ry_factors[2] = 1 - ry1, ry_factors[3] = (1 - ry1)(1 - ry2), etc.
    let mut ry_factors = vec![ONE; num_rounds_y + 1];
    for i in 0..num_rounds_y {
      ry_factors[i + 1] = (ry_factors[i]) * (ONE - ry[i]);
    }

    // POLY COMMIT
    let timer_commit_opening = Timer::new("verify_sc_commitment_opening");
    let mut num_proofs_list = Vec::new();
    let mut num_inputs_list = Vec::new();
    let mut eval_Zr_list = Vec::new();
    for i in 0..num_witness_secs {
      let w = witness_secs[i];
      let wit_sec_num_instance = w.num_proofs.len();
      for p in 0..wit_sec_num_instance {
        if w.num_inputs[p] > 1 {
          // comm_list.push(&w.comm_w[p]);
          num_proofs_list.push(w.num_proofs[p]);
          num_inputs_list.push(w.num_inputs[p]);
          eval_Zr_list.push(self.eval_vars_at_ry_list[i][p]);
        } else {
          assert_eq!(self.eval_vars_at_ry_list[i][p], ZERO);
        }
      }
    }

    /*
    PolyEvalProof::verify_batched_instances_disjoint_rounds(
      &self.proof_eval_vars_at_ry_list,
      &num_proofs_list,
      &num_inputs_list,
      transcript,
      &rq,
      &ry,
    )?;
    */

    // Then on rp
    let mut expected_eval_vars_list = Vec::new();
    for p in 0..num_instances {
      let wit_sec_p = |i: usize| {
        if witness_secs[i].num_proofs.len() == 1 {
          0
        } else {
          p
        }
      };
      let c = |i: usize| {
        if witness_secs[i].num_inputs[wit_sec_p(i)] >= max_num_inputs {
          self.eval_vars_at_ry_list[i][wit_sec_p(i)]
        } else {
          self.eval_vars_at_ry_list[i][wit_sec_p(i)]
            * ry_factors[num_rounds_y - witness_secs[i].num_inputs[wit_sec_p(i)].log_2()]
        }
      };
      let prefix_list = match num_witness_secs.next_power_of_two() {
        1 => {
          vec![ONE]
        }
        2 => {
          vec![(ONE - rw[0]), rw[0]]
        }
        4 => {
          vec![
            (ONE - rw[0]) * (ONE - rw[1]),
            (ONE - rw[0]) * rw[1],
            rw[0] * (ONE - rw[1]),
            rw[0] * rw[1],
          ]
        }
        8 => {
          vec![
            (ONE - rw[0]) * (ONE - rw[1]) * (ONE - rw[2]),
            (ONE - rw[0]) * (ONE - rw[1]) * rw[2],
            (ONE - rw[0]) * rw[1] * (ONE - rw[2]),
            (ONE - rw[0]) * rw[1] * rw[2],
            rw[0] * (ONE - rw[1]) * (ONE - rw[2]),
            rw[0] * (ONE - rw[1]) * rw[2],
            rw[0] * rw[1] * (ONE - rw[2]),
            rw[0] * rw[1] * rw[2],
          ]
        }
        _ => {
          panic!("Unsupported num_witness_secs: {}", num_witness_secs);
        }
      };
      let mut eval_vars_comb =
        (1..num_witness_secs).fold(prefix_list[0] * c(0), |s, i| s + prefix_list[i] * c(i));
      for q in 0..(num_rounds_q - num_proofs[p].log_2()) {
        eval_vars_comb *= ONE - rq[q];
      }
      expected_eval_vars_list.push(eval_vars_comb);
    }

    let EQ_p = &EqPolynomial::new(rp.clone()).evals()[..num_instances];
    let expected_eval_vars_at_ry =
      zip(EQ_p, expected_eval_vars_list).fold(ZERO, |s, (a, b)| s + *a * b);

    assert_eq!(expected_eval_vars_at_ry, self.eval_vars_at_ry);

    timer_commit_opening.stop();

    // compute commitment to eval_Z_at_ry = (ONE - ry[0]) * self.eval_vars_at_ry + ry[0] * poly_input_eval
    let eval_Z_at_ry = &self.eval_vars_at_ry;

    // perform the final check in the second sum-check protocol
    let [eval_A_r, eval_B_r, eval_C_r] = evals;
    let expected_claim_post_phase2 =
      (r_A * *eval_A_r + r_B * *eval_B_r + r_C * *eval_C_r) * *eval_Z_at_ry * p_rp_poly_bound_ry;

    // verify proof that expected_claim_post_phase2 == claim_post_phase2
    assert_eq!(claim_post_phase_2, expected_claim_post_phase2);

    Ok([rp, rq, rx, [rw, ry].concat()])
  }
}
