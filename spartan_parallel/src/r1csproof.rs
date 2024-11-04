#![allow(clippy::too_many_arguments)]
use crate::{ProverWitnessSecInfo, VerifierWitnessSecInfo};
use super::dense_mlpoly::{
  DensePolynomial, EqPolynomial, PolyEvalProof,
  /* TODO: Alternative PCS
  PolyCommitmentGens, 
  */
};
use super::custom_dense_mlpoly::DensePolynomialPqx;
use super::errors::ProofVerifyError;
/* TODO: Alternative PCS
use super::commitments::{Commitments, MultiCommitGens};
use super::group::{CompressedGroup, GroupElement, VartimeMultiscalarMul};
*/
use super::nizk::{EqualityProof, KnowledgeProof, ProductProof};
use super::math::Math;
use super::r1csinstance::R1CSInstance;
use super::random::RandomTape;
use super::scalar::Scalar;
use super::sumcheck::ZKSumcheckInstanceProof;
use super::timer::Timer;
use super::transcript::{AppendToTranscript, ProofTranscript};
use core::iter;
use std::cmp::min;
use merlin::Transcript;
use serde::{Deserialize, Serialize};

const ZERO: Scalar = Scalar::zero();
const ONE: Scalar = Scalar::one();

#[derive(Serialize, Deserialize, Debug)]
pub struct R1CSProof {
  sc_proof_phase1: ZKSumcheckInstanceProof,
  sc_proof_phase2: ZKSumcheckInstanceProof,
  pok_claims_phase2: (KnowledgeProof, ProductProof),
  proof_eq_sc_phase1: EqualityProof,
  proof_eq_sc_phase2: EqualityProof,
  /* TODO: Alternative PCS
  sc_proof_phase1: ZKSumcheckInstanceProof,
  claims_phase2: (
    CompressedGroup,
    CompressedGroup,
    CompressedGroup,
    CompressedGroup,
  ),
  pok_claims_phase2: (KnowledgeProof, ProductProof),
  proof_eq_sc_phase1: EqualityProof,
  sc_proof_phase2: ZKSumcheckInstanceProof,
  // Need to commit vars for short and long witnesses separately
  // The long version must exist, the short version might not
  comm_vars_at_ry_list: Vec<Vec<CompressedGroup>>,
  comm_vars_at_ry: CompressedGroup,
  proof_eval_vars_at_ry_list: Vec<PolyEvalProof>,
  proof_eq_sc_phase2: EqualityProof,
  */
}

/* TODO: Alternative PCS
#[derive(Clone, Serialize)]
pub struct R1CSSumcheckGens {
  gens_1: MultiCommitGens,
  gens_3: MultiCommitGens,
  gens_4: MultiCommitGens,
}

// TODO: fix passing gens_1_ref
impl R1CSSumcheckGens {
  pub fn new(label: &'static [u8], gens_1_ref: &MultiCommitGens) -> Self {
    let gens_1 = gens_1_ref.clone();
    let gens_3 = MultiCommitGens::new(3, label);
    let gens_4 = MultiCommitGens::new(4, label);

    R1CSSumcheckGens {
      gens_1,
      gens_3,
      gens_4,
    }
  }
}

#[derive(Clone, Serialize)]
pub struct R1CSGens {
  pub gens_sc: R1CSSumcheckGens,
  pub gens_pc: PolyCommitmentGens,
}

impl R1CSGens {
  pub fn new(label: &'static [u8], _num_cons: usize, num_vars: usize) -> Self {
    let num_poly_vars = num_vars.log_2();
    let gens_pc = PolyCommitmentGens::new(num_poly_vars, label);
    let gens_sc = R1CSSumcheckGens::new(label, &gens_pc.gens.gens_1);
    R1CSGens { gens_sc, gens_pc }
  }
}
*/

impl R1CSProof {
  fn prove_phase_one(
    num_rounds: usize,
    num_rounds_x_max: usize,
    num_rounds_q_max: usize,
    num_rounds_p: usize,
    num_proofs: &Vec<usize>,
    num_cons: &Vec<usize>,
    evals_tau_p: &mut DensePolynomial,
    evals_tau_q: &mut DensePolynomial,
    evals_tau_x: &mut DensePolynomial,
    evals_Az: &mut DensePolynomialPqx,
    evals_Bz: &mut DensePolynomialPqx,
    evals_Cz: &mut DensePolynomialPqx,
    /* TODO: Alternative PCS
    gens: &R1CSSumcheckGens,
    */
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (ZKSumcheckInstanceProof, Vec<Scalar>, Vec<Scalar>, Scalar) {
    let comb_func = |poly_A_comp: &Scalar,
                     poly_B_comp: &Scalar,
                     poly_C_comp: &Scalar,
                     poly_D_comp: &Scalar|
     -> Scalar { poly_A_comp * (poly_B_comp * poly_C_comp - poly_D_comp) };

    let (sc_proof_phase_one, r, claims, blind_claim_postsc) =
      ZKSumcheckInstanceProof::prove_cubic_with_additive_term_disjoint_rounds(
        &ZERO, // claim is zero
        &ZERO, // blind for claim is also zero
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
        /* TODO: Alternative PCS
        &gens.gens_1,
        &gens.gens_4,
        */
        transcript,
        random_tape,
      );

    (sc_proof_phase_one, r, claims, blind_claim_postsc)
  }

  fn prove_phase_two(
    num_rounds: usize,
    num_rounds_y_max: usize,
    num_rounds_w: usize,
    num_rounds_p: usize,
    single_inst: bool,
    num_witness_secs: usize,
    num_inputs: Vec<usize>,
    claim: &Scalar,
    blind_claim: &Scalar,
    evals_eq: &mut DensePolynomial,
    evals_ABC: &mut DensePolynomialPqx,
    evals_z: &mut DensePolynomialPqx,
    /* TODO: Alternative PCS
    gens: &R1CSSumcheckGens,
    */
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (ZKSumcheckInstanceProof, Vec<Scalar>, Vec<Scalar>, Scalar) {
    let comb_func =
      |poly_A_comp: &Scalar, poly_B_comp: &Scalar, poly_C_comp: &Scalar| -> Scalar { poly_A_comp * poly_B_comp * poly_C_comp };
    let (sc_proof_phase_two, r, claims, blind_claim_postsc) = ZKSumcheckInstanceProof::prove_cubic_disjoint_rounds(
      claim,
      blind_claim,
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
      /* TODO: Alternative PCS
      &gens.gens_1,
      &gens.gens_4,
      */
      transcript,
      random_tape,
    );

    (sc_proof_phase_two, r, claims, blind_claim_postsc)
  }

  /*
  fn prove_phase_two_single(
    num_rounds: usize,
    claim: &Scalar,
    blind_claim: &Scalar,
    evals_z: &mut DensePolynomial,
    evals_ABC: &mut DensePolynomial,
    gens: &R1CSSumcheckGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (ZKSumcheckInstanceProof, Vec<Scalar>, Vec<Scalar>, Scalar) {
    let comb_func =
      |poly_A_comp: &Scalar, poly_B_comp: &Scalar| -> Scalar { poly_A_comp * poly_B_comp };
    let (sc_proof_phase_two, r, claims, blind_claim_postsc) = ZKSumcheckInstanceProof::prove_quad(
      claim,
      blind_claim,
      num_rounds,
      evals_z,
      evals_ABC,
      comb_func,
      &gens.gens_1,
      &gens.gens_3,
      transcript,
      random_tape,
    );

    (sc_proof_phase_two, r, claims, blind_claim_postsc)
  }
  */

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
    num_inputs: &Vec<usize>,
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
    witness_secs: Vec<&ProverWitnessSecInfo>,
    // INSTANCES
    inst: &R1CSInstance,
    /* TODO: Alternative PCS
    gens: &R1CSGens,
    */
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (R1CSProof, [Vec<Scalar>; 4]) {
    let timer_prove = Timer::new("R1CSProof::prove");
    transcript.append_protocol_name(R1CSProof::protocol_name());

    let num_witness_secs = witness_secs.len();

    // Assert everything is a power of 2, except num_instances
    assert_eq!(max_num_proofs, max_num_proofs.next_power_of_two());
    for p in num_proofs {
      assert_eq!(*p, p.next_power_of_two());
      assert!(*p <= max_num_proofs);
    }
    for i in num_inputs {
      assert_eq!(*i, i.next_power_of_two());
      assert!(*i <= max_num_inputs);
    }
    // Number of instances is either one or matches num_instances
    assert!(inst.get_num_instances() == 1 || inst.get_num_instances() == num_instances);

    // Assert num_witness_secs is valid
    assert!(num_witness_secs >= 1 && num_witness_secs <= 16);
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
    let block_num_cons = if inst.get_num_instances() == 1 { vec![inst.get_inst_num_cons()[0]; num_instances] } else { inst.get_inst_num_cons().clone() };
    let timer_sc_proof_phase1 = Timer::new("prove_sc_phase_one");

    // append input to variables to create a single vector z
    let timer_tmp = Timer::new("prove_z_mat_gen");
    let mut z_mat: Vec<Vec<Vec<Vec<Scalar>>>> = Vec::new();
    for p in 0..num_instances {
      z_mat.push(Vec::new());
      for q in 0..num_proofs[p] {
        z_mat[p].push(vec![vec![ZERO; num_inputs[p]]; num_witness_secs]);
        for w in 0..witness_secs.len() {
          let ws = witness_secs[w];
          let p_w = if ws.w_mat.len() == 1 { 0 } else { p };
          let q_w = if ws.w_mat[p_w].len() == 1 { 0 } else { q };
          // Only append the first num_inputs_entries of w_mat[p][q]
          for i in 0..min(ws.num_inputs[p_w], num_inputs[p]) {
            z_mat[p][q][w][i] = ws.w_mat[p_w][q_w][i];
          }
        }
      }
    }
    timer_tmp.stop();

    // derive the verifier's challenge \tau
    let timer_tmp = Timer::new("prove_vec_mult");
    let (num_rounds_p, num_rounds_q, num_rounds_x, num_rounds_w, num_rounds_y) = 
      (num_instances.next_power_of_two().log_2(), max_num_proofs.log_2(), num_cons.log_2(), num_witness_secs.log_2(), max_num_inputs.log_2());
    let tau_p = transcript.challenge_vector(b"challenge_tau_p", num_rounds_p);
    let tau_q = transcript.challenge_vector(b"challenge_tau_q", num_rounds_q);
    let tau_x = transcript.challenge_vector(b"challenge_tau_x", num_rounds_x);

    // compute the initial evaluation table for R(\tau, x)
    let mut poly_tau_p = DensePolynomial::new(EqPolynomial::new(tau_p).evals());
    let mut poly_tau_q = DensePolynomial::new(EqPolynomial::new(tau_q).evals());
    let mut poly_tau_x = DensePolynomial::new(EqPolynomial::new(tau_x).evals());
    let (mut poly_Az, mut poly_Bz, mut poly_Cz) =
      inst.multiply_vec_block(
        num_instances, 
        num_proofs.clone(), 
        max_num_proofs, 
        num_inputs.clone(), 
        max_num_inputs, 
        num_cons, 
        block_num_cons.clone(), 
        &z_mat
      );
    timer_tmp.stop();

    // Sumcheck 1: (Az * Bz - Cz) * eq(x, q, p) = 0
    let timer_tmp = Timer::new("prove_sum_check");
    let (sc_proof_phase1, rx, _claims_phase1, blind_claim_postsc1) = R1CSProof::prove_phase_one(
      num_rounds_x + num_rounds_q + num_rounds_p,
      num_rounds_x,
      num_rounds_q,
      num_rounds_p,
      &num_proofs,
      &block_num_cons,
      &mut poly_tau_p,
      &mut poly_tau_q,
      &mut poly_tau_x,
      &mut poly_Az,
      &mut poly_Bz,
      &mut poly_Cz,
      /* TODO: Alternative PCS
      &gens.gens_sc,
      */
      transcript,
      random_tape,
    );
    assert_eq!(poly_tau_p.len(), 1);
    assert_eq!(poly_tau_q.len(), 1);
    assert_eq!(poly_tau_x.len(), 1);
    assert_eq!(poly_Az.len(), 1);
    assert_eq!(poly_Bz.len(), 1);
    assert_eq!(poly_Cz.len(), 1);
    timer_tmp.stop();
    timer_sc_proof_phase1.stop();

    let (tau_claim, Az_claim, Bz_claim, Cz_claim) =
      (&(poly_tau_p[0] * poly_tau_q[0] * poly_tau_x[0]), &poly_Az.index(0, 0, 0, 0), &poly_Bz.index(0, 0, 0, 0), &poly_Cz.index(0, 0, 0, 0));

    let (Az_blind, Bz_blind, Cz_blind, prod_Az_Bz_blind) = (
      random_tape.random_scalar(b"Az_blind"),
      random_tape.random_scalar(b"Bz_blind"),
      random_tape.random_scalar(b"Cz_blind"),
      random_tape.random_scalar(b"prod_Az_Bz_blind"),
    );

    /* TODO: Alternative PCS
    let (pok_Cz_claim, comm_Cz_claim) = {
    */
    let pok_Cz_claim = {
      KnowledgeProof::prove(
        /* TODO: Alternative PCS
        &gens.gens_sc.gens_1,
        */
        transcript,
        random_tape,
        Cz_claim,
        &Cz_blind,
      )
    };

    /* TODO: Alternative PCS
    let (proof_prod, comm_Az_claim, comm_Bz_claim, comm_prod_Az_Bz_claims) = {
    */
    let proof_prod = {
      let prod = Az_claim * Bz_claim;
      ProductProof::prove(
        /* TODO: Alternative PCS
        &gens.gens_sc.gens_1,
        */
        transcript,
        random_tape,
        Az_claim,
        &Az_blind,
        Bz_claim,
        &Bz_blind,
        &prod,
        &prod_Az_Bz_blind,
      )
    };
    
    /* TODO: Alternative PCS
    comm_Az_claim.append_to_transcript(b"comm_Az_claim", transcript);
    comm_Bz_claim.append_to_transcript(b"comm_Bz_claim", transcript);
    comm_Cz_claim.append_to_transcript(b"comm_Cz_claim", transcript);
    comm_prod_Az_Bz_claims.append_to_transcript(b"comm_prod_Az_Bz_claims", transcript);
    */

    // prove the final step of sum-check #1
    let taus_bound_rx = tau_claim;

    let blind_expected_claim_postsc1 = taus_bound_rx * (prod_Az_Bz_blind - Cz_blind);
    let claim_post_phase1 = (Az_claim * Bz_claim - Cz_claim) * taus_bound_rx;
    /* TODO: Alternative PCS
    let (proof_eq_sc_phase1, _C1, _C2) = EqualityProof::prove(
    */
    let proof_eq_sc_phase1 = EqualityProof::prove(
      /* TODO: Alternative PCS
      &gens.gens_sc.gens_1,
      */
      transcript,
      random_tape,
      &claim_post_phase1,
      &blind_expected_claim_postsc1,
      &claim_post_phase1,
      &blind_claim_postsc1,
    );

    // Separate the result rx into rp, rq, and rx
    let (rx_rev, rq_rev) = rx.split_at(num_rounds_x);
    let (rq_rev, rp) = rq_rev.split_at(num_rounds_q);
    let rx: Vec<Scalar> = rx_rev.iter().copied().rev().collect();
    let rq_rev = rq_rev.to_vec();
    let rq: Vec<Scalar> = rq_rev.iter().copied().rev().collect();
    let rp = rp.to_vec();

    // --
    // PHASE 2
    // --
    let timer_sc_proof_phase2 = Timer::new("prove_sc_phase_two");
    // combine the three claims into a single claim
    let r_A = transcript.challenge_scalar(b"challenge_Az");
    let r_B = transcript.challenge_scalar(b"challenge_Bz");
    let r_C = transcript.challenge_scalar(b"challenge_Cz");

    let claim_phase2 = r_A * Az_claim + r_B * Bz_claim + r_C * Cz_claim;
    let blind_claim_phase2 = r_A * Az_blind + r_B * Bz_blind + r_C * Cz_blind;

    let timer_tmp = Timer::new("prove_abc_gen");
    let evals_ABC = {
      // compute the initial evaluation table for R(\tau, x)
      let evals_rx = EqPolynomial::new(rx.clone()).evals();
      let (evals_A, evals_B, evals_C) =
      inst.compute_eval_table_sparse_disjoint_rounds(
        num_instances, 
        inst.get_inst_num_cons(), 
        num_witness_secs, 
        max_num_inputs, 
        &num_inputs, 
        &evals_rx
      );

      let mut evals_ABC = Vec::new();
      for p in 0..inst.get_num_instances() {
        evals_ABC.push(vec![Vec::new()]);
        for w in 0..num_witness_secs {
          evals_ABC[p][0].push(Vec::new());
          for i in 0..num_inputs[p] {
            evals_ABC[p][0][w].push(r_A * evals_A[p][0][w][i] + r_B * evals_B[p][0][w][i] + r_C * evals_C[p][0][w][i]);
          }
        }
      }
      evals_ABC
    };
    let mut ABC_poly = DensePolynomialPqx::new_rev(&evals_ABC, vec![1; num_instances], 1, num_inputs.clone(), max_num_inputs);
    timer_tmp.stop();

    let timer_tmp = Timer::new("prove_z_gen");
    // Construct a p * q * len(z) matrix Z and bound it to r_q
    let mut Z_poly = DensePolynomialPqx::new_rev(&z_mat, num_proofs.clone(), max_num_proofs, num_inputs.clone(), max_num_inputs);
    timer_tmp.stop();
    let timer_tmp = Timer::new("prove_z_bind");
    Z_poly.bound_poly_vars_rq(&rq_rev.to_vec());
    timer_tmp.stop();

    // An Eq function to match p with rp
    let mut eq_p_rp_poly = DensePolynomial::new(EqPolynomial::new(rp).evals());

    // Sumcheck 2: (rA + rB + rC) * Z * eq(p) = e
    let (sc_proof_phase2, ry, claims_phase2, blind_claim_postsc2) = R1CSProof::prove_phase_two(
      num_rounds_y + num_rounds_w + num_rounds_p,
      num_rounds_y,
      num_rounds_w,
      num_rounds_p,
      inst.get_num_instances() == 1,
      num_witness_secs,
      num_inputs.clone(),
      &claim_phase2,
      &blind_claim_phase2,
      &mut eq_p_rp_poly,
      &mut ABC_poly,
      &mut Z_poly,
      /* TODO: Alternative PCS
      &gens.gens_sc,
      */
      transcript,
      random_tape,
    );
    timer_sc_proof_phase2.stop();

    // Separate ry into rp, rw, and ry
    let (ry_rev, rw) = ry.split_at(num_rounds_y);
    let (rw, rp) = rw.split_at(num_rounds_w);
    let rp = rp.to_vec();
    let rw = rw.to_vec();
    let ry: Vec<Scalar> = ry_rev.iter().copied().rev().collect();

    assert_eq!(Z_poly.len(), 1);
    assert_eq!(ABC_poly.len(), 1);

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
    /* TODO: Alternative PCS
    let mut comm_vars_at_ry_list = vec![Vec::new(); num_witness_secs];
    */
    for i in 0..num_witness_secs {
      let w = witness_secs[i];
      let wit_sec_num_instance = w.w_mat.len();
      eval_vars_at_ry_list.push(Vec::new());
      /* TODO: Alternative PCS
      comm_vars_at_ry_list.push(Vec::new());
      */
      for p in 0..wit_sec_num_instance {
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
        /* TODO: Alternative PCS
        comm_vars_at_ry_list[i].push(eval_vars_at_ry.commit(&Scalar::zero(), &gens.gens_pc.gens.gens_1).compress());
        */
      }
    }
    let proof_eval_vars_at_ry_list = PolyEvalProof::prove_batched_instances_disjoint_rounds(
      &poly_list,
      &num_proofs_list,
      &num_inputs_list,
      None,
      &rq,
      &ry,
      &Zr_list,
      None,
      /* TODO: Alternative PCS
      &gens.gens_pc,
      */
      transcript,
      random_tape,
    );

    // Bind the resulting witness list to rp
    // poly_vars stores the result of each witness matrix bounded to (rq_short ++ ry)
    // but we want to bound them to (rq ++ ry)
    // So we need to multiply each entry by (1 - rq0)(1 - rq1)
    let mut eval_vars_comb_list = Vec::new();
    for p in 0..num_instances {
      let wit_sec_p = |i: usize| if witness_secs[i].w_mat.len() == 1 { 0 } else { p };
      let e = |i: usize| eval_vars_at_ry_list[i][wit_sec_p(i)];
      let prefix_list = match num_witness_secs.next_power_of_two() {
        1 => { vec![ONE] }
        2 => { vec![(ONE - rw[0]), rw[0]] }
        4 => { vec![(ONE - rw[0]) * (ONE - rw[1]), (ONE - rw[0]) * rw[1], rw[0] * (ONE - rw[1]), rw[0] * rw[1]] }
        8 => { vec![
          (ONE - rw[0]) * (ONE - rw[1]) * (ONE - rw[2]),
          (ONE - rw[0]) * (ONE - rw[1]) * rw[2],
          (ONE - rw[0]) * rw[1] * (ONE - rw[2]),
          (ONE - rw[0]) * rw[1] * rw[2],
          rw[0] * (ONE - rw[1]) * (ONE - rw[2]),
          rw[0] * (ONE - rw[1]) * rw[2],
          rw[0] * rw[1] * (ONE - rw[2]),
          rw[0] * rw[1] * rw[2],
        ] }
        _ => { panic!("Unsupported num_witness_secs: {}", num_witness_secs); }
      };
      let mut eval_vars_comb = (0..num_witness_secs).fold(ZERO, |s, i| s + prefix_list[i] * e(i));
      for q in 0..(num_rounds_q - num_proofs[p].log_2()) {
        eval_vars_comb *= ONE - rq[q];
      }
      eval_vars_comb_list.push(eval_vars_comb);
    }
    timer_polyeval.stop();

    let poly_vars = DensePolynomial::new(eval_vars_comb_list);
    let eval_vars_at_ry = poly_vars.evaluate(&rp);
    /* TODO: Alternative PCS
    let comm_vars_at_ry = eval_vars_at_ry.commit(&ZERO, &gens.gens_pc.gens.gens_1).compress();
    */

    // prove the final step of sum-check #2
    let blind_expected_claim_postsc2 = ZERO;
    let claim_post_phase2 = claims_phase2[0] * claims_phase2[1] * claims_phase2[2];

    /* TODO: Alternative PCS
    let (proof_eq_sc_phase2, _C1, _C2) = EqualityProof::prove(
    */
    let proof_eq_sc_phase2 = EqualityProof::prove(
      /* TODO: Alternative PCS
      &gens.gens_pc.gens.gens_1,
      */
      transcript,
      random_tape,
      &claim_post_phase2,
      &blind_expected_claim_postsc2,
      &claim_post_phase2,
      &blind_claim_postsc2,
    );

    timer_prove.stop();

    /* TODO: Alternative PCS
    let claims_phase2 = (
      comm_Az_claim,
      comm_Bz_claim,
      comm_Cz_claim,
      comm_prod_Az_Bz_claims,
    );
    */
    let pok_claims_phase2 = (
      pok_Cz_claim, proof_prod
    );

    (
      /* TODO: Alternative PCS
      R1CSProof {
        sc_proof_phase1,
        claims_phase2,
        pok_claims_phase2,
        proof_eq_sc_phase1,
        sc_proof_phase2,
        comm_vars_at_ry_list,
        comm_vars_at_ry,
        proof_eval_vars_at_ry_list,
        proof_eq_sc_phase2
      },
      */
      R1CSProof {
        sc_proof_phase1,
        sc_proof_phase2,
        pok_claims_phase2,
        proof_eq_sc_phase1,
        proof_eq_sc_phase2,
      },
      [rp, rq_rev, rx, [rw, ry].concat()]
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
    /* TODO: Alternative PCS
    gens: &R1CSGens,
    */
    evals: &[Scalar; 3],
    transcript: &mut Transcript,
  ) -> Result<[Vec<Scalar>; 4], ProofVerifyError> {
    transcript.append_protocol_name(R1CSProof::protocol_name());

    let num_witness_secs = witness_secs.len();

    // Assert num_witness_secs is valid
    assert!(num_witness_secs >= 1 && num_witness_secs <= 16);

    let (num_rounds_p, num_rounds_q, num_rounds_x, num_rounds_w, num_rounds_y) = 
      (num_instances.next_power_of_two().log_2(), max_num_proofs.log_2(), num_cons.log_2(), num_witness_secs.log_2(), max_num_inputs.log_2());

    // derive the verifier's challenge tau
    let tau_p = transcript.challenge_vector(b"challenge_tau_p", num_rounds_p);
    let tau_q = transcript.challenge_vector(b"challenge_tau_q", num_rounds_q);
    let tau_x = transcript.challenge_vector(b"challenge_tau_x", num_rounds_x);

    /* TODO: Alternative PCS
    // verify the first sum-check instance
    let claim_phase1 = ZERO
      .commit(&ZERO, &gens.gens_sc.gens_1)
      .compress();
    */

    /* TODO: Alternative PCS
    let (comm_claim_post_phase1, rx) = self.sc_proof_phase1.verify(
    */
    let rx = self.sc_proof_phase1.verify(
      /* TODO: Alternative PCS
      &claim_phase1,
      */
      num_rounds_x + num_rounds_q + num_rounds_p,
      3,
      /* TODO: Alternative PCS
      &gens.gens_sc.gens_1,
      &gens.gens_sc.gens_4,
      */
      transcript,
    )?;

    /* TODO: Alternative PCS
    // perform the intermediate sum-check test with claimed Az, Bz, and Cz
    let (comm_Az_claim, comm_Bz_claim, comm_Cz_claim, comm_prod_Az_Bz_claims) = &self.claims_phase2;
    let (pok_Cz_claim, proof_prod) = &self.pok_claims_phase2;

    pok_Cz_claim.verify(&gens.gens_sc.gens_1, transcript, comm_Cz_claim)?;
    proof_prod.verify(
      &gens.gens_sc.gens_1,
      transcript,
      comm_Az_claim,
      comm_Bz_claim,
      comm_prod_Az_Bz_claims,
    )?;

    comm_Az_claim.append_to_transcript(b"comm_Az_claim", transcript);
    comm_Bz_claim.append_to_transcript(b"comm_Bz_claim", transcript);
    comm_Cz_claim.append_to_transcript(b"comm_Cz_claim", transcript);
    comm_prod_Az_Bz_claims.append_to_transcript(b"comm_prod_Az_Bz_claims", transcript);
    */

    // Separate the result rx into rp_round1, rq, and rx
    let (rx_rev, rq_rev) = rx.split_at(num_rounds_x);
    let (rq_rev, rp_round1) = rq_rev.split_at(num_rounds_q);
    let rx: Vec<Scalar> = rx_rev.iter().copied().rev().collect();
    let rq_rev = rq_rev.to_vec();
    let rq: Vec<Scalar> = rq_rev.iter().copied().rev().collect();
    let rp_round1 = rp_round1.to_vec();

    /* TODO: Alternative PCS
    // taus_bound_rx is really taus_bound_rx_rq_rp
    let taus_bound_rp: Scalar = (0..rp_round1.len())
      .map(|i| rp_round1[i] * tau_p[i] + (ONE - rp_round1[i]) * (ONE - tau_p[i]))
      .product();
    let taus_bound_rq: Scalar = (0..rq_rev.len())
      .map(|i| rq_rev[i] * tau_q[i] + (ONE - rq_rev[i]) * (ONE - tau_q[i]))
      .product();
    let taus_bound_rx: Scalar = (0..rx_rev.len())
      .map(|i| rx_rev[i] * tau_x[i] + (ONE - rx_rev[i]) * (ONE - tau_x[i]))
      .product();
    let taus_bound_rx = taus_bound_rp * taus_bound_rq * taus_bound_rx;

    let expected_claim_post_phase1 = (taus_bound_rx
      * (comm_prod_Az_Bz_claims.decompress().unwrap() - comm_Cz_claim.decompress().unwrap()))
    .compress();

    // verify proof that expected_claim_post_phase1 == claim_post_phase1
    self.proof_eq_sc_phase1.verify(
      &gens.gens_sc.gens_1,
      transcript,
      &expected_claim_post_phase1,
      &comm_claim_post_phase1,
    )?;
    */

    // derive three public challenges and then derive a joint claim
    let r_A = transcript.challenge_scalar(b"challenge_Az");
    let r_B = transcript.challenge_scalar(b"challenge_Bz");
    let r_C = transcript.challenge_scalar(b"challenge_Cz");

    /* TODO: Alternative PCS
    // r_A * comm_Az_claim + r_B * comm_Bz_claim + r_C * comm_Cz_claim;
    let comm_claim_phase2 = GroupElement::vartime_multiscalar_mul(
      iter::once(&r_A)
        .chain(iter::once(&r_B))
        .chain(iter::once(&r_C)),
      iter::once(&comm_Az_claim)
        .chain(iter::once(&comm_Bz_claim))
        .chain(iter::once(&comm_Cz_claim))
        .map(|pt| pt.decompress().unwrap())
        .collect::<Vec<GroupElement>>(),
    )
    .compress();
    */

    // verify the joint claim with a sum-check protocol
    /* TODO: Alternative PCS
    let (comm_claim_post_phase2, ry) = self.sc_proof_phase2.verify(
    */
    let ry = self.sc_proof_phase2.verify(
      /* TODO: Alternative PCS
      &comm_claim_phase2,
      */
      num_rounds_y + num_rounds_w + num_rounds_p,
      3,
      /* TODO: Alternative PCS
      &gens.gens_sc.gens_1,
      &gens.gens_sc.gens_4,
      */
      transcript,
    )?;

    // Separate ry into rp, rw, and ry
    let (ry_rev, rw) = ry.split_at(num_rounds_y);
    let (rw, rp) = rw.split_at(num_rounds_w);
    let rp = rp.to_vec();
    let rw = rw.to_vec();
    let ry: Vec<Scalar> = ry_rev.iter().copied().rev().collect();

    // An Eq function to match p with rp
    let p_rp_poly_bound_ry: Scalar = (0..rp.len())
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
    /* TODO: Alternative PCS
    let mut comm_list = Vec::new();
    */
    let mut num_proofs_list = Vec::new();
    let mut num_inputs_list = Vec::new();
    /* TODO: Alternative PCS
    let mut comm_Zr_list = Vec::new();
    */
    for i in 0..num_witness_secs {
      let w = witness_secs[i];
      let wit_sec_num_instance = w.num_proofs.len();
      for p in 0..wit_sec_num_instance {
        /* TODO: Alternative PCS
        comm_list.push(&w.comm_w[p]);
        */
        num_proofs_list.push(w.num_proofs[p]);
        num_inputs_list.push(w.num_inputs[p]);
        /* TODO: Alternative PCS
        comm_Zr_list.push(self.comm_vars_at_ry_list[i][p].decompress().unwrap());
        */
      }
    }
    /* TODO: Alternative PCS
    PolyEvalProof::verify_batched_instances_disjoint_rounds(
      &self.proof_eval_vars_at_ry_list,
      &num_proofs_list,
      &num_inputs_list,
      &gens.gens_pc,
      transcript,
      &rq,
      &ry,
      &comm_Zr_list,
      &comm_list,
    )?;
    */

    // Then on rp
    /* TODO: Alternative PCS
    let mut expected_comm_vars_list = Vec::new();
    */
    for p in 0..num_instances {
      let wit_sec_p = |i: usize| if witness_secs[i].num_proofs.len() == 1 { 0 } else { p };
      let c = |i: usize| 
        if witness_secs[i].num_inputs[wit_sec_p(i)] >= max_num_inputs {
          /* TODO: Alternative PCS
          self.comm_vars_at_ry_list[i][wit_sec_p(i)].decompress().unwrap()
          */
        } else {
          /* TODO: Alternative PCS
          self.comm_vars_at_ry_list[i][wit_sec_p(i)].decompress().unwrap() * ry_factors[num_rounds_y - witness_secs[i].num_inputs[wit_sec_p(i)].log_2()]
          */
        };
      let prefix_list = match num_witness_secs.next_power_of_two() {
        1 => { vec![ONE] }
        2 => { vec![(ONE - rw[0]), rw[0]] }
        4 => { vec![(ONE - rw[0]) * (ONE - rw[1]), (ONE - rw[0]) * rw[1], rw[0] * (ONE - rw[1]), rw[0] * rw[1]] }
        8 => { vec![
          (ONE - rw[0]) * (ONE - rw[1]) * (ONE - rw[2]),
          (ONE - rw[0]) * (ONE - rw[1]) * rw[2],
          (ONE - rw[0]) * rw[1] * (ONE - rw[2]),
          (ONE - rw[0]) * rw[1] * rw[2],
          rw[0] * (ONE - rw[1]) * (ONE - rw[2]),
          rw[0] * (ONE - rw[1]) * rw[2],
          rw[0] * rw[1] * (ONE - rw[2]),
          rw[0] * rw[1] * rw[2],
        ] }
        _ => { panic!("Unsupported num_witness_secs: {}", num_witness_secs); }
      };
      /* TODO: Alternative PCS
      let mut comm_vars_comb = (1..num_witness_secs).fold(prefix_list[0] * c(0), |s, i| s + prefix_list[i] * c(i));
      for q in 0..(num_rounds_q - num_proofs[p].log_2()) {
        comm_vars_comb *= ONE - rq[q];
      }
      expected_comm_vars_list.push(comm_vars_comb);
      */
    }

    let EQ_p = &EqPolynomial::new(rp.clone()).evals()[..num_instances];
    /* TODO: Alternative PCS
    let expected_comm_vars_at_ry = GroupElement::vartime_multiscalar_mul(EQ_p, expected_comm_vars_list).compress();
    assert_eq!(expected_comm_vars_at_ry, self.comm_vars_at_ry);
    */
    timer_commit_opening.stop();

    /* TODO: Alternative PCS
    // compute commitment to eval_Z_at_ry = (ONE - ry[0]) * self.eval_vars_at_ry + ry[0] * poly_input_eval
    let comm_eval_Z_at_ry = &self.comm_vars_at_ry.decompress().unwrap();
    */

    // perform the final check in the second sum-check protocol
    let [eval_A_r, eval_B_r, eval_C_r] = evals;
    /* TODO: Alternative PCS
    let expected_claim_post_phase2 =
      ((r_A * eval_A_r + r_B * eval_B_r + r_C * eval_C_r) * comm_eval_Z_at_ry * p_rp_poly_bound_ry).compress();
    */

    /* TODO: Alternative PCS
    // verify proof that expected_claim_post_phase2 == claim_post_phase2
    self.proof_eq_sc_phase2.verify(
      &gens.gens_sc.gens_1,
      transcript,
      &expected_claim_post_phase2,
      &comm_claim_post_phase2,
    )?;
    */

    Ok([rp, rq_rev, rx, [rw, ry].concat()])
  }

  /*
  // Proving a single instance with multiple proofs specialized for PERM_POLY and CONSIS_CHECK
  // Constraints is of size max_input_rows_bound * base_constraint_size
  // Inputs of each proof is of size max_input_rows_bound * base_input_size
  // However, only first input_rows[i] * base_input_size entries are non-zero, and only these input_rows[i] * base_input_size entries are supplied
  // Moreover, when multiplying the instance with the inputs, only the first input_rows[i] * base_constraint_size products will be non_zero
  // Let max_input_row = max_i(input_rows[i])
  // All of max_input_rows_bound, max_input_rows, input_rows[i], base_input_size, and base_constraint_size are powers of 2
  //
  // The strategy of prove_single is to redefine the variables such that
  // num_proofs -> num_instances, input_rows -> num_proofs, base_input_size -> num_inputs, base_constraint_size -> num_constraints
  // And apply the data-paralleled version
  pub fn prove_single(
    num_proofs: usize,
    base_constraint_size: usize,
    base_input_size: usize,
    max_input_rows_bound: usize,
    max_input_rows: usize,
    input_rows: &Vec<usize>,

    inst: &R1CSInstance,
    gens: &R1CSGens,
    // The actual input size of the witness, can be different per proof
    // Currently only support w_input_size >= base_input_size
    w_input_size: &Vec<usize>,
    w_mat: &Vec<Vec<Vec<Scalar>>>,
    poly_w_list: &Vec<DensePolynomial>,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (R1CSProof, [Vec<Scalar>; 3]) {
    let timer_prove = Timer::new("R1CSProof::prove");
    transcript.append_protocol_name(R1CSProof::protocol_name());

    // --
    // PRELIMINARIES
    // --

    // Assert meta values are correct
    assert!(num_proofs <= input_rows.len());
    assert_eq!(base_input_size, base_input_size.next_power_of_two());
    assert_eq!(max_input_rows, max_input_rows.next_power_of_two());
    assert_eq!(w_input_size.len(), num_proofs);
    assert_eq!(w_mat.len(), num_proofs);
    assert!(inst.get_num_cons() >= max_input_rows * base_constraint_size);
    for i in 0..num_proofs {
      let input = input_rows[i];
      assert!(input <= max_input_rows);
      assert_eq!(input, input.next_power_of_two());
      assert_eq!(w_mat[i].len(), input);
      assert!(w_input_size[i] >= base_input_size);
      for j in 0..input {
        assert_eq!(w_mat[i][j].len(), w_input_size[i]);
      }
    }
    assert!(max_input_rows <= max_input_rows_bound);

    // --
    // PHASE 1
    // --
    let timer_sc_proof_phase1 = Timer::new("prove_sc_phase_one");
    // append input to variables to create a single vector z
    // Since w_input_size might not match base_input_size, need to reconstruct z
    let mut z_list = Vec::new();
    for p in 0..num_proofs {
      z_list.push(Vec::new());
      for q in 0..input_rows[p] {
        for i in 0..base_input_size {
          z_list[p].push(w_mat[p][q][i]);
        }
      }
    }
    let z_list = &z_list;
    let z_len = max_input_rows * base_input_size;

    // derive the verifier's challenge tau
    let (num_rounds_p, num_rounds_q, num_rounds_xb, num_rounds_yb) = 
      (num_proofs.next_power_of_two().log_2(), max_input_rows.log_2(), base_constraint_size.log_2(), base_input_size.log_2());
      
    let tau_p = transcript.challenge_vector(b"challenge_tau_p", num_rounds_p);
    let tau_q = transcript.challenge_vector(b"challenge_tau_q", num_rounds_q);
    let tau_xb = transcript.challenge_vector(b"challenge_tau_x", num_rounds_xb);

    // compute the initial evaluation table for R(\tau, x)
    let mut poly_tau_p = DensePolynomial::new(EqPolynomial::new(tau_p).evals());
    let mut poly_tau_q = DensePolynomial::new(EqPolynomial::new(tau_q).evals());
    let mut poly_tau_xb = DensePolynomial::new(EqPolynomial::new(tau_xb).evals());
    let (mut poly_Az, mut poly_Bz, mut poly_Cz) =
      inst.multiply_vec_single(num_proofs, input_rows, max_input_rows_bound, max_input_rows, base_constraint_size, base_input_size, z_list);

    // Sumcheck 1: (Az * Bz - Cz) * eq(x, q, p) = 0
    let (sc_proof_phase1, rx, _claims_phase1, blind_claim_postsc1) = R1CSProof::prove_phase_one(
      num_rounds_xb + num_rounds_q + num_rounds_p,
      num_rounds_xb,
      num_rounds_q,
      num_rounds_p,
      &input_rows,
      &mut poly_tau_p,
      &mut poly_tau_q,
      &mut poly_tau_xb,
      &mut poly_Az,
      &mut poly_Bz,
      &mut poly_Cz,
      &gens.gens_sc,
      transcript,
      random_tape,
    );
    assert_eq!(poly_tau_p.len(), 1);
    assert_eq!(poly_tau_q.len(), 1);
    assert_eq!(poly_tau_xb.len(), 1);
    assert_eq!(poly_Az.len(), 1);
    assert_eq!(poly_Bz.len(), 1);
    assert_eq!(poly_Cz.len(), 1);
    timer_sc_proof_phase1.stop();

    let (tau_claim, Az_claim, Bz_claim, Cz_claim) =
      (&(poly_tau_p[0] * poly_tau_q[0] * poly_tau_xb[0]), &poly_Az.index(0, 0, 0), &poly_Bz.index(0, 0, 0), &poly_Cz.index(0, 0, 0));

    let (Az_blind, Bz_blind, Cz_blind, prod_Az_Bz_blind) = (
      random_tape.random_scalar(b"Az_blind"),
      random_tape.random_scalar(b"Bz_blind"),
      random_tape.random_scalar(b"Cz_blind"),
      random_tape.random_scalar(b"prod_Az_Bz_blind"),
    );

    let (pok_Cz_claim, comm_Cz_claim) = {
      KnowledgeProof::prove(
        &gens.gens_sc.gens_1,
        transcript,
        random_tape,
        Cz_claim,
        &Cz_blind,
      )
    };

    let (proof_prod, comm_Az_claim, comm_Bz_claim, comm_prod_Az_Bz_claims) = {
      let prod = Az_claim * Bz_claim;
      ProductProof::prove(
        &gens.gens_sc.gens_1,
        transcript,
        random_tape,
        Az_claim,
        &Az_blind,
        Bz_claim,
        &Bz_blind,
        &prod,
        &prod_Az_Bz_blind,
      )
    };

    comm_Az_claim.append_to_transcript(b"comm_Az_claim", transcript);
    comm_Bz_claim.append_to_transcript(b"comm_Bz_claim", transcript);
    comm_Cz_claim.append_to_transcript(b"comm_Cz_claim", transcript);
    comm_prod_Az_Bz_claims.append_to_transcript(b"comm_prod_Az_Bz_claims", transcript);

    // prove the final step of sum-check #1
    let taus_bound_rx = tau_claim;

    let blind_expected_claim_postsc1 = taus_bound_rx * (prod_Az_Bz_blind - Cz_blind);
    let claim_post_phase1 = (Az_claim * Bz_claim - Cz_claim) * taus_bound_rx;
    let (proof_eq_sc_phase1, _C1, _C2) = EqualityProof::prove(
      &gens.gens_sc.gens_1,
      transcript,
      random_tape,
      &claim_post_phase1,
      &blind_expected_claim_postsc1,
      &claim_post_phase1,
      &blind_claim_postsc1,
    );

    // Separate the result rx into rp, rq, and rx
    let (rx, rq_rev) = rx.split_at(num_rounds_xb);
    let (rq_rev, rp) = rq_rev.split_at(num_rounds_q);

    let rx = [rq_rev.iter().copied().rev().collect(), rx.to_vec()].concat();
    let rp = rp.to_vec();

    // --
    // PHASE 2
    // --

    let timer_sc_proof_phase2 = Timer::new("prove_sc_phase_two");
    // combine the three claims into a single claim
    let r_A = transcript.challenge_scalar(b"challenge_Az");
    let r_B = transcript.challenge_scalar(b"challenge_Bz");
    let r_C = transcript.challenge_scalar(b"challenge_Cz");
    let claim_phase2 = r_A * Az_claim + r_B * Bz_claim + r_C * Cz_claim;
    let blind_claim_phase2 = r_A * Az_blind + r_B * Bz_blind + r_C * Cz_blind;

    // Here we have 1 qx*qy instance
    // Unlike the parallel proof where we have p x*y instance
    let evals_ABC = {
      // compute the initial evaluation table for R(\tau, x)
      let evals_rx = EqPolynomial::new(rx.clone()).evals();
      let (evals_A, evals_B, evals_C) =
        inst.compute_eval_table_sparse_single(
          1, 
          max_input_rows, 
          max_input_rows_bound, 
          inst.get_num_cons(), 
          z_len,
          &evals_rx
        );

      assert_eq!(evals_A.len(), evals_B.len());
      assert_eq!(evals_A.len(), evals_C.len());
      (0..evals_A.len())
        .map(|i| r_A * evals_A[i] + r_B * evals_B[i] + r_C * evals_C[i])
        .collect::<Vec<Scalar>>()
    };
    let mut ABC_poly = DensePolynomial::new(evals_ABC);

    // Construct Z_poly evaluated on rp within runtime bound
    // Here we have p length-q*y Z, want to bind to rp
    let mut n = num_proofs.next_power_of_two() / 2;
    let mut z_list = z_list.clone();
  
    for r in &rp {
      for p in 0..n {
        for x in 0..z_list[p].len() {
          z_list[p][x] *= ONE - r;
        }
        if p + n < num_proofs {
          for x in 0..z_list[p + n].len() {
            let z_high = z_list[p + n][x];
            z_list[p][x] += r * z_high;
          }
        }
      }
      n /= 2;
    }
    let mut Z_poly = DensePolynomial::new(z_list[0].clone());

    // Sumcheck 2: (rA + rB + rC) * Z = e
    let (sc_proof_phase2, ry, claims_phase2, blind_claim_postsc2) = R1CSProof::prove_phase_two_single(
      num_rounds_q + num_rounds_yb,
      &claim_phase2,
      &blind_claim_phase2,
      &mut Z_poly,
      &mut ABC_poly,
      &gens.gens_sc,
      transcript,
      random_tape,
    );
    timer_sc_proof_phase2.stop();

    // Separate ry into rq and ry_short,
    // Keep the original ry for return
    let (rq, ry_short) = ry.split_at(num_rounds_q);
    let rq = rq.to_vec();
    let ry_short = ry_short.to_vec();

    assert_eq!(Z_poly.len(), 1);
    assert_eq!(ABC_poly.len(), 1);

    // --
    // POLY COMMIT
    // --

    // Bind the witnesses and inputs instance-by-instance
    let mut eval_vars_at_ry_list = Vec::new();
    let mut comm_vars_at_ry_list = Vec::new();
    let timer_polyeval = Timer::new("polyeval");

    for p in 0..num_proofs {
      // If w_input_size > base_input_size, need to pad 0 at the front of ry (but after rq)
      let ry_pad = &vec![ZERO; w_input_size[p].log_2() - base_input_size.log_2()];
      let combined_poly = &poly_w_list[p];
      // Size of input_rows[p] decides how many digits of rq will be used
      let rq_short = &rq[num_rounds_q - input_rows[p].log_2()..];
      let r = &[rq_short, ry_pad, &ry_short].concat();
      let eval_vars_at_ry = combined_poly.evaluate(r);
      eval_vars_at_ry_list.push(eval_vars_at_ry);
      comm_vars_at_ry_list.push(eval_vars_at_ry.commit(&Scalar::zero(), &gens.gens_pc.gens.gens_1).compress());
    }

    let proof_eval_vars_at_ry_list = PolyEvalProof::prove_batched_instances_disjoint_rounds(
      &poly_w_list.iter().map(|i| i).collect(),
      &input_rows,
      &w_input_size,
      None,
      &rq,
      &ry_short,
      &eval_vars_at_ry_list,
      None,
      &gens.gens_pc,
      transcript,
      random_tape,
    );
    
    // Bind the resulting witness list to rp
    // poly_vars stores the result of each witness matrix bounded to (rq_short ++ ry)
    // but we want to bound them to (rq ++ ry)
    // So we need to multiply each entry by (1 - rq0)(1 - rq1)...
    for p in 0..num_proofs {
      for q in 0..(num_rounds_q - input_rows[p].log_2()) {
        eval_vars_at_ry_list[p] *= ONE - ry[q];
      }
    }

    timer_polyeval.stop();

    let poly_vars = DensePolynomial::new(eval_vars_at_ry_list);
    let eval_vars_at_ry = poly_vars.evaluate(&rp);

    let comm_vars_at_ry = eval_vars_at_ry.commit(&ZERO, &gens.gens_pc.gens.gens_1).compress();

    // prove the final step of sum-check #2
    let blind_expected_claim_postsc2 = ZERO;
    let claim_post_phase2 = claims_phase2[0] * claims_phase2[1];

    let (proof_eq_sc_phase2, _C1, _C2) = EqualityProof::prove(
      &gens.gens_pc.gens.gens_1,
      transcript,
      random_tape,
      &claim_post_phase2,
      &blind_expected_claim_postsc2,
      &claim_post_phase2,
      &blind_claim_postsc2,
    );

    timer_prove.stop();

    let claims_phase2 = (
      comm_Az_claim,
      comm_Bz_claim,
      comm_Cz_claim,
      comm_prod_Az_Bz_claims,
    );
    let pok_claims_phase2 = (
      pok_Cz_claim, proof_prod
    );

    // rx and ry might not be long enough: in that case, append them with 0
    let pad = (max_input_rows_bound / max_input_rows).log_2();

    (
      R1CSProof {
        sc_proof_phase1,
        claims_phase2,
        pok_claims_phase2,
        proof_eq_sc_phase1,
        sc_proof_phase2,
        comm_vars_at_ry_list: vec![comm_vars_at_ry_list],
        comm_vars_at_ry,
        proof_eval_vars_at_ry_list,
        proof_eq_sc_phase2
      },
      [rp.clone(), [vec![ZERO; pad], rx].concat(), [vec![ZERO; pad], ry].concat()]
    )
  }

  pub fn verify_single(
    &self,
    num_proofs: usize,
    base_constraint_size: usize,
    base_input_size: usize,
    max_input_rows_bound: usize,
    max_input_rows: usize,
    input_rows: &Vec<usize>,

    gens: &R1CSGens,
    evals: &[Scalar; 3],
    w_input_size: &Vec<usize>,
    // Commitment for witnesses
    comm_w_list: &Vec<PolyCommitment>,
    transcript: &mut Transcript,
  ) -> Result<[Vec<Scalar>; 3], ProofVerifyError> {
    transcript.append_protocol_name(R1CSProof::protocol_name());

    // derive the verifier's challenge tau
    let (num_rounds_p, num_rounds_q, num_rounds_xb, num_rounds_yb) = 
      (num_proofs.next_power_of_two().log_2(), max_input_rows.log_2(), base_constraint_size.log_2(), base_input_size.log_2());
    let tau_p = transcript.challenge_vector(b"challenge_tau_p", num_rounds_p);
    let tau_q = transcript.challenge_vector(b"challenge_tau_q", num_rounds_q);
    let tau_xb = transcript.challenge_vector(b"challenge_tau_x", num_rounds_xb);

    // verify the first sum-check instance
    let claim_phase1 = ZERO
      .commit(&ZERO, &gens.gens_sc.gens_1)
      .compress();
    let (comm_claim_post_phase1, rx) = self.sc_proof_phase1.verify(
      &claim_phase1,
      num_rounds_xb + num_rounds_q + num_rounds_p,
      3,
      &gens.gens_sc.gens_1,
      &gens.gens_sc.gens_4,
      transcript,
    )?;

    // perform the intermediate sum-check test with claimed Az, Bz, and Cz
    let (comm_Az_claim, comm_Bz_claim, comm_Cz_claim, comm_prod_Az_Bz_claims) = &self.claims_phase2;
    let (pok_Cz_claim, proof_prod) = &self.pok_claims_phase2;

    pok_Cz_claim.verify(&gens.gens_sc.gens_1, transcript, comm_Cz_claim)?;
    proof_prod.verify(
      &gens.gens_sc.gens_1,
      transcript,
      comm_Az_claim,
      comm_Bz_claim,
      comm_prod_Az_Bz_claims,
    )?;

    comm_Az_claim.append_to_transcript(b"comm_Az_claim", transcript);
    comm_Bz_claim.append_to_transcript(b"comm_Bz_claim", transcript);
    comm_Cz_claim.append_to_transcript(b"comm_Cz_claim", transcript);
    comm_prod_Az_Bz_claims.append_to_transcript(b"comm_prod_Az_Bz_claims", transcript);

    // Separate the result rx into rp, rq, and rx
    let (rx, rq_rev) = rx.split_at(num_rounds_xb);
    let (rq_rev, rp) = rq_rev.split_at(num_rounds_q);
    let rx = rx.to_vec();
    let rq_rev = rq_rev.to_vec();
    let rq_rx: Vec<Scalar> = rq_rev.iter().copied().rev().collect();
    let rp = rp.to_vec();

    // taus_bound_rx is really taus_bound_rx_rq_rp
    let taus_bound_rp: Scalar = (0..rp.len())
      .map(|i| rp[i] * tau_p[i] + (ONE - rp[i]) * (ONE - tau_p[i]))
      .product();
    let taus_bound_rq: Scalar = (0..rq_rev.len())
      .map(|i| rq_rev[i] * tau_q[i] + (ONE - rq_rev[i]) * (ONE - tau_q[i]))
      .product();
    let taus_bound_rx: Scalar = (0..rx.len())
      .map(|i| rx[i] * tau_xb[i] + (ONE - rx[i]) * (ONE - tau_xb[i]))
      .product();
    let taus_bound_rx = taus_bound_rp * taus_bound_rq * taus_bound_rx;

    let expected_claim_post_phase1 = (taus_bound_rx
      * (comm_prod_Az_Bz_claims.decompress().unwrap() - comm_Cz_claim.decompress().unwrap()))
    .compress();

    // verify proof that expected_claim_post_phase1 == claim_post_phase1
    self.proof_eq_sc_phase1.verify(
      &gens.gens_sc.gens_1,
      transcript,
      &expected_claim_post_phase1,
      &comm_claim_post_phase1,
    )?;

    // derive three public challenges and then derive a joint claim
    let r_A = transcript.challenge_scalar(b"challenge_Az");
    let r_B = transcript.challenge_scalar(b"challenge_Bz");
    let r_C = transcript.challenge_scalar(b"challenge_Cz");

    // r_A * comm_Az_claim + r_B * comm_Bz_claim + r_C * comm_Cz_claim;
    let comm_claim_phase2 = GroupElement::vartime_multiscalar_mul(
      iter::once(&r_A)
        .chain(iter::once(&r_B))
        .chain(iter::once(&r_C)),
      iter::once(&comm_Az_claim)
        .chain(iter::once(&comm_Bz_claim))
        .chain(iter::once(&comm_Cz_claim))
        .map(|pt| pt.decompress().unwrap())
        .collect::<Vec<GroupElement>>(),
    )
    .compress();

    // verify the joint claim with a sum-check protocol
    let (comm_claim_post_phase2, ry) = self.sc_proof_phase2.verify(
      &comm_claim_phase2,
      num_rounds_q + num_rounds_yb,
      2,
      &gens.gens_sc.gens_1,
      &gens.gens_sc.gens_3,
      transcript,
    )?;

    // Separate ry into rq and ry_short,
    // Keep the original ry for return
    let (rq, ry_short) = ry.split_at(num_rounds_q);
    let rq = rq.to_vec();
    let ry_short = ry_short.to_vec();

    // verify Z(rp, rq, ry) proof against the initial commitment
    // First instance-by-instance on ry
    PolyEvalProof::verify_batched_instances_disjoint_rounds(
      &self.proof_eval_vars_at_ry_list,
      &input_rows,
      &w_input_size,
      &gens.gens_pc,
      transcript,
      &rq,
      &ry_short,
      &self.comm_vars_at_ry_list[0].iter().map(|i| i.decompress().unwrap()).collect(),
      &comm_w_list.iter().map(|i| i).collect(),
    )?;

    // Then on rp
    let mut expected_comm_vars_list: Vec<RistrettoPoint> = self.comm_vars_at_ry_list[0].iter().map(|i| i.decompress().unwrap()).collect();
    for p in 0..num_proofs {
      for q in 0..(num_rounds_q - input_rows[p].log_2()) {
        expected_comm_vars_list[p] *= ONE - ry[q];
      }
    }
    let EQ_p = &EqPolynomial::new(rp.clone()).evals()[..num_proofs];
    let expected_comm_vars_at_ry = GroupElement::vartime_multiscalar_mul(EQ_p, expected_comm_vars_list).compress();
    assert_eq!(expected_comm_vars_at_ry, self.comm_vars_at_ry);

    let comm_eval_Z_at_ry = &self.comm_vars_at_ry.decompress().unwrap();

    // perform the final check in the second sum-check protocol
    let [eval_A_r, eval_B_r, eval_C_r] = evals;
    let expected_claim_post_phase2 =
      ((r_A * eval_A_r + r_B * eval_B_r + r_C * eval_C_r) * comm_eval_Z_at_ry).compress();

    // verify proof that expected_claim_post_phase2 == claim_post_phase2
    self.proof_eq_sc_phase2.verify(
      &gens.gens_sc.gens_1,
      transcript,
      &expected_claim_post_phase2,
      &comm_claim_post_phase2,
    )?;

    // rx and ry might not be long enough: in that case, append them with 0
    let pad = (max_input_rows_bound / max_input_rows).log_2();
    Ok([rp, [vec![ZERO; pad], rq_rx, rx].concat(), [vec![ZERO; pad], ry].concat()])
  }
  */
}

// #[cfg(test)]
// mod tests {
//   use super::*;
//   use rand::rngs::OsRng;

//   fn produce_tiny_r1cs() -> (R1CSInstance, Vec<Scalar>, Vec<Scalar>) {
//     // three constraints over five variables Z1, Z2, Z3, Z4, and Z5
//     // rounded to the nearest power of two
//     let num_cons = 128;
//     let num_vars = 256;
//     let num_inputs = 2;

//     // encode the above constraints into three matrices
//     let mut A: Vec<(usize, usize, Scalar)> = Vec::new();
//     let mut B: Vec<(usize, usize, Scalar)> = Vec::new();
//     let mut C: Vec<(usize, usize, Scalar)> = Vec::new();

//     let one = ONE;
//     // constraint 0 entries
//     // (Z1 + Z2) * I0 - Z3 = 0;
//     A.push((0, 0, one));
//     A.push((0, 1, one));
//     B.push((0, num_vars + 1, one));
//     C.push((0, 2, one));

//     // constraint 1 entries
//     // (Z1 + I1) * (Z3) - Z4 = 0
//     A.push((1, 0, one));
//     A.push((1, num_vars + 2, one));
//     B.push((1, 2, one));
//     C.push((1, 3, one));
//     // constraint 3 entries
//     // Z5 * 1 - 0 = 0
//     A.push((2, 4, one));
//     B.push((2, num_vars, one));

//     let inst = R1CSInstance::new(num_cons, num_vars, num_inputs, &A, &B, &C);

//     // compute a satisfying assignment
//     let mut csprng: OsRng = OsRng;
//     let i0 = Scalar::random(&mut csprng);
//     let i1 = Scalar::random(&mut csprng);
//     let z1 = Scalar::random(&mut csprng);
//     let z2 = Scalar::random(&mut csprng);
//     let z3 = (z1 + z2) * i0; // constraint 1: (Z1 + Z2) * I0 - Z3 = 0;
//     let z4 = (z1 + i1) * z3; // constraint 2: (Z1 + I1) * (Z3) - Z4 = 0
//     let z5 = ZERO; //constraint 3

//     let mut vars = vec![ZERO; num_vars];
//     vars[0] = z1;
//     vars[1] = z2;
//     vars[2] = z3;
//     vars[3] = z4;
//     vars[4] = z5;

//     let mut input = vec![ZERO; num_inputs];
//     input[0] = i0;
//     input[1] = i1;

//     (inst, vars, input)
//   }

//   #[test]
//   fn test_tiny_r1cs() {
//     let (inst, vars, input) = tests::produce_tiny_r1cs();
//     let is_sat = inst.is_sat(&vars, &input);
//     assert!(is_sat);
//   }

//   #[test]
//   fn test_synthetic_r1cs() {
//     let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(1024, 1024, 10);
//     let is_sat = inst.is_sat(&vars, &input);
//     assert!(is_sat);
//   }

//   #[test]
//   pub fn check_r1cs_proof() {
//     let num_vars = 1024;
//     let num_cons = num_vars;
//     let num_inputs = 10;
//     let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

//     let gens = R1CSGens::new(b"test-m", num_cons, num_vars);

//     let mut random_tape = RandomTape::new(b"proof");
//     let mut prover_transcript = Transcript::new(b"example");
//     let (proof, rx, ry) = R1CSProof::prove(
//       &inst,
//       vars,
//       &input,
//       &gens,
//       &mut prover_transcript,
//       &mut random_tape,
//     );

//     let inst_evals = inst.evaluate(&rx, &ry);

//     let mut verifier_transcript = Transcript::new(b"example");
//     assert!(proof
//       .verify(
//         inst.get_num_vars(),
//         inst.get_num_cons(),
//         &input,
//         &inst_evals,
//         &mut verifier_transcript,
//         &gens,
//       )
//       .is_ok());
//   }
// }