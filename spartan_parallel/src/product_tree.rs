#![allow(dead_code)]
use ff_ext::ExtensionField;

use multilinear_extensions::mle::{DenseMultilinearExtension, MultilinearExtension};
use super::dense_mlpoly::EqPolynomial;
use super::math::Math;
use super::sumcheck::SumcheckInstanceProof;
use super::transcript::{Transcript, append_scalar, challenge_scalar, challenge_vector};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone)]
pub struct ProductCircuit<E: ExtensionField> {
  left_vec: Vec<DenseMultilinearExtension<E>>,
  right_vec: Vec<DenseMultilinearExtension<E>>,
}

impl<E: ExtensionField> ProductCircuit<E> {
  fn compute_layer(
    inp_left: &DenseMultilinearExtension<E>,
    inp_right: &DenseMultilinearExtension<E>,
  ) -> (DenseMultilinearExtension<E>, DenseMultilinearExtension<E>) {
    let len = inp_left.evaluations().len() + inp_right.evaluations().len();
    let outp_left = (0..len / 4)
      .map(|i| inp_left.get_ext_field_vec()[i] * inp_right.get_ext_field_vec()[i])
      .collect::<Vec<E>>();
    let outp_right = (len / 4..len / 2)
      .map(|i| inp_left.get_ext_field_vec()[i] * inp_right.get_ext_field_vec()[i])
      .collect::<Vec<E>>();

    (
      DenseMultilinearExtension::from_evaluation_vec_smart(outp_left.len().log_2(), outp_left),
      DenseMultilinearExtension::from_evaluation_vec_smart(outp_right.len().log_2(), outp_right),
    )
  }

  pub fn new(poly: &DenseMultilinearExtension<E>) -> Self {
    let mut left_vec: Vec<DenseMultilinearExtension<E>> = Vec::new();
    let mut right_vec: Vec<DenseMultilinearExtension<E>> = Vec::new();

    let split_idx = poly.evaluations().len() / 2;
    let num_layers = poly.evaluations().len().log_2();

    let (outp_left, outp_right): (DenseMultilinearExtension<E>, DenseMultilinearExtension<E>) = (
      DenseMultilinearExtension::from_evaluation_vec_smart(split_idx.log_2(), poly.get_ext_field_vec()[0..split_idx].to_vec()),
      DenseMultilinearExtension::from_evaluation_vec_smart(split_idx.log_2(), poly.get_ext_field_vec()[split_idx..].to_vec())
    );

    left_vec.push(outp_left);
    right_vec.push(outp_right);

    for i in 0..num_layers - 1 {
      let (outp_left, outp_right) = ProductCircuit::compute_layer(&left_vec[i], &right_vec[i]);
      left_vec.push(outp_left);
      right_vec.push(outp_right);
    }

    ProductCircuit {
      left_vec,
      right_vec,
    }
  }

  pub fn evaluate(&self) -> E {
    let len = self.left_vec.len();
    assert_eq!(self.left_vec[len - 1].num_vars, 0);
    assert_eq!(self.right_vec[len - 1].num_vars, 0);
    self.left_vec[len - 1].get_ext_field_vec()[0] * self.right_vec[len - 1].get_ext_field_vec()[0]
  }
}

#[derive(Clone)]
pub struct DotProductCircuit<E: ExtensionField> {
  left: DenseMultilinearExtension<E>,
  right: DenseMultilinearExtension<E>,
  weight: DenseMultilinearExtension<E>,
}

impl<E: ExtensionField> DotProductCircuit<E> {
  pub fn new(
    left: DenseMultilinearExtension<E>,
    right: DenseMultilinearExtension<E>,
    weight: DenseMultilinearExtension<E>,
  ) -> Self {
    assert_eq!(left.evaluations().len(), right.evaluations().len());
    assert_eq!(left.evaluations().len(), weight.evaluations().len());
    DotProductCircuit {
      left,
      right,
      weight,
    }
  }

  pub fn evaluate(&self) -> E {
    (0..self.left.evaluations().len())
      .map(|i| self.left.get_ext_field_vec()[i] * self.right.get_ext_field_vec()[i] * self.weight.get_ext_field_vec()[i])
      .sum()
  }

  pub fn split(&mut self) -> (DotProductCircuit<E>, DotProductCircuit<E>) {
    let idx = self.left.evaluations().len() / 2;
    assert_eq!(idx * 2, self.left.evaluations().len());

    let (l1, l2): (DenseMultilinearExtension<E>, DenseMultilinearExtension<E>) = (
      DenseMultilinearExtension::from_evaluation_vec_smart(idx.log_2(), self.left.get_ext_field_vec()[0..idx].to_vec()),
      DenseMultilinearExtension::from_evaluation_vec_smart(idx.log_2(), self.left.get_ext_field_vec()[idx..].to_vec())
    );
    let (r1, r2): (DenseMultilinearExtension<E>, DenseMultilinearExtension<E>) = (
      DenseMultilinearExtension::from_evaluation_vec_smart(idx.log_2(), self.right.get_ext_field_vec()[0..idx].to_vec()),
      DenseMultilinearExtension::from_evaluation_vec_smart(idx.log_2(), self.right.get_ext_field_vec()[idx..].to_vec())
    );
    let (w1, w2): (DenseMultilinearExtension<E>, DenseMultilinearExtension<E>) = (
      DenseMultilinearExtension::from_evaluation_vec_smart(idx.log_2(), self.weight.get_ext_field_vec()[0..idx].to_vec()),
      DenseMultilinearExtension::from_evaluation_vec_smart(idx.log_2(), self.weight.get_ext_field_vec()[idx..].to_vec())
    );

    (
      DotProductCircuit {
        left: l1,
        right: r1,
        weight: w1,
      },
      DotProductCircuit {
        left: l2,
        right: r2,
        weight: w2,
      },
    )
  }
}

#[allow(dead_code)]
#[derive(Debug, Serialize, Deserialize)]
pub struct LayerProof<E: ExtensionField> {
  pub proof: SumcheckInstanceProof<E>,
  pub claims: Vec<E>,
}

#[allow(dead_code)]
impl<E: ExtensionField> LayerProof<E> {
  pub fn verify(
    &self,
    claim: E,
    num_rounds: usize,
    degree_bound: usize,
    transcript: &mut Transcript<E>,
  ) -> (E, Vec<E>) {
    self
      .proof
      .verify(claim, num_rounds, degree_bound, transcript)
      .unwrap()
  }
}

#[allow(dead_code)]
#[derive(Debug, Serialize, Deserialize)]
pub struct LayerProofBatched<E: ExtensionField> {
  pub proof: SumcheckInstanceProof<E>,
  pub claims_prod_left: Vec<E>,
  pub claims_prod_right: Vec<E>,
}

#[allow(dead_code)]
impl<E: ExtensionField> LayerProofBatched<E> {
  pub fn verify(
    &self,
    claim: E,
    num_rounds: usize,
    degree_bound: usize,
    transcript: &mut Transcript<E>,
  ) -> (E, Vec<E>) {
    self
      .proof
      .verify(claim, num_rounds, degree_bound, transcript)
      .unwrap()
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ProductCircuitEvalProof<E: ExtensionField> {
  proof: Vec<LayerProof<E>>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ProductCircuitEvalProofBatched<E: ExtensionField> {
  proof: Vec<LayerProofBatched<E>>,
  claims_dotp: (Vec<E>, Vec<E>, Vec<E>),
}

impl<E: ExtensionField> ProductCircuitEvalProof<E> {
  #![allow(dead_code)]
  pub fn prove(circuit: &mut ProductCircuit<E>, transcript: &mut Transcript<E>) -> (Self, E, Vec<E>) {
    let mut proof: Vec<LayerProof<E>> = Vec::new();
    let num_layers = circuit.left_vec.len();

    let mut claim = circuit.evaluate();
    let mut rand = Vec::new();
    for layer_id in (0..num_layers).rev() {
      let len = circuit.left_vec[layer_id].evaluations().len() + circuit.right_vec[layer_id].evaluations().len();

      let poly_c_evals = EqPolynomial::new(rand.clone()).evals();
      let mut poly_C = DenseMultilinearExtension::from_evaluation_vec_smart(poly_c_evals.len().log_2(), poly_c_evals);
      assert_eq!(poly_C.evaluations().len(), len / 2);

      let num_rounds_prod = poly_C.evaluations().len().log_2();
      let comb_func_prod = |poly_A_comp: &E, poly_B_comp: &E, poly_C_comp: &E| -> E {
        *poly_A_comp * *poly_B_comp * *poly_C_comp
      };
      let (proof_prod, rand_prod, claims_prod) = SumcheckInstanceProof::prove_cubic(
        &claim,
        num_rounds_prod,
        &mut circuit.left_vec[layer_id],
        &mut circuit.right_vec[layer_id],
        &mut poly_C,
        comb_func_prod,
        transcript,
      );

      append_scalar(b"claim_prod_left", transcript, claims_prod[0]);
      append_scalar(b"claim_prod_right", transcript, claims_prod[1]);

      // produce a random challenge
      let r_layer = challenge_scalar(transcript, b"challenge_r_layer");
      claim = claims_prod[0] + r_layer * (claims_prod[1] - claims_prod[0]);

      let mut ext = vec![r_layer];
      ext.extend(rand_prod);
      rand = ext;

      proof.push(LayerProof {
        proof: proof_prod,
        claims: claims_prod[0..claims_prod.len() - 1].to_vec(),
      });
    }

    (ProductCircuitEvalProof { proof }, claim, rand)
  }

  pub fn verify(&self, eval: E, len: usize, transcript: &mut Transcript<E>) -> (E, Vec<E>) {
    let num_layers = len.log_2();
    let mut claim = eval;
    let mut rand: Vec<E> = Vec::new();
    //let mut num_rounds = 0;
    assert_eq!(self.proof.len(), num_layers);
    for (num_rounds, i) in (0..num_layers).enumerate() {
      let (claim_last, rand_prod) = self.proof[i].verify(claim, num_rounds, 3, transcript);

      let claims_prod = &self.proof[i].claims;
      append_scalar(b"claim_prod_left", transcript, claims_prod[0]);
      append_scalar(b"claim_prod_right", transcript, claims_prod[1]);

      assert_eq!(rand.len(), rand_prod.len());
      let eq: E = (0..rand.len())
        .map(|i| {
          rand[i] * rand_prod[i] + (E::ONE - rand[i]) * (E::ONE - rand_prod[i])
        })
        .product();
      assert_eq!(claims_prod[0] * claims_prod[1] * eq, claim_last);

      // produce a random challenge
      let r_layer = challenge_scalar(transcript, b"challenge_r_layer");
      claim = (E::ONE - r_layer) * claims_prod[0] + r_layer * claims_prod[1];
      let mut ext = vec![r_layer];
      ext.extend(rand_prod);
      rand = ext;
    }

    (claim, rand)
  }
}

impl<E: ExtensionField> ProductCircuitEvalProofBatched<E> {
  pub fn prove(
    prod_circuit_vec: &mut Vec<&mut ProductCircuit<E>>,
    dotp_circuit_vec: &mut Vec<&mut DotProductCircuit<E>>,
    transcript: &mut Transcript<E>,
  ) -> (Self, Vec<E>) {
    assert!(!prod_circuit_vec.is_empty());

    let mut claims_dotp_final = (Vec::new(), Vec::new(), Vec::new());

    let mut proof_layers: Vec<LayerProofBatched<E>> = Vec::new();
    let num_layers = prod_circuit_vec[0].left_vec.len();
    let mut claims_to_verify = (0..prod_circuit_vec.len())
      .map(|i| prod_circuit_vec[i].evaluate())
      .collect::<Vec<E>>();
    let mut rand = Vec::new();
    for layer_id in (0..num_layers).rev() {
      // prepare paralell instance that share poly_C first
      let len = prod_circuit_vec[0].left_vec[layer_id].evaluations().len()
        + prod_circuit_vec[0].right_vec[layer_id].evaluations().len();

      let poly_c_par_evals = EqPolynomial::new(rand.clone()).evals();
      let mut poly_C_par = DenseMultilinearExtension::from_evaluation_vec_smart(poly_c_par_evals.len().log_2(), poly_c_par_evals);
      assert_eq!(poly_C_par.evaluations().len(), len / 2);

      let num_rounds_prod = poly_C_par.evaluations().len().log_2();
      let comb_func_prod = |poly_A_comp: &E, poly_B_comp: &E, poly_C_comp: &E| -> E {
        *poly_A_comp * *poly_B_comp * *poly_C_comp
      };

      let mut poly_A_batched_par: Vec<&mut DenseMultilinearExtension<E>> = Vec::new();
      let mut poly_B_batched_par: Vec<&mut DenseMultilinearExtension<E>> = Vec::new();
      for prod_circuit in prod_circuit_vec.iter_mut() {
        poly_A_batched_par.push(&mut prod_circuit.left_vec[layer_id]);
        poly_B_batched_par.push(&mut prod_circuit.right_vec[layer_id])
      }
      let poly_vec_par = (
        &mut poly_A_batched_par,
        &mut poly_B_batched_par,
        &mut poly_C_par,
      );

      // prepare sequential instances that don't share poly_C
      let mut poly_A_batched_seq: Vec<&mut DenseMultilinearExtension<E>> = Vec::new();
      let mut poly_B_batched_seq: Vec<&mut DenseMultilinearExtension<E>> = Vec::new();
      let mut poly_C_batched_seq: Vec<&mut DenseMultilinearExtension<E>> = Vec::new();
      if layer_id == 0 && !dotp_circuit_vec.is_empty() {
        // add additional claims
        for item in dotp_circuit_vec.iter() {
          claims_to_verify.push(item.evaluate());
          assert_eq!(len / 2, item.left.evaluations().len());
          assert_eq!(len / 2, item.right.evaluations().len());
          assert_eq!(len / 2, item.weight.evaluations().len());
        }

        for dotp_circuit in dotp_circuit_vec.iter_mut() {
          poly_A_batched_seq.push(&mut dotp_circuit.left);
          poly_B_batched_seq.push(&mut dotp_circuit.right);
          poly_C_batched_seq.push(&mut dotp_circuit.weight);
        }
      }
      let poly_vec_seq = (
        &mut poly_A_batched_seq,
        &mut poly_B_batched_seq,
        &mut poly_C_batched_seq,
      );

      // produce a fresh set of coeffs and a joint claim
      let coeff_vec = challenge_vector(transcript, b"rand_coeffs_next_layer", claims_to_verify.len());

      let claim = (0..claims_to_verify.len())
        .map(|i| claims_to_verify[i] * coeff_vec[i])
        .sum();

      let (proof, rand_prod, claims_prod, claims_dotp) = SumcheckInstanceProof::prove_cubic_batched(
        &claim,
        num_rounds_prod,
        poly_vec_par,
        poly_vec_seq,
        &coeff_vec,
        comb_func_prod,
        transcript,
      );

      let (claims_prod_left, claims_prod_right, _claims_eq) = claims_prod;
      for i in 0..prod_circuit_vec.len() {
        append_scalar(b"claim_prod_left", transcript, claims_prod_left[i]);
        append_scalar(b"claim_prod_right", transcript, claims_prod_right[i]);
      }

      if layer_id == 0 && !dotp_circuit_vec.is_empty() {
        let (claims_dotp_left, claims_dotp_right, claims_dotp_weight) = claims_dotp;
        for i in 0..dotp_circuit_vec.len() {
          append_scalar(b"claim_dotp_left", transcript, claims_dotp_left[i]);
          append_scalar(b"claim_dotp_right", transcript, claims_dotp_right[i]);
          append_scalar(b"claim_dotp_weight", transcript, claims_dotp_weight[i]);
        }
        claims_dotp_final = (claims_dotp_left, claims_dotp_right, claims_dotp_weight);
      }

      // produce a random challenge to condense two claims into a single claim
      let r_layer = challenge_scalar(transcript, b"challenge_r_layer");

      claims_to_verify = (0..prod_circuit_vec.len())
        .map(|i| claims_prod_left[i] + r_layer * (claims_prod_right[i] - claims_prod_left[i]))
        .collect::<Vec<E>>();

      let mut ext = vec![r_layer];
      ext.extend(rand_prod);
      rand = ext;

      proof_layers.push(LayerProofBatched {
        proof,
        claims_prod_left,
        claims_prod_right,
      });
    }

    (
      ProductCircuitEvalProofBatched {
        proof: proof_layers,
        claims_dotp: claims_dotp_final,
      },
      rand,
    )
  }

  pub fn verify(
    &self,
    claims_prod_vec: &[E],
    claims_dotp_vec: &[E],
    len: usize,
    transcript: &mut Transcript<E>,
  ) -> (Vec<E>, Vec<E>, Vec<E>) {
    let num_layers = len.log_2();
    let mut rand: Vec<E> = Vec::new();
    //let mut num_rounds = 0;
    assert_eq!(self.proof.len(), num_layers);

    let mut claims_to_verify = claims_prod_vec.to_owned();
    let mut claims_to_verify_dotp: Vec<E> = Vec::new();
    for (num_rounds, i) in (0..num_layers).enumerate() {
      if i == num_layers - 1 {
        claims_to_verify.extend(claims_dotp_vec);
      }

      // produce random coefficients, one for each instance
      let coeff_vec: Vec<E> =
        challenge_vector(transcript, b"rand_coeffs_next_layer", claims_to_verify.len());

      // produce a joint claim
      let claim = (0..claims_to_verify.len())
        .map(|i| claims_to_verify[i] * coeff_vec[i])
        .sum();

      let (claim_last, rand_prod) = self.proof[i].verify(claim, num_rounds, 3, transcript);

      let claims_prod_left = &self.proof[i].claims_prod_left;
      let claims_prod_right = &self.proof[i].claims_prod_right;
      assert_eq!(claims_prod_left.len(), claims_prod_vec.len());
      assert_eq!(claims_prod_right.len(), claims_prod_vec.len());

      for i in 0..claims_prod_vec.len() {
        append_scalar(b"claim_prod_left", transcript, claims_prod_left[i]);
        append_scalar(b"claim_prod_right", transcript, claims_prod_right[i]);
      }

      assert_eq!(rand.len(), rand_prod.len());
      let eq: E = (0..rand.len())
        .map(|i| {
          rand[i] * rand_prod[i] + (E::ONE - rand[i]) * (E::ONE - rand_prod[i])
        })
        .product();
      let mut claim_expected: E = (0..claims_prod_vec.len())
        .map(|i| coeff_vec[i] * (claims_prod_left[i] * claims_prod_right[i] * eq))
        .sum();

      // add claims from the dotp instances
      if i == num_layers - 1 {
        let num_prod_instances = claims_prod_vec.len();
        let (claims_dotp_left, claims_dotp_right, claims_dotp_weight) = &self.claims_dotp;
        for i in 0..claims_dotp_left.len() {
          append_scalar(b"claim_dotp_left", transcript, claims_dotp_left[i]);
          append_scalar(b"claim_dotp_right", transcript, claims_dotp_right[i]);
          append_scalar(b"claim_dotp_weight", transcript, claims_dotp_weight[i]);

          claim_expected = claim_expected
            + coeff_vec[i + num_prod_instances]
              * claims_dotp_left[i]
              * claims_dotp_right[i]
              * claims_dotp_weight[i];
        }
      }

      assert_eq!(claim_expected, claim_last);

      // produce a random challenge
      let r_layer = challenge_scalar(transcript, b"challenge_r_layer");

      claims_to_verify = (0..claims_prod_left.len())
        .map(|i| claims_prod_left[i] + r_layer * (claims_prod_right[i] - claims_prod_left[i]))
        .collect::<Vec<E>>();

      // add claims to verify for dotp circuit
      if i == num_layers - 1 {
        let (claims_dotp_left, claims_dotp_right, claims_dotp_weight) = &self.claims_dotp;

        for i in 0..claims_dotp_vec.len() / 2 {
          // combine left claims
          let claim_left = claims_dotp_left[2 * i]
            + r_layer * (claims_dotp_left[2 * i + 1] - claims_dotp_left[2 * i]);

          let claim_right = claims_dotp_right[2 * i]
            + r_layer * (claims_dotp_right[2 * i + 1] - claims_dotp_right[2 * i]);

          let claim_weight = claims_dotp_weight[2 * i]
            + r_layer * (claims_dotp_weight[2 * i + 1] - claims_dotp_weight[2 * i]);
          claims_to_verify_dotp.push(claim_left);
          claims_to_verify_dotp.push(claim_right);
          claims_to_verify_dotp.push(claim_weight);
        }
      }

      let mut ext = vec![r_layer];
      ext.extend(rand_prod);
      rand = ext;
    }
    (claims_to_verify, claims_to_verify_dotp, rand)
  }
}
