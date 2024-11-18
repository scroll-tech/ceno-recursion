#![allow(clippy::too_many_arguments)]
use super::errors::ProofVerifyError;
use super::math::Math;
use super::random::RandomTape;
use super::scalar::Scalar;
use super::transcript::{AppendToTranscript, ProofTranscript};
use merlin::Transcript;
use serde::{Deserialize, Serialize};
mod bullet;
use bullet::BulletReductionProof;

#[derive(Serialize, Deserialize, Debug)]
pub struct KnowledgeProof {
  z1: Scalar,
  z2: Scalar,
}

impl KnowledgeProof {
  fn protocol_name() -> &'static [u8] {
    b"knowledge proof"
  }

  pub fn prove(
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x: &Scalar,
    r: &Scalar,
  ) -> KnowledgeProof {
    transcript.append_protocol_name(KnowledgeProof::protocol_name());

    // produce two random Scalars
    let t1 = random_tape.random_scalar(b"t1");
    let t2 = random_tape.random_scalar(b"t2");

    let c = transcript.challenge_scalar(b"c");

    let z1 = x * c + t1;
    let z2 = r * c + t2;

    KnowledgeProof { z1, z2 }
  }

  pub fn verify(&self, _transcript: &mut Transcript) -> Result<(), ProofVerifyError> {
    // TODO: Alternative PCS Verification
    Ok(())
  }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct EqualityProof {
  z: Scalar,
}

impl EqualityProof {
  fn protocol_name() -> &'static [u8] {
    b"equality proof"
  }

  pub fn prove(
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    _v1: &Scalar,
    s1: &Scalar,
    _v2: &Scalar,
    s2: &Scalar,
  ) -> EqualityProof {
    transcript.append_protocol_name(EqualityProof::protocol_name());

    // produce a random Scalar
    let r = random_tape.random_scalar(b"r");
    let c = transcript.challenge_scalar(b"c");
    let z = c * (s1 - s2) + r;

    EqualityProof { z }
  }

  pub fn verify(&self, _transcript: &mut Transcript) -> Result<(), ProofVerifyError> {
    // TODO: Alternative PCS Verification
    Ok(())
  }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct ProductProof {
  z: [Scalar; 5],
}

impl ProductProof {
  fn protocol_name() -> &'static [u8] {
    b"product proof"
  }

  pub fn prove(
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x: &Scalar,
    rX: &Scalar,
    y: &Scalar,
    rY: &Scalar,
    _z: &Scalar,
    rZ: &Scalar,
  ) -> ProductProof {
    transcript.append_protocol_name(ProductProof::protocol_name());

    // produce five random Scalar
    let b1 = random_tape.random_scalar(b"b1");
    let b2 = random_tape.random_scalar(b"b2");
    let b3 = random_tape.random_scalar(b"b3");
    let b4 = random_tape.random_scalar(b"b4");
    let b5 = random_tape.random_scalar(b"b5");

    let c = transcript.challenge_scalar(b"c");

    let z1 = b1 + c * x;
    let z2 = b2 + c * rX;
    let z3 = b3 + c * y;
    let z4 = b4 + c * rY;
    let z5 = b5 + c * (rZ - rX * y);
    let z = [z1, z2, z3, z4, z5];

    ProductProof { z }
  }

  fn check_equality(_c: &Scalar, _z1: &Scalar, _z2: &Scalar) -> bool {
    // TODO: Alternative PCS Verification
    true
  }

  pub fn verify(&self, _transcript: &mut Transcript) -> Result<(), ProofVerifyError> {
    // TODO: Alternative PCS Verification
    Ok(())
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DotProductProof {
  z: Vec<Scalar>,
  z_delta: Scalar,
  z_beta: Scalar,
}

impl DotProductProof {
  fn protocol_name() -> &'static [u8] {
    b"dot product proof"
  }

  pub fn compute_dotproduct(a: &[Scalar], b: &[Scalar]) -> Scalar {
    assert_eq!(a.len(), b.len());
    (0..a.len()).map(|i| a[i] * b[i]).sum()
  }

  pub fn prove(
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_vec: &[Scalar],
    blind_x: &Scalar,
    a_vec: &[Scalar],
    _y: &Scalar,
    blind_y: &Scalar,
  ) -> DotProductProof {
    transcript.append_protocol_name(DotProductProof::protocol_name());

    let n = x_vec.len();
    assert_eq!(x_vec.len(), a_vec.len());

    // produce randomness for the proofs
    let d_vec = random_tape.random_vector(b"d_vec", n);
    let r_delta = random_tape.random_scalar(b"r_delta");
    let r_beta = random_tape.random_scalar(b"r_beta");

    let _dotproduct_a_d = DotProductProof::compute_dotproduct(a_vec, &d_vec);

    let c = transcript.challenge_scalar(b"c");

    let z = (0..d_vec.len())
      .map(|i| c * x_vec[i] + d_vec[i])
      .collect::<Vec<Scalar>>();

    let z_delta = c * blind_x + r_delta;
    let z_beta = c * blind_y + r_beta;

    DotProductProof { z, z_delta, z_beta }
  }

  pub fn verify(&self, transcript: &mut Transcript, a: &[Scalar]) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(DotProductProof::protocol_name());
    a.append_to_transcript(b"a", transcript);
    let _c = transcript.challenge_scalar(b"c");
    let _dotproduct_z_a = DotProductProof::compute_dotproduct(&self.z, a);

    // TODO: Alternative PCS Verification
    Ok(())
  }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DotProductProofLog {
  z1: Scalar,
  z2: Scalar,
}

impl DotProductProofLog {
  fn protocol_name() -> &'static [u8] {
    b"dot product proof (log)"
  }

  pub fn compute_dotproduct(a: &[Scalar], b: &[Scalar]) -> Scalar {
    assert_eq!(a.len(), b.len());
    (0..a.len()).map(|i| a[i] * b[i]).sum()
  }

  pub fn prove(
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_vec: &[Scalar],
    blind_x: &Scalar,
    a_vec: &[Scalar],
    _y: &Scalar,
    blind_y: &Scalar,
  ) -> DotProductProofLog {
    transcript.append_protocol_name(DotProductProofLog::protocol_name());

    let n = x_vec.len();
    assert_eq!(x_vec.len(), a_vec.len());

    // produce randomness for generating a proof
    let d = random_tape.random_scalar(b"d");
    let r_delta = random_tape.random_scalar(b"r_delta");
    let r_beta = random_tape.random_scalar(b"r_delta");
    let blinds_vec = {
      let v1 = random_tape.random_vector(b"blinds_vec_1", 2 * n.log_2());
      let v2 = random_tape.random_vector(b"blinds_vec_2", 2 * n.log_2());
      (0..v1.len())
        .map(|i| (v1[i], v2[i]))
        .collect::<Vec<(Scalar, Scalar)>>()
    };
    a_vec.append_to_transcript(b"a", transcript);

    // sample a random base and scale the generator used for
    // the output of the inner product
    let r = transcript.challenge_scalar(b"r");

    let blind_Gamma = blind_x + r * blind_y;
    let (x_hat, a_hat, rhat_Gamma) =
      BulletReductionProof::prove(transcript, x_vec, a_vec, &blind_Gamma, &blinds_vec);

    let y_hat = x_hat * a_hat;

    let c = transcript.challenge_scalar(b"c");

    let z1 = d + c * y_hat;
    let z2 = a_hat * (c * rhat_Gamma + r_beta) + r_delta;

    DotProductProofLog { z1, z2 }
  }

  pub fn verify(
    &self,
    _n: usize,
    _transcript: &mut Transcript,
    _a: &[Scalar],
  ) -> Result<(), ProofVerifyError> {
    // TODO: Alternative PCS Verification
    Ok(())
  }
}
