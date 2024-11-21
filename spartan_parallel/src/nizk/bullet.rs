//! This module is an adaptation of code from the bulletproofs crate.
//! See NOTICE.md for more details
#![allow(non_snake_case)]
#![allow(clippy::type_complexity)]
#![allow(clippy::too_many_arguments)]
use super::super::scalar::SpartanExtensionField;
use super::super::transcript::ProofTranscript;
use merlin::Transcript;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BulletReductionProof<S: SpartanExtensionField> {
  _phantom: S,
}

impl<S: SpartanExtensionField> BulletReductionProof<S> {
  /// Create an inner-product proof.
  ///
  /// The proof is created with respect to the bases \\(G\\).
  ///
  /// The `transcript` is passed in as a parameter so that the
  /// challenges depend on the *entire* transcript (including parent
  /// protocols).
  ///
  /// The lengths of the vectors must all be the same, and must all be
  /// either 0 or a power of 2.
  pub fn prove(
    transcript: &mut Transcript,
    a_vec: &[S],
    b_vec: &[S],
    blind: &S,
    blinds_vec: &[(S, S)],
  ) -> (S, S, S) {
    // Create slices G, H, a, b backed by their respective
    // vectors.  This lets us reslice as we compress the lengths
    // of the vectors in the main loop below.
    let mut a: &mut [S] = &mut a_vec.to_owned()[..];
    let mut b: &mut [S] = &mut b_vec.to_owned()[..];

    let mut blinds_iter = blinds_vec.iter();
    let mut blind_fin: S = *blind;

    let mut n = a.len();
    assert_eq!(a.len(), n);
    assert_eq!(b.len(), n);

    while n != 1 {
      n /= 2;
      let (a_L, a_R) = a.split_at_mut(n);
      let (b_L, b_R) = b.split_at_mut(n);

      let _c_L = inner_product(a_L, b_R);
      let _c_R = inner_product(a_R, b_L);

      let (blind_L, blind_R) = blinds_iter.next().unwrap();

      let u: S = transcript.challenge_scalar(b"u");
      let u_inv = u.invert().unwrap();

      for i in 0..n {
        a_L[i] = a_L[i] * u + u_inv * a_R[i];
        b_L[i] = b_L[i] * u_inv + u * b_R[i];
      }

      blind_fin = blind_fin + *blind_L * u * u + *blind_R * u_inv * u_inv;

      a = a_L;
      b = b_L;
    }

    (a[0], b[0], blind_fin)
  }
}

/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// Panics if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are not equal.
pub fn inner_product<S: SpartanExtensionField>(a: &[S], b: &[S]) -> S {
  assert!(
    a.len() == b.len(),
    "inner_product(a,b): lengths of vectors do not match"
  );
  let mut out = S::field_zero();
  for i in 0..a.len() {
    out = out + a[i] * b[i];
  }
  out
}
