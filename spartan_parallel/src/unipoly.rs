use ff_ext::ExtensionField;
use super::transcript::{Transcript, append_scalar, append_message};
use serde::{Deserialize, Serialize};

// ax^2 + bx + c stored as vec![c,b,a]
// ax^3 + bx^2 + cx + d stored as vec![d,c,b,a]
#[derive(Debug)]
pub struct UniPoly<E: ExtensionField> {
  coeffs: Vec<E>,
}

// ax^2 + bx + c stored as vec![c,a]
// ax^3 + bx^2 + cx + d stored as vec![d,b,a]
#[derive(Serialize, Deserialize, Debug)]
pub struct CompressedUniPoly<E: ExtensionField> {
  coeffs_except_linear_term: Vec<E>,
}

impl<E: ExtensionField> UniPoly<E> {
  pub fn from_evals(evals: &[E]) -> Self {
    // we only support degree-2 or degree-3 univariate polynomials
    assert!(evals.len() == 3 || evals.len() == 4);
    let coeffs = if evals.len() == 3 {
      // ax^2 + bx + c
      let two_inv = E::from(2_u64).invert().unwrap();

      let c = evals[0];
      let a = two_inv * (evals[2] - evals[1] - evals[1] + c);
      let b = evals[1] - c - a;
      vec![c, b, a]
    } else {
      // ax^3 + bx^2 + cx + d
      let two_inv = E::from(2_u64).invert().unwrap();
      let six_inv = E::from(6_u64).invert().unwrap();

      let d = evals[0];
      let a = six_inv
        * (evals[3] - evals[2] - evals[2] - evals[2] + evals[1] + evals[1] + evals[1] - evals[0]);
      let b = two_inv
        * (evals[0] + evals[0] - evals[1] - evals[1] - evals[1] - evals[1] - evals[1]
          + evals[2]
          + evals[2]
          + evals[2]
          + evals[2]
          - evals[3]);
      let c = evals[1] - d - a - b;
      vec![d, c, b, a]
    };

    UniPoly { coeffs }
  }

  pub fn degree(&self) -> usize {
    self.coeffs.len() - 1
  }

  pub fn as_vec(&self) -> Vec<E> {
    self.coeffs.clone()
  }

  pub fn eval_at_zero(&self) -> E {
    self.coeffs[0]
  }

  pub fn eval_at_one(&self) -> E {
    (0..self.coeffs.len()).map(|i| self.coeffs[i]).sum()
  }

  pub fn evaluate(&self, r: &E) -> E {
    let mut eval = self.coeffs[0];
    let mut power = *r;
    for i in 1..self.coeffs.len() {
      eval = eval + power * self.coeffs[i];
      power = power * *r;
    }
    eval
  }

  pub fn compress(&self) -> CompressedUniPoly<E> {
    let coeffs_except_linear_term = [&self.coeffs[..1], &self.coeffs[2..]].concat();
    assert_eq!(coeffs_except_linear_term.len() + 1, self.coeffs.len());
    CompressedUniPoly {
      coeffs_except_linear_term,
    }
  }

  pub fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript<E>) {
    append_message(label, transcript, b"UniPoly_begin");
    for i in 0..self.coeffs.len() {
      append_scalar(b"coeff", transcript, self.coeffs[i]);
    }
    append_message(label, transcript, b"UniPoly_end");
  }
}

impl<E: ExtensionField> CompressedUniPoly<E> {
  // we require eval(0) + eval(1) = hint, so we can solve for the linear term as:
  // linear_term = hint - 2 * constant_term - deg2 term - deg3 term
  pub fn decompress(&self, hint: &E) -> UniPoly<E> {
    let mut linear_term =
      *hint - self.coeffs_except_linear_term[0] - self.coeffs_except_linear_term[0];
    for i in 1..self.coeffs_except_linear_term.len() {
      linear_term = linear_term - self.coeffs_except_linear_term[i];
    }

    let mut coeffs = vec![self.coeffs_except_linear_term[0], linear_term];
    coeffs.extend(&self.coeffs_except_linear_term[1..]);
    assert_eq!(self.coeffs_except_linear_term.len() + 1, coeffs.len());
    UniPoly { coeffs }
  }
}

/*
#[cfg(test)]
mod tests {
  use super::*;
  use crate::scalar::Scalar;

  #[test]
  fn test_from_evals_quad() {
    // polynomial is 2x^2 + 3x + 1
    let e0 = Scalar::one();
    let e1 = Scalar::from(6u64);
    let e2 = Scalar::from(15u64);
    let evals = vec![e0, e1, e2];
    let poly = UniPoly::from_evals(&evals);

    assert_eq!(poly.eval_at_zero(), e0);
    assert_eq!(poly.eval_at_one(), e1);
    assert_eq!(poly.coeffs.len(), 3);
    assert_eq!(poly.coeffs[0], Scalar::one());
    assert_eq!(poly.coeffs[1], Scalar::from(3_usize));
    assert_eq!(poly.coeffs[2], Scalar::from(2_usize));

    let hint = e0 + e1;
    let compressed_poly = poly.compress();
    let decompressed_poly = compressed_poly.decompress(&hint);
    for i in 0..decompressed_poly.coeffs.len() {
      assert_eq!(decompressed_poly.coeffs[i], poly.coeffs[i]);
    }

    let e3 = Scalar::from(28_usize);
    assert_eq!(poly.evaluate(&Scalar::from(3_usize)), e3);
  }

  #[test]
  fn test_from_evals_cubic() {
    // polynomial is x^3 + 2x^2 + 3x + 1
    let e0 = Scalar::one();
    let e1 = Scalar::from(7_usize);
    let e2 = Scalar::from(23_usize);
    let e3 = Scalar::from(55_usize);
    let evals = vec![e0, e1, e2, e3];
    let poly = UniPoly::from_evals(&evals);

    assert_eq!(poly.eval_at_zero(), e0);
    assert_eq!(poly.eval_at_one(), e1);
    assert_eq!(poly.coeffs.len(), 4);
    assert_eq!(poly.coeffs[0], Scalar::one());
    assert_eq!(poly.coeffs[1], Scalar::from(3_usize));
    assert_eq!(poly.coeffs[2], Scalar::from(2_usize));
    assert_eq!(poly.coeffs[3], Scalar::from(1_usize));

    let hint = e0 + e1;
    let compressed_poly = poly.compress();
    let decompressed_poly = compressed_poly.decompress(&hint);
    for i in 0..decompressed_poly.coeffs.len() {
      assert_eq!(decompressed_poly.coeffs[i], poly.coeffs[i]);
    }

    let e4 = Scalar::from(109_usize);
    assert_eq!(poly.evaluate(&Scalar::from(4_usize)), e4);
  }
}
*/