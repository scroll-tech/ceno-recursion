#![allow(clippy::too_many_arguments)]
use ff_ext::ExtensionField;
use multilinear_extensions::mle::DenseMultilinearExtension;

use super::errors::ProofVerifyError;
use super::math::Math;
use super::random::RandomTape;
use super::transcript::Transcript;
use core::ops::Index;
use rayon::{iter::ParallelIterator, slice::ParallelSliceMut};
use serde::{Deserialize, Serialize};
use std::cmp::min;

pub struct EqPolynomial<E: ExtensionField> {
  r: Vec<E>,
}

impl<E: ExtensionField> EqPolynomial<E> {
  pub fn new(r: Vec<E>) -> Self {
    EqPolynomial { r }
  }

  pub fn evaluate(&self, rx: &[E]) -> E {
    assert_eq!(self.r.len(), rx.len());
    (0..rx.len())
      .map(|i| self.r[i] * rx[i] + (E::ONE - self.r[i]) * (E::ONE - rx[i]))
      .product()
  }

  pub fn evals(&self) -> Vec<E> {
    let ell = self.r.len();

    let mut evals: Vec<E> = vec![E::ONE; ell.pow2()];
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
  pub fn evals_front(&self, total_len: usize) -> Vec<E> {
    let ell = self.r.len();

    let mut evals: Vec<E> = vec![E::ONE; total_len.pow2()];
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

  pub fn compute_factored_evals(&self) -> (Vec<E>, Vec<E>) {
    let ell = self.r.len();
    let (left_num_vars, _right_num_vars) = EqPolynomial::<E>::compute_factored_lens(ell);

    let L = EqPolynomial::new(self.r[..left_num_vars].to_vec()).evals();
    let R = EqPolynomial::new(self.r[left_num_vars..ell].to_vec()).evals();

    (L, R)
  }
}
pub struct IdentityPolynomial<E: ExtensionField> {
  size_point: usize,
  _phantom: E,
}

impl<E: ExtensionField> IdentityPolynomial<E> {
  pub fn new(size_point: usize) -> Self {
    IdentityPolynomial {
      size_point,
      _phantom: E::ZERO,
    }
  }

  pub fn evaluate(&self, r: &[E]) -> E {
    let len = r.len();
    assert_eq!(len, self.size_point);
    (0..len)
      .map(|i| E::from((len - i - 1).pow2() as u64) * r[i])
      .sum()
  }
}