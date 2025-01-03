#![allow(clippy::too_many_arguments)]
use core::{unimplemented, unreachable};
use std::cmp::min;

use crate::{dense_mlpoly::DensePolynomial, instance};
use ff::Field;
use ff_ext::ExtensionField;
use multilinear_extensions::mle::{FieldType, MultilinearExtension, DenseMultilinearExtension, RangedMultilinearExtension};
use std::{any::TypeId, borrow::Cow, mem, sync::Arc};

use super::math::Math;

const MODE_P: usize = 1;
const MODE_Q: usize = 2;
const MODE_W: usize = 3;
const MODE_X: usize = 4;

// Customized Dense ML Polynomials for Data-Parallelism
// These Dense ML Polys are aimed for space-efficiency by removing the 0s for invalid (p, q, w, x) quadruple

// Dense polynomial with variable order: p, q_rev, w, x_rev
// Used by Z_poly in r1csproof
#[derive(Debug, Clone)]
pub struct DensePolynomialPqx<E: ExtensionField> {
  num_instances: usize, // num_instances is a power of 2 and num_instances / 2 < Z.len() <= num_instances
  num_proofs: Vec<usize>,
  max_num_proofs: usize,
  pub num_witness_secs: usize, // num_witness_secs is a power of 2 and num_witness_secs / 2 < Z[.][.].len() <= num_witness_secs
  num_inputs: Vec<usize>,
  max_num_inputs: usize,
  pub Z: Vec<Vec<Vec<Vec<E>>>>, // Evaluations of the polynomial in all the 2^num_vars Boolean inputs of order (p, q_rev, w, x_rev)
                                // Let Q_max = max_num_proofs, assume that for a given P, num_proofs[P] = Q_i, then let STEP = Q_max / Q_i,
                                // Z(P, y, .) is only non-zero if y is a multiple of STEP, so Z[P][j][.] actually stores Z(P, j*STEP, .)
                                // The same applies to X
  pub dense_multilinear: Option<DenseMultilinearExtension<E>>,
}

// Reverse the bits in q or x
pub fn rev_bits(q: usize, max_num_proofs: usize) -> usize {
  (0..max_num_proofs.log_2())
    .rev()
    .map(|i| q / (i.pow2()) % 2 * (max_num_proofs / i.pow2() / 2))
    .fold(0, |a, b| a + b)
}

impl<E: ExtensionField> DensePolynomialPqx<E> {
  // Assume z_mat is of form (p, q_rev, x), construct DensePoly
  pub fn new(
    z_mat: Vec<Vec<Vec<Vec<E>>>>,
    num_proofs: Vec<usize>,
    max_num_proofs: usize,
    num_inputs: Vec<usize>,
    max_num_inputs: usize,
  ) -> Self {
    let num_instances = z_mat.len().next_power_of_two();
    let num_witness_secs = z_mat[0][0].len().next_power_of_two();
    let mut inst = DensePolynomialPqx {
      num_instances,
      num_proofs,
      max_num_proofs,
      num_witness_secs,
      num_inputs,
      max_num_inputs,
      Z: z_mat,
      dense_multilinear: None,
    };
    inst.fill_dense_Z_poly();
    inst
  }

  // Assume z_mat is in its standard form of (p, q, x)
  // Reverse q and x and convert it to (p, q_rev, x_rev)
  pub fn new_rev(
    z_mat: &Vec<Vec<Vec<Vec<E>>>>,
    num_proofs: Vec<usize>,
    max_num_proofs: usize,
    num_inputs: Vec<usize>,
    max_num_inputs: usize,
  ) -> Self {
    let mut Z = Vec::new();
    let num_instances = z_mat.len();
    let num_witness_secs = z_mat[0][0].len();
    for p in 0..num_instances {
      Z.push(vec![
        vec![
          vec![E::ZERO; num_inputs[p]];
          num_witness_secs
        ];
        num_proofs[p]
      ]);

      let step_q = max_num_proofs / num_proofs[p];
      let step_x = max_num_inputs / num_inputs[p];
      for q in 0..num_proofs[p] {
        // Reverse the bits of q. q_rev is a multiple of step_q
        let q_rev = rev_bits(q, max_num_proofs);
        // Now q_rev is between 0 to num_proofs[p]
        let q_rev = q_rev / step_q;

        for x in 0..num_inputs[p] {
          // Reverse the bits of x. x_rev is a multiple of step_x
          let x_rev = rev_bits(x, max_num_inputs);
          // Now x_rev is between 0 to num_inputs[p]
          let x_rev = x_rev / step_x;
          for w in 0..num_witness_secs {
            Z[p][q_rev][w][x_rev] = z_mat[p][q][w][x];
          }
        }
      }
    }
    let mut inst = DensePolynomialPqx {
      num_instances: num_instances.next_power_of_two(),
      num_proofs,
      max_num_proofs,
      num_witness_secs: num_witness_secs.next_power_of_two(),
      num_inputs,
      max_num_inputs,
      Z,
      dense_multilinear: None,
    };
    inst.fill_dense_Z_poly();
    inst
  }

  pub fn len(&self) -> usize {
    return self.num_instances * self.max_num_proofs * self.max_num_inputs;
  }

  // Given (p, q_rev, x_rev) return Z[p][q_rev][x_rev]
  pub fn index(&self, p: usize, q_rev: usize, w: usize, x_rev: usize) -> E {
    if p < self.Z.len()
      && q_rev < self.Z[p].len()
      && w < self.Z[p][q_rev].len()
      && x_rev < self.Z[p][q_rev][w].len()
    {
      return self.Z[p][q_rev][w][x_rev];
    } else {
      return E::ZERO;
    }
  }

  // Given (p, q_rev, w, x_rev) and a mode, return Z[p*][q_rev*][w*][x_rev*]
  // Mode = 1 ==> p* is p with first bit set to 1
  // Mode = 2 ==> q_rev* is q_rev with first bit set to 1
  // Mode = 3 ==> w* is w with first bit set to 1
  // Mode = 4 ==> x_rev* is x_rev with first bit set to 1
  // Assume that first bit of the corresponding index is 0, otherwise throw out of bound exception
  pub fn index_high(&self, p: usize, q_rev: usize, w: usize, x_rev: usize, mode: usize) -> E {
    match mode {
      MODE_P => {
        if p + self.num_instances / 2 < self.Z.len() {
          return self.Z[p + self.num_instances / 2][q_rev][w][x_rev];
        } else {
          return E::ZERO;
        }
      }
      MODE_Q => {
        return if self.num_proofs[p] == 1 {
          E::ZERO
        } else {
          self.Z[p][q_rev + self.num_proofs[p] / 2][w][x_rev]
        };
      }
      MODE_W => {
        if w + self.num_witness_secs / 2 < self.Z[p][q_rev].len() {
          return self.Z[p][q_rev][w + self.num_witness_secs / 2][x_rev];
        } else {
          return E::ZERO;
        }
      }
      MODE_X => {
        return if self.num_inputs[p] == 1 {
          E::ZERO
        } else {
          self.Z[p][q_rev][w][x_rev + self.num_inputs[p] / 2]
        };
      }
      _ => {
        panic!(
          "DensePolynomialPqx bound failed: unrecognized mode {}!",
          mode
        );
      }
    }
  }

  // Bound a variable to r according to mode
  // Mode = 1 ==> Bound first variable of "p" section to r
  // Mode = 2 ==> Bound first variable of "q" section to r
  // Mode = 3 ==> Bound first variable of "w" section to r
  // Mode = 4 ==> Bound first variable of "x" section to r
  pub fn bound_poly(&mut self, r: &E, mode: usize) {
    match mode {
      MODE_P => {
        self.bound_poly_p(r);
      }
      MODE_Q => {
        self.bound_poly_q(r);
      }
      MODE_W => {
        self.bound_poly_w(r);
      }
      MODE_X => {
        self.bound_poly_x(r);
      }
      _ => {
        panic!(
          "DensePolynomialPqx bound failed: unrecognized mode {}!",
          mode
        );
      }
    }
  }

  // Bound the first variable of "p" section to r
  // We are only allowed to bound "p" if we have bounded the entire q and x section
  pub fn bound_poly_p(&mut self, r: &E) {
    assert_eq!(self.max_num_proofs, 1);
    assert_eq!(self.max_num_inputs, 1);
    self.num_instances /= 2;
    for p in 0..self.num_instances {
      for w in 0..min(self.num_witness_secs, self.Z[p][0].len()) {
        let Z_high = if p + self.num_instances < self.Z.len() {
          self.Z[p + self.num_instances][0][w][0]
        } else {
          E::ZERO
        };
        self.Z[p][0][w][0] = self.Z[p][0][w][0] + *r * (Z_high - self.Z[p][0][w][0]);
      }
    }
  }

  // Bound the first variable of "q" section to r
  pub fn bound_poly_q(&mut self, r: &E) {
    self.max_num_proofs /= 2;

    for p in 0..min(self.num_instances, self.Z.len()) {
      if self.num_proofs[p] == 1 {
        for w in 0..min(self.num_witness_secs, self.Z[p][0].len()) {
          for x in 0..self.num_inputs[p] {
            self.Z[p][0][w][x] = (E::ONE - *r) * self.Z[p][0][w][x];
          }
        }
      } else {
        self.num_proofs[p] /= 2;
        for q in 0..self.num_proofs[p] {
          for w in 0..min(self.num_witness_secs, self.Z[p][q].len()) {
            for x in 0..self.num_inputs[p] {
              self.Z[p][q][w][x] = self.Z[p][q][w][x]
                + *r * (self.Z[p][q + self.num_proofs[p]][w][x] - self.Z[p][q][w][x]);
            }
          }
        }
      }
    }
  }

  // Bound the first variable of "w" section to r
  pub fn bound_poly_w(&mut self, r: &E) {
    self.num_witness_secs /= 2;

    for p in 0..min(self.num_instances, self.Z.len()) {
      for q in 0..self.num_proofs[p] {
        for w in 0..self.num_witness_secs {
          for x in 0..self.num_inputs[p] {
            let Z_high = if w + self.num_witness_secs < self.Z[p][q].len() {
              self.Z[p][q][w + self.num_witness_secs][x]
            } else {
              E::ZERO
            };
            self.Z[p][q][w][x] = self.Z[p][q][w][x] + *r * (Z_high - self.Z[p][q][w][x]);
          }
        }
      }
    }
  }

  // Bound the first variable of "x" section to r
  pub fn bound_poly_x(&mut self, r: &E) {
    self.max_num_inputs /= 2;

    for p in 0..min(self.num_instances, self.Z.len()) {
      if self.num_inputs[p] == 1 {
        for q in 0..self.num_proofs[p] {
          for w in 0..min(self.num_witness_secs, self.Z[p][q].len()) {
            self.Z[p][q][w][0] = (E::ONE - *r) * self.Z[p][q][w][0];
          }
        }
      } else {
        self.num_inputs[p] /= 2;
        for q in 0..self.num_proofs[p] {
          for w in 0..min(self.num_witness_secs, self.Z[p][q].len()) {
            for x in 0..self.num_inputs[p] {
              self.Z[p][q][w][x] = self.Z[p][q][w][x]
                + *r * (self.Z[p][q][w][x + self.num_inputs[p]] - self.Z[p][q][w][x]);
            }
          }
        }
      }
    }
  }

  // Bound the entire "p" section to r_p
  // Must occur after r_q's are bounded
  pub fn bound_poly_vars_rp(&mut self, r_p: &Vec<E>) {
    for r in r_p {
      self.bound_poly_p(r);
    }
  }

  // Bound the entire "q_rev" section to r_q
  pub fn bound_poly_vars_rq(&mut self, r_q: &Vec<E>) {
    for r in r_q {
      self.bound_poly_q(r);
    }
  }

  // Bound the entire "w" section to r_w
  pub fn bound_poly_vars_rw(&mut self, r_w: &Vec<E>) {
    for r in r_w {
      self.bound_poly_w(r);
    }
  }

  // Bound the entire "x_rev" section to r_x
  pub fn bound_poly_vars_rx(&mut self, r_x: &Vec<E>) {
    for r in r_x {
      self.bound_poly_x(r);
    }
  }

  pub fn flattened_len(&self) -> usize {
    self.num_instances * self.max_num_proofs * self.num_witness_secs * self.max_num_inputs
  }

  pub fn num_flattened_vars(&self) -> usize {
    self.flattened_len().log_2()
  }

  pub fn evaluate(&self, r_p: &Vec<E>, r_q: &Vec<E>, r_w: &Vec<E>, r_x: &Vec<E>) -> E {
    let mut cl = self.clone();
    cl.bound_poly_vars_rx(r_x);
    cl.bound_poly_vars_rw(r_w);
    cl.bound_poly_vars_rq(r_q);
    cl.bound_poly_vars_rp(r_p);
    cl.index(0, 0, 0, 0)
  }

  fn fill_dense_Z_poly(&mut self) {
    let mut Z_poly =
      vec![
        E::ZERO;
        self.flattened_len()
      ];
    for p in 0..min(self.num_instances, self.Z.len()) {
      let step_q = self.max_num_proofs / self.num_proofs[p];
      let step_x = self.max_num_inputs / self.num_inputs[p];
      for q_rev in 0..self.num_proofs[p] {
        let q = rev_bits(q_rev * step_q, self.max_num_proofs);
        for x_rev in 0..self.num_inputs[p] {
          let x = rev_bits(x_rev * step_x, self.max_num_inputs);
          for w in 0..min(self.num_witness_secs, self.Z[p][q_rev].len()) {
            Z_poly[p * self.max_num_proofs * self.num_witness_secs * self.max_num_inputs
              + q * self.num_witness_secs * self.max_num_inputs
              + w * self.max_num_inputs
              + x] = self.Z[p][q_rev][w][x_rev];
          }
        }
      }
    }

    self.dense_multilinear = Some(DenseMultilinearExtension::from_evaluations_ext_vec(Z_poly.len().log_2(), Z_poly));
  }

  // Convert to Ceno prover compatible multilinear poly
  pub fn to_dense_poly(&self) -> DensePolynomial<E> {
    match self.evaluations() {
      FieldType::Ext(v) => DensePolynomial::new(v.to_vec()),
      _ => { unreachable!() }
    }
  }

  // Convert to Ceno prover compatible multilinear poly
  pub fn to_ceno_multilinear(&self) -> DenseMultilinearExtension<E> {
    match self.evaluations() {
      FieldType::Ext(v) => DenseMultilinearExtension::from_evaluations_ext_vec(v.len().log_2(), v.to_vec()),
      _ => { unreachable!() }
    }
  }
}

impl<E: ExtensionField> MultilinearExtension<E> for DensePolynomialPqx<E> {
  type Output = DenseMultilinearExtension<E>;
  /// Reduce the number of variables of `self` by fixing the
  /// `partial_point.len()` variables at `partial_point`.
  fn fix_variables(&self, partial_point: &[E]) -> Self::Output {
      // TODO: return error.
      assert!(
          partial_point.len() <= self.num_vars(),
          "invalid size of partial point"
      );

      let mut poly = self.clone();

      for point in partial_point.iter() {
        poly.fix_variables_in_place(&[*point])
      }
      assert!(poly.num_flattened_vars() == self.num_flattened_vars() - partial_point.len(),);
      poly.to_ceno_multilinear()
  }

  /// Reduce the number of variables of `self` by fixing the
  /// `partial_point.len()` variables at `partial_point` in place
  fn fix_variables_in_place(&mut self, partial_point: &[E]) {
      // TODO: return error.
      assert!(
        partial_point.len() <= self.num_flattened_vars(),
        "partial point len {} >= num_vars {}",
        partial_point.len(),
        self.num_flattened_vars()
      );

      let mut instance_vars = self.num_instances.log_2();
      let mut proofs_vars = self.max_num_proofs.log_2();
      let mut witness_secs_vars = self.num_witness_secs.log_2();
      let mut input_vars = self.max_num_inputs.log_2();

      for point in partial_point.iter() {
        if input_vars > 0 {
          self.bound_poly_vars_rx(&vec![*point]);
          input_vars /= 2;
        } else if witness_secs_vars > 0 {
          self.bound_poly_vars_rw(&vec![*point]);
          witness_secs_vars /= 2;
        } else if proofs_vars > 0 {
          self.bound_poly_vars_rq(&vec![*point]);
          proofs_vars /= 2;
        } else {
          self.bound_poly_vars_rp(&vec![*point]);
          instance_vars /= 2;
        }
      }
  }

  /// Reduce the number of variables of `self` by fixing the
  /// `partial_point.len()` variables at `partial_point` from high position
  fn fix_high_variables(&self, _partial_point: &[E]) -> Self::Output {
      unimplemented!()
  }

  /// Reduce the number of variables of `self` by fixing the
  /// `partial_point.len()` variables at `partial_point` from high position in place
  fn fix_high_variables_in_place(&mut self, _partial_point: &[E]) {
      unimplemented!()
  }

  /// Evaluate the MLE at a give point.
  /// Returns an error if the MLE length does not match the point.
  fn evaluate(&self, point: &[E]) -> E {
      // TODO: return error.
      assert_eq!(
          self.num_vars(),
          point.len(),
          "MLE size does not match the point"
      );
      let mle = self.fix_variables_parallel(point);
      
      if let Some(f) = &self.dense_multilinear {
        match &f.evaluations {
          FieldType::Ext(v) => v[0],
          _ => unreachable!()
        }
      } else {
        unreachable!()
      }
  }

  fn num_vars(&self) -> usize {
      self.num_flattened_vars()
  }

  /// Reduce the number of variables of `self` by fixing the
  /// `partial_point.len()` variables at `partial_point`.
  fn fix_variables_parallel(&self, partial_point: &[E]) -> Self::Output {
      self.fix_variables(partial_point)
  }

  /// Reduce the number of variables of `self` by fixing the
  /// `partial_point.len()` variables at `partial_point` in place
  fn fix_variables_in_place_parallel(&mut self, partial_point: &[E]) {
    self.fix_variables_in_place(partial_point);
  }

  fn evaluations(&self) -> &FieldType<E> {
    &self.dense_multilinear.as_ref().unwrap().evaluations
  }

  fn evaluations_to_owned(self) -> FieldType<E> {
    unimplemented!()
  }

  fn evaluations_range(&self) -> Option<(usize, usize)> {
      None
  }

  fn name(&self) -> &'static str {
      "DensePolynomialPqx"
  }

  /// assert and get base field vector
  /// panic if not the case
  fn get_base_field_vec(&self) -> &[E::BaseField] {
    if let Some(f) = &self.dense_multilinear {
      match &f.evaluations {
        FieldType::Base(evaluations) => &evaluations[..],
        _ => unreachable!(),
      }
    } else {
      unreachable!()
    }
  }

  fn merge(&mut self, _rhs: DenseMultilinearExtension<E>) {
      unimplemented!()
  }

  /// get ranged multiliear extention
  fn get_ranged_mle(
      &self,
      num_range: usize,
      range_index: usize,
  ) -> RangedMultilinearExtension<'_, E> {
      assert!(num_range > 0);
      // ranged_mle is exclusively used in multi-thread parallelism
      // The number of ranges must be a power of 2
      assert!(num_range.next_power_of_two() == num_range);
      let offset = self.evaluations().len() / num_range;
      let start = offset * range_index;
      RangedMultilinearExtension::new(self.dense_multilinear.as_ref().unwrap(), start, offset)
  }

  /// resize to new size (num_instances * new_size_per_instance / num_range)
  /// and selected by range_index
  /// only support resize base fields, otherwise panic
  fn resize_ranged(
      &self,
      _num_instances: usize,
      _new_size_per_instance: usize,
      _num_range: usize,
      _range_index: usize,
  ) -> Self::Output {
      unimplemented!()
  }

  /// dup to new size 1 << (self.num_vars + ceil_log2(num_dups))
  fn dup(&self, _num_instances: usize, _num_dups: usize) -> Self::Output {
      unimplemented!()
  }
}
