#![allow(clippy::too_many_arguments)]
use std::cmp::min;
use std::{any::TypeId, borrow::Cow, mem, sync::Arc};

use crate::dense_mlpoly::DensePolynomial;
use crate::math::Math;
use ff_ext::ExtensionField;
use multilinear_extensions::mle::{MultilinearExtension, DenseMultilinearExtension};
use rayon::prelude::*;

const MODE_P: usize = 1;
const MODE_Q: usize = 2;
const MODE_W: usize = 3;
const MODE_X: usize = 4;

// Customized Dense ML Polynomials for Data-Parallelism
// These Dense ML Polys are aimed for space-efficiency by removing the 0s for invalid (p, q, w, x) quadruple

// Dense polynomial with variable order: p, q, w, x
// Used by Z_poly in r1csproof
#[derive(Debug, Clone, Hash)]
pub struct DensePolynomialPqx<E: ExtensionField> {
  // All metadata might not be a power of 2
  pub num_instances: usize,
  pub num_proofs: Vec<usize>, // P
  pub num_witness_secs: usize,
  pub num_inputs: Vec<Vec<usize>>, // P x W
  pub num_vars_p: usize, // log(P.next_power_of_two())
  pub num_vars_q: usize,
  pub num_vars_w: usize,
  pub num_vars_x: usize,
  pub Z: Vec<Vec<Vec<Vec<E>>>>, // Evaluations of the polynomial in all the 2^num_vars Boolean inputs of order (p, q, w, x)
}

fn fold_rq<E: ExtensionField>(proofs: &mut [Vec<Vec<E>>], r_q: &[E], step: usize, mut q: usize, w: usize, x: &Vec<usize>) {
  for r in r_q {
    let r1 = E::ONE - r.clone();
    let r2 = r.clone();

    q = q.div_ceil(2);
    (0..q).for_each(|q| {
      (0..w).for_each(|w| {
        (0..x[w]).for_each(|x| {
          proofs[q * step][w][x] = r1 * proofs[2 * q * step][w][x] + r2 * proofs[(2 * q + 1) * step][w][x];
        });
      });
    });
  }
}

impl<E: ExtensionField> DensePolynomialPqx<E> {
  // Assume z_mat is of form (p, q_rev, x), construct DensePoly
  pub fn new(
    z_mat: Vec<Vec<Vec<Vec<E>>>>, 
  ) -> Self {
    let num_instances = z_mat.len();
    let num_proofs: Vec<usize> = (0..num_instances).map(|p| z_mat[p].len()).collect();
    let num_witness_secs = z_mat[0][0].len();
    let num_inputs: Vec<Vec<usize>> = (0..num_instances).map(|p| 
      (0..num_witness_secs).map(|w| z_mat[p][0][w].len()).collect()
    ).collect();
    // Sortedness check: num_proofs and num_inputs[p] are sorted in decreasing order
    assert!((0..num_instances - 1).fold(true, |b, i| b && num_proofs[i] >= num_proofs[i + 1]));
    for w in &num_inputs {
      assert!((0..num_witness_secs - 1).fold(true, |b, i| b && w[i] >= w[i + 1]));
    }

    let num_vars_p = num_instances.next_power_of_two().log_2();
    let num_vars_q = num_proofs.iter().max().unwrap().next_power_of_two().log_2();
    let num_vars_w = num_witness_secs.next_power_of_two().log_2();
    let num_vars_x = num_inputs.iter().map(|i| i.iter().max().unwrap()).max().unwrap().next_power_of_two().log_2();
    DensePolynomialPqx {
      num_instances,
      num_proofs,
      num_witness_secs,
      num_inputs,
      num_vars_p,
      num_vars_q,
      num_vars_w,
      num_vars_x,
      Z: z_mat,
    }
  }

  pub fn len(&self) -> usize {
    return self.num_vars_p.pow2() * self.num_vars_q.pow2() * self.num_vars_w.pow2() * self.num_vars_x.pow2();
  }

  // Given (p, q, w, x) return Z[p][q][w][x], DO NOT CHECK FOR OUT OF BOUND
  pub fn index(&self, p: usize, q: usize, w: usize, x: usize) -> E {
    return self.Z[p][q][w][x];
  }

  // Given (p, q, w, x) and a mode, return Z[p*][q*][w*][x*]
  // Mode = 1 ==> p* = 2p for low, 2p + 1 for high
  // Mode = 2 ==> q* = 2q for low, 2q + 1
  // Mode = 3 ==> w* = 2w for low, 2w + 1
  // Mode = 4 ==> x* = 2x for low, 2x + 1
  // Assume p*, q*, w*, x* are within bound
  pub fn index_low(&self, p: usize, q: usize, w: usize, x: usize, mode: usize) -> E {
    let ZERO = E::ZERO;
    match mode {
      MODE_P => { if self.num_instances == 1 { self.Z[0][q][w][x] } else if 2 * p >= self.num_instances { ZERO } else { self.Z[2 * p][q][w][x] } }
      MODE_Q => { if 2 * q >= self.num_proofs[p] { ZERO } else { self.Z[p][2 * q][w][x] } },
      MODE_W => { if 2 * w >= self.num_witness_secs { ZERO } else { self.Z[p][q][2 * w][x] } }
      MODE_X => { if 2 * x >= self.num_inputs[p][w] { ZERO } else { self.Z[p][q][w][2 * x] } },
      _ => unreachable!()
    }
  }
  pub fn index_high(&self, p: usize, q: usize, w: usize, x: usize, mode: usize) -> E {
    let ZERO = E::ZERO;
    match mode {
      MODE_P => { if self.num_instances == 1 { self.Z[0][q][w][x] } else if 2 * p + 1 >= self.num_instances { ZERO } else { self.Z[2 * p + 1][q][w][x] } }
      MODE_Q => { if 2 * q + 1 >= self.num_proofs[p] { ZERO } else { self.Z[p][2 * q + 1][w][x] } }
      MODE_W => { if 2 * w + 1 >= self.num_witness_secs { ZERO } else { self.Z[p][q][2 * w + 1][x] } }
      MODE_X => { if 2 * x + 1 >= self.num_inputs[p][w] { ZERO } else { self.Z[p][q][w][2 * x + 1] } }
      _ => unreachable!()
    }
  }

  // Bound a variable to r according to mode
  // Mode = 1 ==> Bound last variable of "p" section to r
  // Mode = 2 ==> Bound last variable of "q" section to r
  // Mode = 3 ==> Bound last variable of "w" section to r
  // Mode = 4 ==> Bound last variable of "x" section to r
  pub fn bound_poly(&mut self, r: &E, mode: usize) {
    match mode {
        MODE_P => { self.bound_poly_p(r); }
        MODE_Q => { self.bound_poly_q(r); }
        MODE_W => { self.bound_poly_w(r); }
        MODE_X => { self.bound_poly_x(r); }
        _ => { panic!("DensePolynomialPqx bound failed: unrecognized mode {}!", mode); }
    }
  }

  // Bound the last variable of "p" section to r
  // We are only allowed to bound "p" if we have bounded the entire q and x section
  pub fn bound_poly_p(&mut self, r: &E) {
    assert!(self.num_vars_p >= 1);
    assert_eq!(self.num_vars_q, 0);
    assert_eq!(self.num_vars_x, 0);
    let new_num_instances = self.num_instances.div_ceil(2);
    for p in 0..new_num_instances {
      for w in 0..self.num_witness_secs {
        let Z_low = self.index_low(p, 0, w, 0, MODE_P);
        let Z_high = self.index_high(p, 0, w, 0, MODE_P);
        self.Z[p][0][w][0] = Z_low + r.clone() * (Z_high - Z_low);
      }
    }
    self.num_instances = new_num_instances;
    self.num_vars_p -= 1;
  }

  // Bound the last variable of "q" section to r
  pub fn bound_poly_q(&mut self, r: &E) {
    assert!(self.num_vars_q >= 1);
    for p in 0..self.num_instances {
      let new_num_proofs = self.num_proofs[p].div_ceil(2);
      for q in 0..new_num_proofs {
        for w in 0..self.num_witness_secs {
          for x in 0..self.num_inputs[p][w] {
            let Z_low = self.index_low(p, q, w, x, MODE_Q);
            let Z_high = self.index_high(p, q, w, x, MODE_Q);
            self.Z[p][q][w][x] = Z_low + r.clone() * (Z_high - Z_low);
          }
        }
      }
      self.num_proofs[p] = new_num_proofs;
    }
    self.num_vars_q -= 1;
  }

  // Bound the last variable of "w" section to r
  // We are only allowed to bound "w" if we have bounded the entire x section
  pub fn bound_poly_w(&mut self, r: &E) {
    assert!(self.num_vars_w >= 1);
    assert_eq!(self.num_vars_x, 0);
    let new_num_witness_secs = self.num_witness_secs.div_ceil(2);
    for p in 0..self.num_instances {
      for q in 0..self.num_proofs[p] {
        for w in 0..new_num_witness_secs {
          let Z_low = self.index_low(p, q, w, 0, MODE_W);
          let Z_high = self.index_high(p, q, w, 0, MODE_W);
          self.Z[p][q][w][0] = Z_low + r.clone() * (Z_high - Z_low);
        }
      }
    }
    self.num_witness_secs = new_num_witness_secs;
    self.num_vars_w -= 1;
}

  // Bound the last variable of "x" section to r
  pub fn bound_poly_x(&mut self, r: &E) {
    // assert!(self.num_vars_x >= 1);
    for p in 0..self.num_instances {
      for w in 0..self.num_witness_secs {
        let new_num_inputs = self.num_inputs[p][w].div_ceil(2);
        for q in 0..self.num_proofs[p] {
          for x in 0..new_num_inputs {
            let Z_low = self.index_low(p, q, w, x, MODE_X);
            let Z_high = self.index_high(p, q, w, x, MODE_X);
            self.Z[p][q][w][x] = Z_low + r.clone() * (Z_high - Z_low);
          }
        }
        self.num_inputs[p][w] = new_num_inputs;
      }
    }
    if self.num_vars_x >= 1 {
      self.num_vars_x -= 1;
    }
  }

  // Bound the entire "p" section to r_p in reverse
  // Must occur after r_q's are bounded
  pub fn bound_poly_vars_rp(&mut self, r_p: &[E]) {
    for r in r_p {
      self.bound_poly_p(r);
    }
  }

  // Bound the entire "q" section to r_q in reverse
  pub fn bound_poly_vars_rq_parallel(
    &mut self, 
    r_q: &[E],
  ) {
    let Z = std::mem::take(&mut self.Z);

    self.Z = Z
      .into_iter()
      .enumerate()
      .map(|(p, mut inst)| {
        let num_proofs = self.num_proofs[p];
        let dist_size = num_proofs / min(num_proofs, rayon::current_num_threads().next_power_of_two()); // distributed number of proofs on each thread
        let num_threads = num_proofs / dist_size;

        // To perform rigorous parallelism, both num_proofs and # threads must be powers of 2
        // # threads must fully divide num_proofs for even distribution
        assert_eq!(num_proofs, num_proofs.next_power_of_two());
        assert_eq!(num_threads, num_threads.next_power_of_two());

        // Determine parallelism levels
        let levels = num_proofs.log_2(); // total layers
        let sub_levels = dist_size.log_2(); // parallel layers
        let final_levels = num_threads.log_2(); // single core final layers
        let left_over_q_len = r_q.len() - levels; // if r_q.len() > log2(num_proofs)

        // single proof matrix dimension W x X
        let num_witness_secs = min(self.num_witness_secs, inst[0].len());
        let num_inputs = &self.num_inputs[p];

        // Divide rq into sub, final, and left_over
        let sub_rq = &r_q[0..sub_levels];
        let final_rq = &r_q[sub_levels..levels];
        let left_over_rq = &r_q[(r_q.len() - left_over_q_len)..r_q.len()];

        if sub_levels > 0 {
          inst = inst
            .par_chunks_mut(dist_size)
            .map(|chunk| {
              fold_rq(chunk, sub_rq, 1, dist_size, num_witness_secs, num_inputs);
              chunk.to_vec()
            })
            .flatten().collect()
        }

        if final_levels > 0 {
          // aggregate the final result from sub-threads outputs using a single core
          fold_rq(&mut inst, final_rq, dist_size, num_threads, num_witness_secs, num_inputs);
        }

        if left_over_q_len > 0 {
          // the series of random challenges exceeds the total number of variables
          let c = left_over_rq.into_iter().fold(E::ONE, |acc, n| acc * (E::ONE - *n));
          for w in 0..inst[0].len() {
            for x in 0..inst[0][w].len() {
              inst[0][w][x] *= c;
            }
          }
        }

        inst
      }).collect::<Vec<Vec<Vec<Vec<E>>>>>();

    self.num_vars_q = 0;
    self.num_proofs = vec![1; self.num_instances];
  }

  // Bound the entire "q" section to r_q in reverse
  pub fn bound_poly_vars_rq(&mut self, r_q: &[E]) {
    for r in r_q {
      self.bound_poly_q(r);
    }
  }

  // Bound the entire "w" section to r_w in reverse
  pub fn bound_poly_vars_rw(&mut self, r_w: &[E]) {
    for r in r_w {
      self.bound_poly_w(r);
    }
  }

  // Bound the entire "x_rev" section to r_x
  pub fn bound_poly_vars_rx(&mut self, r_x: &[E]) {
    for r in r_x {
      self.bound_poly_x(r);
    }
  }

  pub fn evaluate(&self,
    rp_rev: &Vec<E>,
    rq_rev: &Vec<E>,
    rw_rev: &Vec<E>,
    rx_rev: &Vec<E>,
  ) -> E {
    let mut cl = self.clone();
    cl.bound_poly_vars_rx(rx_rev);
    cl.bound_poly_vars_rw(rw_rev);
    cl.bound_poly_vars_rq(rq_rev);
    cl.bound_poly_vars_rp(rp_rev);
    return cl.index(0, 0, 0, 0);
  }

  // Convert to a (p, q_rev, x_rev) regular dense poly of form (p, q, x)
  pub fn to_dense_poly(&self) -> DensePolynomial<E> {
    let ZERO = E::ZERO;

    let p_space = self.num_vars_p.pow2();
    let q_space = self.num_vars_q.pow2();
    let w_space = self.num_vars_w.pow2();
    let x_space = self.num_vars_x.pow2();

    let mut Z_poly = vec![ZERO; p_space * q_space * w_space * x_space];
    for p in 0..self.num_instances {
      for q in 0..self.num_proofs[p] {
        for w in 0..self.num_witness_secs {
          for x in 0..self.num_inputs[p][w] {
              Z_poly[
                  p * q_space * w_space * x_space
                + q * w_space * x_space
                + w * x_space
                + x
              ] = self.Z[p][q][w][x];
          }
        }
      }
    }
    DensePolynomial::new(Z_poly)
  }
}

impl<E: ExtensionField> MultilinearExtension<E> for DensePolynomialPqx<E> {
  type Output = DenseMultilinearExtension<E>;
  /// Reduce the number of variables of `self` by fixing the
  /// `partial_point.len()` variables at `partial_point`.
  fn fix_variables(&self, partial_point: &[E]) -> Self {
      // TODO: return error.
      assert!(
          partial_point.len() <= self.num_vars(),
          "invalid size of partial point"
      );
      let mut poly = Cow::Borrowed(self);

      // evaluate single variable of partial point from left to right
      // `Cow` type here to skip first evaluation vector copy
      for point in partial_point.iter() {
          match &mut poly {
              poly @ Cow::Borrowed(_) => {
                  *poly = op_mle!(self, |evaluations| {
                      Cow::Owned(DenseMultilinearExtension::from_evaluations_ext_vec(
                          self.num_vars() - 1,
                          evaluations
                              .chunks(2)
                              .map(|buf| *point * (buf[1] - buf[0]) + buf[0])
                              .collect(),
                      ))
                  });
              }
              Cow::Owned(poly) => poly.fix_variables_in_place(&[*point]),
          }
      }
      assert!(poly.num_vars == self.num_vars() - partial_point.len(),);
      poly.into_owned()
  }

  /// Reduce the number of variables of `self` by fixing the
  /// `partial_point.len()` variables at `partial_point` in place
  fn fix_variables_in_place(&mut self, partial_point: &[E]) {
      // TODO: return error.
      assert!(
          partial_point.len() <= self.num_vars(),
          "partial point len {} >= num_vars {}",
          partial_point.len(),
          self.num_vars()
      );
      let nv = self.num_vars();
      // evaluate single variable of partial point from left to right
      for point in partial_point.iter() {
          // override buf[b1, b2,..bt, 0] = (1-point) * buf[b1, b2,..bt, 0] + point * buf[b1,
          // b2,..bt, 1] in parallel
          match &mut self.evaluations {
              FieldType::Base(evaluations) => {
                  let evaluations_ext = evaluations
                      .chunks(2)
                      .map(|buf| *point * (buf[1] - buf[0]) + buf[0])
                      .collect();
                  let _ = mem::replace(&mut self.evaluations, FieldType::Ext(evaluations_ext));
              }
              FieldType::Ext(evaluations) => {
                  (0..evaluations.len()).step_by(2).for_each(|b| {
                      evaluations[b >> 1] =
                          evaluations[b] + (evaluations[b + 1] - evaluations[b]) * point
                  });
              }
              FieldType::Unreachable => unreachable!(),
          };
      }
      match &mut self.evaluations {
          FieldType::Base(_) => unreachable!(),
          FieldType::Ext(evaluations) => {
              evaluations.truncate(1 << (nv - partial_point.len()));
          }
          FieldType::Unreachable => unreachable!(),
      }

      self.num_vars = nv - partial_point.len();
  }

  /// Reduce the number of variables of `self` by fixing the
  /// `partial_point.len()` variables at `partial_point` from high position
  fn fix_high_variables(&self, partial_point: &[E]) -> Self {
      // TODO: return error.
      assert!(
          partial_point.len() <= self.num_vars(),
          "invalid size of partial point"
      );
      let current_eval_size = self.evaluations.len();
      let mut poly = Cow::Borrowed(self);
      // `Cow` type here to skip first evaluation vector copy
      for point in partial_point.iter().rev() {
          match &mut poly {
              poly @ Cow::Borrowed(_) => {
                  let half_size = current_eval_size >> 1;
                  *poly = op_mle!(self, |evaluations| Cow::Owned(
                      DenseMultilinearExtension::from_evaluations_ext_vec(self.num_vars() - 1, {
                          let (lo, hi) = evaluations.split_at(half_size);
                          lo.par_iter()
                              .zip(hi)
                              .with_min_len(64)
                              .map(|(lo, hi)| *point * (*hi - *lo) + *lo)
                              .collect()
                      })
                  ));
              }
              Cow::Owned(poly) => poly.fix_high_variables_in_place(&[*point]),
          }
      }
      assert!(poly.num_vars == self.num_vars() - partial_point.len(),);
      poly.into_owned()
  }

  /// Reduce the number of variables of `self` by fixing the
  /// `partial_point.len()` variables at `partial_point` from high position in place
  fn fix_high_variables_in_place(&mut self, partial_point: &[E]) {
      // TODO: return error.
      assert!(
          partial_point.len() <= self.num_vars(),
          "invalid size of partial point"
      );
      let nv = self.num_vars();
      let mut current_eval_size = self.evaluations.len();
      for point in partial_point.iter().rev() {
          let half_size = current_eval_size >> 1;
          match &mut self.evaluations {
              FieldType::Base(evaluations) => {
                  let (lo, hi) = evaluations.split_at(half_size);
                  let evaluations_ext = lo
                      .par_iter()
                      .zip(hi)
                      .with_min_len(64)
                      .map(|(lo, hi)| *point * (*hi - *lo) + *lo)
                      .collect();
                  let _ = mem::replace(&mut self.evaluations, FieldType::Ext(evaluations_ext));
                  current_eval_size = half_size;
              }
              FieldType::Ext(evaluations) => {
                  let (lo, hi) = evaluations.split_at_mut(half_size);
                  lo.par_iter_mut()
                      .zip(hi)
                      .with_min_len(64)
                      .for_each(|(lo, hi)| *lo += (*hi - *lo) * point);
                  current_eval_size = half_size;
              }
              FieldType::Unreachable => unreachable!(),
          };
      }
      match &mut self.evaluations {
          FieldType::Base(_) => {}
          FieldType::Ext(evaluations) => {
              evaluations.truncate(current_eval_size);
          }
          FieldType::Unreachable => unreachable!(),
      }
      self.num_vars = nv - partial_point.len()
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
      op_mle!(
          mle,
          |f| {
              assert_eq!(f.len(), 1);
              f[0]
          },
          |v| E::from(v)
      )
  }

  fn num_vars(&self) -> usize {
      self.num_vars
  }

  /// Reduce the number of variables of `self` by fixing the
  /// `partial_point.len()` variables at `partial_point`.
  fn fix_variables_parallel(&self, partial_point: &[E]) -> Self {
      // TODO: return error.
      assert!(
          partial_point.len() <= self.num_vars(),
          "invalid size of partial point"
      );
      let mut poly = Cow::Borrowed(self);

      // evaluate single variable of partial point from left to right
      // `Cow` type here to skip first evaluation vector copy
      for point in partial_point.iter() {
          match &mut poly {
              poly @ Cow::Borrowed(_) => {
                  *poly = op_mle!(self, |evaluations| {
                      Cow::Owned(DenseMultilinearExtension::from_evaluations_ext_vec(
                          self.num_vars() - 1,
                          evaluations
                              .par_iter()
                              .chunks(2)
                              .with_min_len(64)
                              .map(|buf| *point * (*buf[1] - *buf[0]) + *buf[0])
                              .collect(),
                      ))
                  });
              }
              Cow::Owned(poly) => poly.fix_variables_in_place_parallel(&[*point]),
          }
      }
      assert!(poly.num_vars == self.num_vars() - partial_point.len(),);
      poly.into_owned()
  }

  /// Reduce the number of variables of `self` by fixing the
  /// `partial_point.len()` variables at `partial_point` in place
  fn fix_variables_in_place_parallel(&mut self, partial_point: &[E]) {
      // TODO: return error.
      assert!(
          partial_point.len() <= self.num_vars(),
          "partial point len {} >= num_vars {}",
          partial_point.len(),
          self.num_vars()
      );
      let nv = self.num_vars();
      // evaluate single variable of partial point from left to right
      for (i, point) in partial_point.iter().enumerate() {
          let max_log2_size = nv - i;
          // override buf[b1, b2,..bt, 0] = (1-point) * buf[b1, b2,..bt, 0] + point * buf[b1, b2,..bt, 1] in parallel
          match &mut self.evaluations {
              FieldType::Base(evaluations) => {
                  let evaluations_ext = evaluations
                      .par_iter()
                      .chunks(2)
                      .with_min_len(64)
                      .map(|buf| *point * (*buf[1] - *buf[0]) + *buf[0])
                      .collect();
                  let _ = mem::replace(&mut self.evaluations, FieldType::Ext(evaluations_ext));
              }
              FieldType::Ext(evaluations) => {
                  evaluations
                      .par_iter_mut()
                      .chunks(2)
                      .with_min_len(64)
                      .for_each(|mut buf| *buf[0] = *buf[0] + (*buf[1] - *buf[0]) * point);

                  // sequentially update buf[b1, b2,..bt] = buf[b1, b2,..bt, 0]
                  for index in 0..1 << (max_log2_size - 1) {
                      evaluations[index] = evaluations[index << 1];
                  }
              }
              FieldType::Unreachable => unreachable!(),
          };
      }
      match &mut self.evaluations {
          FieldType::Base(_) => unreachable!(),
          FieldType::Ext(evaluations) => {
              evaluations.truncate(1 << (nv - partial_point.len()));
          }
          FieldType::Unreachable => unreachable!(),
      }

      self.num_vars = nv - partial_point.len();
  }

  fn evaluations(&self) -> &FieldType<E> {
      &self.evaluations
  }

  fn evaluations_to_owned(self) -> FieldType<E> {
      self.evaluations
  }

  fn evaluations_range(&self) -> Option<(usize, usize)> {
      None
  }

  fn name(&self) -> &'static str {
      "DenseMultilinearExtension"
  }

  /// assert and get base field vector
  /// panic if not the case
  fn get_base_field_vec(&self) -> &[E::BaseField] {
      match &self.evaluations {
          FieldType::Base(evaluations) => &evaluations[..],
          FieldType::Ext(_) => unreachable!(),
          FieldType::Unreachable => unreachable!(),
      }
  }

  fn merge(&mut self, rhs: DenseMultilinearExtension<E>) {
      assert_eq!(rhs.name(), "DenseMultilinearExtension");
      let rhs_num_vars = rhs.num_vars();
      match (&mut self.evaluations, rhs.evaluations_to_owned()) {
          (FieldType::Base(e1), FieldType::Base(e2)) => {
              e1.extend(e2);
              self.num_vars = ceil_log2(e1.len());
          }
          (FieldType::Ext(e1), FieldType::Ext(e2)) => {
              e1.extend(e2);
              self.num_vars = ceil_log2(e1.len());
          }
          (FieldType::Unreachable, b @ FieldType::Base(..)) => {
              self.num_vars = rhs_num_vars;
              self.evaluations = b;
          }
          (FieldType::Unreachable, b @ FieldType::Ext(..)) => {
              self.num_vars = rhs_num_vars;
              self.evaluations = b;
          }
          (a, b) => panic!(
              "do not support merge differnt field type DME a: {:?} b: {:?}",
              a, b
          ),
      }
  }

  /// get ranged multiliear extention
  fn get_ranged_mle(
      &self,
      num_range: usize,
      range_index: usize,
  ) -> RangedMultilinearExtension<'_, E> {
      assert!(num_range > 0);
      let offset = self.evaluations.len() / num_range;
      let start = offset * range_index;
      RangedMultilinearExtension::new(self, start, offset)
  }

  /// resize to new size (num_instances * new_size_per_instance / num_range)
  /// and selected by range_index
  /// only support resize base fields, otherwise panic
  fn resize_ranged(
      &self,
      num_instances: usize,
      new_size_per_instance: usize,
      num_range: usize,
      range_index: usize,
  ) -> Self {
      println!("called deprecated api");
      assert!(num_range > 0 && num_instances > 0 && new_size_per_instance > 0);
      let new_len = (new_size_per_instance * num_instances) / num_range;
      match &self.evaluations {
          FieldType::Base(evaluations) => {
              let old_size_per_instance = evaluations.len() / num_instances;
              DenseMultilinearExtension::from_evaluations_vec(
                  ceil_log2(new_len),
                  evaluations
                      .chunks(old_size_per_instance)
                      .flat_map(|chunk| {
                          chunk
                              .iter()
                              .cloned()
                              .chain(std::iter::repeat(E::BaseField::ZERO))
                              .take(new_size_per_instance)
                      })
                      .skip(range_index * new_len)
                      .take(new_len)
                      .collect::<Vec<E::BaseField>>(),
              )
          }
          FieldType::Ext(_) => unreachable!(),
          FieldType::Unreachable => unreachable!(),
      }
  }

  /// dup to new size 1 << (self.num_vars + ceil_log2(num_dups))
  fn dup(&self, num_instances: usize, num_dups: usize) -> Self {
      assert!(num_dups.is_power_of_two());
      assert!(num_instances.is_power_of_two());
      match &self.evaluations {
          FieldType::Base(evaluations) => {
              let old_size_per_instance = evaluations.len() / num_instances;
              DenseMultilinearExtension::from_evaluations_vec(
                  self.num_vars + ceil_log2(num_dups),
                  evaluations
                      .chunks(old_size_per_instance)
                      .flat_map(|chunk| {
                          chunk
                              .iter()
                              .cycle()
                              .cloned()
                              .take(old_size_per_instance * num_dups)
                      })
                      .take(1 << (self.num_vars + ceil_log2(num_dups)))
                      .collect::<Vec<E::BaseField>>(),
              )
          }
          FieldType::Ext(_) => unreachable!(),
          FieldType::Unreachable => unreachable!(),
      }
  }
}