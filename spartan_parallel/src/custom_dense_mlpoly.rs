#![allow(clippy::too_many_arguments)]
use std::cmp::min;

use crate::dense_mlpoly::DensePolynomial;

use super::math::Math;
use super::scalar::Scalar;

const ZERO: Scalar = Scalar::zero();
const ONE: Scalar = Scalar::one();
const MODE_P: usize = 1;
const MODE_Q: usize = 2;
const MODE_W: usize = 3;
const MODE_X: usize = 4;

// Customized Dense ML Polynomials for Data-Parallelism
// These Dense ML Polys are aimed for space-efficiency by removing the 0s for invalid (p, q, w, x) quadruple

// Dense polynomial with variable order: p, q_rev, w, x_rev
// Used by Z_poly in r1csproof
#[derive(Debug, Clone)]
pub struct DensePolynomialPqx {
  num_instances: usize, // num_instances is a power of 2 and num_instances / 2 < Z.len() <= num_instances
  num_proofs: Vec<usize>,
  max_num_proofs: usize,
  pub num_witness_secs: usize, // num_witness_secs is a power of 2 and num_witness_secs / 2 < Z[.][.].len() <= num_witness_secs
  num_inputs: Vec<usize>,
  max_num_inputs: usize,
  pub Z: Vec<Vec<Vec<Vec<Scalar>>>>, // Evaluations of the polynomial in all the 2^num_vars Boolean inputs of order (p, q_rev, w, x_rev)
                                     // Let Q_max = max_num_proofs, assume that for a given P, num_proofs[P] = Q_i, then let STEP = Q_max / Q_i,
                                     // Z(P, y, .) is only non-zero if y is a multiple of STEP, so Z[P][j][.] actually stores Z(P, j*STEP, .)
                                     // The same applies to X
}

// Reverse the bits in q or x
pub fn rev_bits(q: usize, max_num_proofs: usize) -> usize {
  (0..max_num_proofs.log_2())
    .rev()
    .map(|i| q / (i.pow2()) % 2 * (max_num_proofs / i.pow2() / 2))
    .sum::<usize>()
}

impl DensePolynomialPqx {
  // Assume z_mat is of form (p, q_rev, x), construct DensePoly
  pub fn new(
    z_mat: &Vec<Vec<Vec<Vec<Scalar>>>>,
    num_proofs: Vec<usize>,
    max_num_proofs: usize,
    num_inputs: Vec<usize>,
    max_num_inputs: usize,
  ) -> Self {
    let num_instances = z_mat.len().next_power_of_two();
    let num_witness_secs = z_mat[0][0].len().next_power_of_two();
    DensePolynomialPqx {
      num_instances,
      num_proofs,
      max_num_proofs,
      num_witness_secs,
      num_inputs,
      max_num_inputs,
      Z: z_mat.clone(),
    }
  }

  // Assume z_mat is in its standard form of (p, q, x)
  // Reverse q and x and convert it to (p, q_rev, x_rev)
  pub fn new_rev(
    z_mat: &Vec<Vec<Vec<Vec<Scalar>>>>,
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
        vec![vec![ZERO; num_inputs[p]]; num_witness_secs];
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
    DensePolynomialPqx {
      num_instances: num_instances.next_power_of_two(),
      num_proofs,
      max_num_proofs,
      num_witness_secs: num_witness_secs.next_power_of_two(),
      num_inputs,
      max_num_inputs,
      Z,
    }
  }

  pub fn len(&self) -> usize {
    self.num_instances * self.max_num_proofs * self.max_num_inputs
  }

  // Given (p, q_rev, x_rev) return Z[p][q_rev][x_rev]
  pub fn index(&self, p: usize, q_rev: usize, w: usize, x_rev: usize) -> Scalar {
    if p < self.Z.len()
      && q_rev < self.Z[p].len()
      && w < self.Z[p][q_rev].len()
      && x_rev < self.Z[p][q_rev][w].len()
    {
      self.Z[p][q_rev][w][x_rev]
    } else {
      ZERO
    }
  }

  // Given (p, q_rev, w, x_rev) and a mode, return Z[p*][q_rev*][w*][x_rev*]
  // Mode = 1 ==> p* is p with first bit set to 1
  // Mode = 2 ==> q_rev* is q_rev with first bit set to 1
  // Mode = 3 ==> w* is w with first bit set to 1
  // Mode = 4 ==> x_rev* is x_rev with first bit set to 1
  // Assume that first bit of the corresponding index is 0, otherwise throw out of bound exception
  pub fn index_high(&self, p: usize, q_rev: usize, w: usize, x_rev: usize, mode: usize) -> Scalar {
    match mode {
      MODE_P => {
        if p + self.num_instances / 2 < self.Z.len() {
          self.Z[p + self.num_instances / 2][q_rev][w][x_rev]
        } else {
          ZERO
        }
      }
      MODE_Q => {
        if self.num_proofs[p] == 1 {
          ZERO
        } else {
          self.Z[p][q_rev + self.num_proofs[p] / 2][w][x_rev]
        }
      }
      MODE_W => {
        if w + self.num_witness_secs / 2 < self.Z[p][q_rev].len() {
          self.Z[p][q_rev][w + self.num_witness_secs / 2][x_rev]
        } else {
          ZERO
        }
      }
      MODE_X => {
        if self.num_inputs[p] == 1 {
          ZERO
        } else {
          self.Z[p][q_rev][w][x_rev + self.num_inputs[p] / 2]
        }
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
  pub fn bound_poly(&mut self, r: &Scalar, mode: usize) {
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
  pub fn bound_poly_p(&mut self, r: &Scalar) {
    assert_eq!(self.max_num_proofs, 1);
    assert_eq!(self.max_num_inputs, 1);
    self.num_instances /= 2;
    for p in 0..self.num_instances {
      for w in 0..min(self.num_witness_secs, self.Z[p][0].len()) {
        let Z_high = if p + self.num_instances < self.Z.len() {
          self.Z[p + self.num_instances][0][w][0]
        } else {
          ZERO
        };
        self.Z[p][0][w][0] = self.Z[p][0][w][0] + r * (Z_high - self.Z[p][0][w][0]);
      }
    }
  }

  // Bound the first variable of "q" section to r
  pub fn bound_poly_q(&mut self, r: &Scalar) {
    self.max_num_proofs /= 2;

    for p in 0..min(self.num_instances, self.Z.len()) {
      if self.num_proofs[p] == 1 {
        for w in 0..min(self.num_witness_secs, self.Z[p][0].len()) {
          for x in 0..self.num_inputs[p] {
            self.Z[p][0][w][x] = (ONE - r) * self.Z[p][0][w][x];
          }
        }
      } else {
        self.num_proofs[p] /= 2;
        for q in 0..self.num_proofs[p] {
          for w in 0..min(self.num_witness_secs, self.Z[p][q].len()) {
            for x in 0..self.num_inputs[p] {
              self.Z[p][q][w][x] = self.Z[p][q][w][x]
                + r * (self.Z[p][q + self.num_proofs[p]][w][x] - self.Z[p][q][w][x]);
            }
          }
        }
      }
    }
  }

  // Bound the first variable of "w" section to r
  pub fn bound_poly_w(&mut self, r: &Scalar) {
    self.num_witness_secs /= 2;

    for p in 0..min(self.num_instances, self.Z.len()) {
      for q in 0..self.num_proofs[p] {
        for w in 0..self.num_witness_secs {
          for x in 0..self.num_inputs[p] {
            let Z_high = if w + self.num_witness_secs < self.Z[p][q].len() {
              self.Z[p][q][w + self.num_witness_secs][x]
            } else {
              ZERO
            };
            self.Z[p][q][w][x] = self.Z[p][q][w][x] + r * (Z_high - self.Z[p][q][w][x]);
          }
        }
      }
    }
  }

  // Bound the first variable of "x" section to r
  pub fn bound_poly_x(&mut self, r: &Scalar) {
    self.max_num_inputs /= 2;

    for p in 0..min(self.num_instances, self.Z.len()) {
      if self.num_inputs[p] == 1 {
        for q in 0..self.num_proofs[p] {
          for w in 0..min(self.num_witness_secs, self.Z[p][q].len()) {
            self.Z[p][q][w][0] = (ONE - r) * self.Z[p][q][w][0];
          }
        }
      } else {
        self.num_inputs[p] /= 2;
        for q in 0..self.num_proofs[p] {
          for w in 0..min(self.num_witness_secs, self.Z[p][q].len()) {
            for x in 0..self.num_inputs[p] {
              self.Z[p][q][w][x] = self.Z[p][q][w][x]
                + r * (self.Z[p][q][w][x + self.num_inputs[p]] - self.Z[p][q][w][x]);
            }
          }
        }
      }
    }
  }

  // Bound the entire "p" section to r_p
  // Must occur after r_q's are bounded
  pub fn bound_poly_vars_rp(&mut self, r_p: &Vec<Scalar>) {
    for r in r_p {
      self.bound_poly_p(r);
    }
  }

  // Bound the entire "q_rev" section to r_q
  pub fn bound_poly_vars_rq(&mut self, r_q: &Vec<Scalar>) {
    for r in r_q {
      self.bound_poly_q(r);
    }
  }

  // Bound the entire "w" section to r_w
  pub fn bound_poly_vars_rw(&mut self, r_w: &Vec<Scalar>) {
    for r in r_w {
      self.bound_poly_w(r);
    }
  }

  // Bound the entire "x_rev" section to r_x
  pub fn bound_poly_vars_rx(&mut self, r_x: &Vec<Scalar>) {
    for r in r_x {
      self.bound_poly_x(r);
    }
  }

  pub fn evaluate(
    &self,
    r_p: &Vec<Scalar>,
    r_q: &Vec<Scalar>,
    r_w: &Vec<Scalar>,
    r_x: &Vec<Scalar>,
  ) -> Scalar {
    let mut cl = self.clone();
    cl.bound_poly_vars_rx(r_x);
    cl.bound_poly_vars_rw(r_w);
    cl.bound_poly_vars_rq(r_q);
    cl.bound_poly_vars_rp(r_p);
    cl.index(0, 0, 0, 0)
  }

  // Convert to a (p, q_rev, x_rev) regular dense poly of form (p, q, x)
  pub fn to_dense_poly(&self) -> DensePolynomial {
    let mut Z_poly =
      vec![
        ZERO;
        self.num_instances * self.max_num_proofs * self.num_witness_secs * self.max_num_inputs
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
    DensePolynomial::new(Z_poly)
  }
}
