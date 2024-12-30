#![allow(clippy::too_many_arguments)]
use std::cmp::min;

use crate::dense_mlpoly::DensePolynomial;
use crate::scalar::SpartanExtensionField;
use rayon::prelude::*;

const MODE_P: usize = 1;
const MODE_Q: usize = 2;
const MODE_W: usize = 3;
const MODE_X: usize = 4;
const NUM_MULTI_THREAD_CORES: usize = 32;

// Customized Dense ML Polynomials for Data-Parallelism
// These Dense ML Polys are aimed for space-efficiency by removing the 0s for invalid (p, q, w, x) quadruple

// Dense polynomial with variable order: p, q_rev, w, x_rev
// Used by Z_poly in r1csproof
#[derive(Debug, Clone)]
pub struct DensePolynomialPqx<S: SpartanExtensionField> {
  num_instances: usize, // num_instances is a power of 2 and num_instances / 2 < Z.len() <= num_instances
  num_proofs: Vec<usize>,
  max_num_proofs: usize,
  pub num_witness_secs: usize, // num_witness_secs is a power of 2 and num_witness_secs / 2 < Z[.][.].len() <= num_witness_secs
  num_inputs: Vec<usize>,
  max_num_inputs: usize,
  pub Z: Vec<Vec<Vec<Vec<S>>>>, // Evaluations of the polynomial in all the 2^num_vars Boolean inputs of order (p, q_rev, w, x_rev)
                                // Let Q_max = max_num_proofs, assume that for a given P, num_proofs[P] = Q_i, then let STEP = Q_max / Q_i,
                                // Z(P, y, .) is only non-zero if y is a multiple of STEP, so Z[P][j][.] actually stores Z(P, j*STEP, .)
                                // The same applies to X
}

impl<S: SpartanExtensionField> DensePolynomialPqx<S> {
  // Assume z_mat is of form (p, q_rev, x_rev), construct DensePoly
  pub fn new(
    z_mat: Vec<Vec<Vec<Vec<S>>>>,
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
      Z: z_mat,
    }
  }

  pub fn len(&self) -> usize {
    return self.num_instances * self.max_num_proofs * self.max_num_inputs;
  }

  // Given (p, q_rev, x_rev) return Z[p][q_rev][x_rev]
  pub fn index(&self, p: usize, q_rev: usize, w: usize, x_rev: usize) -> S {
    if p < self.Z.len()
      && q_rev < self.Z[p].len()
      && w < self.Z[p][q_rev].len()
      && x_rev < self.Z[p][q_rev][w].len()
    {
      return self.Z[p][q_rev][w][x_rev];
    } else {
      return S::field_zero();
    }
  }

  // Given (p, q, w, x) and a mode, return Z[p*][q*][w*][x*]
  // Mode = 1 ==> p* = 2p for low, 2p + 1 for high
  // Mode = 2 ==> q* = 2q for low, 2q + 1
  // Mode = 3 ==> w* = 2w for low, 2w + 1
  // Mode = 4 ==> x* = 2x for low, 2x + 1
  // Assume p*, q*, w*, x*, within bound
  pub fn index_low(&self, p: usize, q: usize, w: usize, x: usize, mode: usize) -> S {
    let ZERO = S::field_zero();
    match mode {
        MODE_P => { if 2 * p >= self.Z.len() { ZERO } else { self.Z[2 * p][q][w][x] } }
        MODE_Q => self.Z[p][2 * q][w][x],
        MODE_W => { if 2 * w >= self.Z[p][q].len() { ZERO } else { self.Z[p][q][2 * w][x] } }
        MODE_X => self.Z[p][q][w][2 * x],
        _ => unreachable!()
    }
  }

  pub fn index_high(&self, p: usize, q: usize, w: usize, x: usize, mode: usize) -> S {
    let ZERO = S::field_zero();
    match mode {
        MODE_P => { if self.num_instances == 1 { self.Z[0][q][w][x] } else if 2 * p + 1 >= self.Z.len() { ZERO } else { self.Z[2 * p + 1][q][w][x] } }
        MODE_Q => { if self.num_proofs[p] == 1 { ZERO } else { self.Z[p][2 * q + 1][w][x] } }
        MODE_W => { if 2 * w + 1 >= self.Z[p][q].len() { ZERO } else { self.Z[p][q][2 * w + 1][x] } }
        MODE_X => { if self.num_inputs[p] == 1 { ZERO } else { self.Z[p][q][w][2 * x + 1] } }
        _ => unreachable!()
    }
  }

  // Bound a variable to r according to mode
  // Mode = 1 ==> Bound last variable of "p" section to r
  // Mode = 2 ==> Bound last variable of "q" section to r
  // Mode = 3 ==> Bound last variable of "w" section to r
  // Mode = 4 ==> Bound last variable of "x" section to r
  pub fn bound_poly(&mut self, r: &S, mode: usize) {
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
  pub fn bound_poly_p(&mut self, r: &S) {
      let ZERO = S::field_zero();
      assert_eq!(self.max_num_proofs, 1);
      assert_eq!(self.max_num_inputs, 1);
      self.num_instances /= 2;
      for p in 0..self.num_instances {
          for w in 0..min(self.num_witness_secs, self.Z[p][0].len()) {
              let Z_low = if 2 * p < self.Z.len() { self.Z[2 * p][0][w][0] } else { ZERO };
              let Z_high = if 2 * p + 1 < self.Z.len() { self.Z[2 * p + 1][0][w][0] } else { ZERO };
              self.Z[p][0][w][0] = Z_low + r.clone() * (Z_high - Z_low);
          }
      }
  }

  // Bound the last variable of "q" section to r
  pub fn bound_poly_q(&mut self, r: &S) {
    let ONE = S::field_one();
    self.max_num_proofs /= 2;

    for p in 0..min(self.num_instances, self.Z.len()) {
      if self.num_proofs[p] == 1 {
        for w in 0..min(self.num_witness_secs, self.Z[p][0].len()) {
          for x in 0..self.num_inputs[p] {
            self.Z[p][0][w][x] *= ONE - r.clone();
          }
        }
      } else {
        self.num_proofs[p] /= 2;
        for q in 0..self.num_proofs[p] {
          for w in 0..min(self.num_witness_secs, self.Z[p][q].len()) {
            for x in 0..self.num_inputs[p] {
              self.Z[p][q][w][x] = self.Z[p][2 * q][w][x] + r.clone() * (self.Z[p][2 * q + 1][w][x] - self.Z[p][2 * q][w][x]);
            }
          }
        }
      }
    }
  }

  // Bound the last variable of "w" section to r
  pub fn bound_poly_w(&mut self, r: &S) {
    let ZERO = S::field_zero();
    self.num_witness_secs /= 2;

    for p in 0..min(self.num_instances, self.Z.len()) {
      for q in 0..self.num_proofs[p] {
        for w in 0..self.num_witness_secs {
          for x in 0..self.num_inputs[p] {
            let Z_low = if 2 * w < self.Z[p][q].len() { self.Z[p][q][2 * w][x] } else { ZERO };
            let Z_high = if 2 * w + 1 < self.Z[p][q].len() { self.Z[p][q][2 * w + 1][x] } else { ZERO };
            self.Z[p][q][w][x] = Z_low + r.clone() * (Z_high - Z_low);
          }
        }
      }
    }
}

  // Bound the last variable of "x" section to r
  pub fn bound_poly_x(&mut self, r: &S) {
      let ONE = S::field_one();
      self.max_num_inputs /= 2;

      for p in 0..min(self.num_instances, self.Z.len()) {
        if self.num_inputs[p] == 1 {
          for q in 0..self.num_proofs[p] {
            for w in 0..min(self.num_witness_secs, self.Z[p][q].len()) {
                self.Z[p][q][w][0] *= ONE - r.clone();
            }
          }
        } else {
          self.num_inputs[p] /= 2;
          for q in 0..self.num_proofs[p] {
            for w in 0..min(self.num_witness_secs, self.Z[p][q].len()) {
              for x in 0..self.num_inputs[p] {
                  self.Z[p][q][w][x] = self.Z[p][q][w][2 * x] + r.clone() * (self.Z[p][q][w][2 * x + 1] - self.Z[p][q][w][2 * x]);
              }
            }
          }
        }
      }
  }

  // Bound the entire "p" section to r_p in reverse
  // Must occur after r_q's are bounded
  pub fn bound_poly_vars_rp(&mut self, 
      r_p: &[S],
    ) {
      for r in r_p {
        self.bound_poly_p(r);
      }
    }

  // Bound the entire "q" section to r_q in reverse
  pub fn bound_poly_vars_rq(
    &mut self, 
    r_q: &[S],
  ) {
    let Z = std::mem::take(&mut self.Z);

    self.Z = Z
      .into_iter()
      .enumerate()
      .map(|(p, mut inst)| {
        let num_proofs = self.num_proofs[p];
        let dist_size = num_proofs / min(num_proofs, NUM_MULTI_THREAD_CORES); // distributed number of proofs on each thread
        let num_threads = num_proofs / dist_size;

        // To perform rigorous parallelism, both num_proofs and # threads must be powers of 2
        // # threads must fully divide num_proofs for even distribution
        assert!(num_proofs & (num_proofs - 1) == 0);
        assert!(num_threads & (num_threads - 1) == 0);

        // Determine parallelism levels
        let levels = num_proofs.trailing_zeros() as usize; // total layers
        let sub_levels = dist_size.trailing_zeros() as usize; // parallelism layers
        let final_levels = num_threads.trailing_zeros() as usize; // single core final layers
        let left_over_q_len = r_q.len() - levels; // if r_q.len() > log2(num_proofs)

        // single proof matrix dimension W x X
        let num_witness_secs = min(self.num_witness_secs, inst[0].len());
        let num_inputs = self.num_inputs[p];

        // debug
        println!("[");
        inst.iter().for_each(|mat| println!("{:?}, ", mat[0][0]));
        println!("]");
        println!();

        if sub_levels > 0 {
          let thread_split_inst = (0..num_threads)
            .map(|_| {
              inst.split_off(inst.len() - dist_size)
            })
            .rev()
            .collect::<Vec<Vec<Vec<Vec<S>>>>>();

          inst = thread_split_inst
            .into_par_iter()
            .map(|mut chunk| {
              fold(&mut chunk, r_q, 0, 1, sub_levels, 0, num_witness_secs, num_inputs);
              chunk
            })
            .collect::<Vec<Vec<Vec<Vec<S>>>>>()
            .into_iter().flatten().collect()
        }

        if final_levels > 0 {
          // aggregate the final result from sub-threads outputs using a single core
          fold(&mut inst, r_q, 0, dist_size, final_levels + sub_levels, sub_levels, num_witness_secs, num_inputs);
        }

        if left_over_q_len > 0 {
          // the series of random challenges exceeds the total number of variables
          let c = r_q[(r_q.len() - left_over_q_len)..r_q.len()].iter().fold(S::field_one(), |acc, n| acc * (S::field_one() - *n));
          for w in 0..inst[0].len() {
            for x in 0..inst[0][0].len() {
              inst[0][w][x] *= c;
            }
          }
        }

        inst
      }).collect::<Vec<Vec<Vec<Vec<S>>>>>();

    self.max_num_proofs /= 2usize.pow(r_q.len() as u32);
  }

  // Bound the entire "w" section to r_w in reverse
  pub fn bound_poly_vars_rw(&mut self, 
    r_w: &[S],
  ) {
    for r in r_w {
      self.bound_poly_w(r);
    }
  }

  // Bound the entire "x_rev" section to r_x
  pub fn bound_poly_vars_rx(&mut self, 
    r_x: &[S],
  ) {
    for r in r_x {
      self.bound_poly_x(r);
    }
  }

  pub fn evaluate(&self,
    rp_rev: &Vec<S>,
    rq_rev: &Vec<S>,
    rw_rev: &Vec<S>,
    rx_rev: &Vec<S>,
  ) -> S {
    let mut cl = self.clone();
    cl.bound_poly_vars_rx(rx_rev);
    cl.bound_poly_vars_rw(rw_rev);
    cl.bound_poly_vars_rq(rq_rev);
    cl.bound_poly_vars_rp(rp_rev);
    return cl.index(0, 0, 0, 0);
  }

  // Convert to a (p, q_rev, x_rev) regular dense poly of form (p, q, x)
  pub fn to_dense_poly(&self) -> DensePolynomial<S> {
      let ZERO = S::field_zero();
      let mut Z_poly = vec![ZERO; self.num_instances * self.max_num_proofs * self.num_witness_secs * self.max_num_inputs];
      for p in 0..min(self.num_instances, self.Z.len()) {
        for q in 0..self.num_proofs[p] {
          for w in 0..min(self.num_witness_secs, self.Z[p][q].len()) {
            for x in 0..self.num_inputs[p] {
                Z_poly[
                    p * self.max_num_proofs * self.num_witness_secs * self.max_num_inputs 
                  + q * self.num_witness_secs * self.max_num_inputs 
                  + w * self.max_num_inputs 
                  + x
                ] = self.Z[p][q][w][x];
            }
          }
        }
      }
      DensePolynomial::new(Z_poly)
  }
}

fn fold<S: SpartanExtensionField>(proofs: &mut Vec<Vec<Vec<S>>>, r_q: &[S], idx: usize, step: usize, lvl: usize, final_lvl: usize, w: usize, x: usize) {
  if lvl > final_lvl {
    fold(proofs, r_q, 2 * idx, step, lvl - 1, final_lvl, w, x);
    fold(proofs, r_q, 2 * idx + step, step, lvl - 1, final_lvl, w, x);

    let r1 = S::field_one() - r_q[lvl - 1];
    let r2 = r_q[lvl - 1];

    (0..w).for_each(|w| {
      (0..x).for_each(|x| {
        proofs[idx][w][x] = r1 * proofs[idx * 2][w][x] + r2 * proofs[idx * 2 + step][w][x];
      });
    });
  } else {
    // base level. do nothing
  }
}