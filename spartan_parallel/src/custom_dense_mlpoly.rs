#![allow(clippy::too_many_arguments)]
use std::cmp::min;

use crate::dense_mlpoly::DensePolynomial;
use crate::scalar::SpartanExtensionField;
use rayon::prelude::*;

const MODE_P: usize = 1;
const MODE_Q: usize = 2;
const MODE_W: usize = 3;
const MODE_X: usize = 4;
const NUM_MULTI_THREAD_CORES: usize = 8;

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
  pub fn bound_poly_vars_rq(&mut self, 
    r_q: &[S],
  ) {
    let num_instances = min(self.num_instances, self.Z.len());

    fn recur<S: SpartanExtensionField>(idx: usize, lvl: usize, w: usize, x: usize, env: &(
      &Vec<Vec<Vec<S>>>, // self.Z[p]
      &[S], // r_q
      &usize, // start_idx
    )) -> S {
      if lvl > 0 {
        (S::field_one() - env.1[lvl]) * recur(2 * idx, lvl - 1, w, x, env) + env.1[lvl] * recur(2 * idx + 1, lvl - 1, w, x, env)
      } else {
        env.0[env.2 + idx][w][x]
      }
    }

    self.Z = (0..num_instances)
      // .into_par_iter()
      .map(|p| {
        let num_proofs = self.num_proofs[p];
        let dist_size = num_proofs / min(num_proofs, NUM_MULTI_THREAD_CORES);
        let num_threads = num_proofs / dist_size;

        // To perform rigorous 2-fold parallelism, both num_proofs and # cores must be powers of 2
        // # cores must fully divide num_proofs for even distribution
        assert!(num_proofs & (num_proofs - 1) == 0);
        assert!(num_threads & (num_threads - 1) == 0);

        // debug_parallelism
        println!("num_proofs: {:?}, num_threads: {:?}", num_proofs, num_threads);

        // Determine the aggregation levels that will be performed in parallel
        // The last rounds of aggregation will be done in single core
        let levels = num_proofs.trailing_zeros() as usize;
        let sub_levels = dist_size.trailing_zeros() as usize;
        let final_levels = num_threads.trailing_zeros() as usize;
        let left_over_q_len = r_q.len() - levels;

        // debug_parallelism
        println!("levels: {:?}, sub_levels: {:?}, final_levels: {:?}, left_over_q_len: {:?}", levels, sub_levels, final_levels, left_over_q_len);

        let num_witness_secs = min(self.num_witness_secs, self.Z[p][0].len());
        let num_inputs = self.num_inputs[p];

        // debug_parallelism
        println!("num_witness_secs: {:?}, num_inputs: {:?}", num_witness_secs, num_inputs);

        let mut sub_mats = if sub_levels > 0 {
          std::iter::successors(Some(0usize), move |&x| Some(x + dist_size))
          .take(NUM_MULTI_THREAD_CORES)
          .collect::<Vec<usize>>()
          .into_par_iter()
          .map(|start_idx| {
            (0..num_witness_secs).map(|w| {
              (0..num_inputs).map(|x| {
                recur(0, sub_levels, w, x, &(&self.Z[p], r_q, &start_idx))
              }).collect::<Vec<S>>()
            }).collect::<Vec<Vec<S>>>()
          }).collect::<Vec<Vec<Vec<S>>>>()
        } else {
          self.Z[p].clone()
        };

        if final_levels > 0 {
          sub_mats[0] = (0..num_witness_secs).map(|w| {
            (0..num_inputs).map(|x| {
              recur(0, final_levels, w, x, &(&sub_mats, r_q, &0))
            }).collect::<Vec<S>>()
          }).collect::<Vec<Vec<S>>>()
        }

        if left_over_q_len > 0 {
          let c = r_q[(r_q.len() - left_over_q_len)..r_q.len()].iter().fold(S::field_one(), |acc, n| acc * (S::field_one() - *n));
          for w in 0..sub_mats[0].len() {
            for x in 0..sub_mats[0][0].len() {
              sub_mats[0][w][x] *= c;
            }
          }
        }
        
        sub_mats
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