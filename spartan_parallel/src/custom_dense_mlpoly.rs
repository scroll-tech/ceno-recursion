#![allow(clippy::too_many_arguments)]
use std::cmp::min;

use crate::dense_mlpoly::DensePolynomial;
use crate::math::Math;
use crate::scalar::SpartanExtensionField;
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
pub struct DensePolynomialPqx<S: SpartanExtensionField> {
  // All metadata might not be a power of 2
  pub num_instances: usize,
  pub num_proofs: Vec<usize>, // P
  pub num_witness_secs: usize,
  pub num_inputs: Vec<Vec<usize>>, // P x W
  pub num_vars_p: usize, // log(P.next_power_of_two())
  pub num_vars_q: usize,
  pub num_vars_w: usize,
  pub num_vars_x: usize,
  pub Z: Vec<Vec<Vec<Vec<S>>>>, // Evaluations of the polynomial in all the 2^num_vars Boolean inputs of order (p, q, w, x)
}

fn fold_rq<S: SpartanExtensionField>(proofs: &mut [Vec<Vec<S>>], r_q: &[S], step: usize, mut q: usize, w: usize, x: &Vec<usize>) {
  for r in r_q {
    let r1 = S::field_one() - r.clone();
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

impl<S: SpartanExtensionField> DensePolynomialPqx<S> {
  // Assume z_mat is of form (p, q_rev, x), construct DensePoly
  pub fn new(
    z_mat: Vec<Vec<Vec<Vec<S>>>>, 
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
  pub fn index(&self, p: usize, q: usize, w: usize, x: usize) -> S {
    return self.Z[p][q][w][x];
  }

  // Given (p, q, w, x) and a mode, return Z[p*][q*][w*][x*]
  // Mode = 1 ==> p* = 2p for low, 2p + 1 for high
  // Mode = 2 ==> q* = 2q for low, 2q + 1
  // Mode = 3 ==> w* = 2w for low, 2w + 1
  // Mode = 4 ==> x* = 2x for low, 2x + 1
  // Assume p*, q*, w*, x* are within bound
  pub fn index_low(&self, p: usize, q: usize, w: usize, x: usize, mode: usize) -> S {
    let ZERO = S::field_zero();
    match mode {
      MODE_P => { if self.num_instances == 1 { self.Z[0][q][w][x] } else if 2 * p >= self.num_instances { ZERO } else { self.Z[2 * p][q][w][x] } }
      MODE_Q => { if 2 * q >= self.num_proofs[p] { ZERO } else { self.Z[p][2 * q][w][x] } },
      MODE_W => { if 2 * w >= self.num_witness_secs { ZERO } else { self.Z[p][q][2 * w][x] } }
      MODE_X => { if 2 * x >= self.num_inputs[p][w] { ZERO } else { self.Z[p][q][w][2 * x] } },
      _ => unreachable!()
    }
  }
  pub fn index_high(&self, p: usize, q: usize, w: usize, x: usize, mode: usize) -> S {
    let ZERO = S::field_zero();
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
  pub fn bound_poly(&mut self, r: &S, mode: usize) {
    match mode {
        MODE_P => { self.bound_poly_p(r); }
        MODE_Q => { self.bound_poly_q(r); }
        MODE_W => { self.bound_poly_w(r); }
        MODE_X => { if self.num_vars_q >= 1 { self.bound_poly_x_parallel(r) } else { self.bound_poly_x(r) }; }
        _ => { panic!("DensePolynomialPqx bound failed: unrecognized mode {}!", mode); }
    }
  }

  // Bound the last variable of "p" section to r
  // We are only allowed to bound "p" if we have bounded the entire q and x section
  fn bound_poly_p(&mut self, r: &S) {
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
  fn bound_poly_q(&mut self, r: &S) {
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
  fn _bound_poly_w_parallel(&mut self, r: &S) {
    let ZERO = S::field_zero();
    assert!(self.num_vars_w >= 1);
    assert_eq!(self.num_vars_x, 0);
    let new_num_witness_secs = self.num_witness_secs.div_ceil(2);
    let Z = std::mem::take(&mut self.Z);
    self.Z = Z.into_iter().map(|Z_p| {
      Z_p.into_par_iter().map(|mut Z_pq| {
        for w in 0..self.num_witness_secs {
          let Z_low = if 2 * w >= self.num_witness_secs { ZERO } else { Z_pq[2 * w][0] };
          let Z_high = if 2 * w + 1 >= self.num_witness_secs { ZERO } else { Z_pq[2 * w + 1][0] };
          Z_pq[w][0] = Z_low + r.clone() * (Z_high - Z_low);
        }
        Z_pq
      }).collect::<Vec<Vec<Vec<S>>>>()
    }).collect::<Vec<Vec<Vec<Vec<S>>>>>();
    self.num_witness_secs = new_num_witness_secs;
    self.num_vars_w -= 1;
}

  // Bound the last variable of "w" section to r
  // We are only allowed to bound "w" if we have bounded the entire x section
  fn bound_poly_w(&mut self, r: &S) {
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
  fn bound_poly_x_parallel(&mut self, r: &S) {
    let ZERO = S::field_zero();
    let new_num_inputs: Vec<Vec<usize>> = self.num_inputs.iter().map(|p|
      p.iter().map(|w| w.div_ceil(2)).collect()
    ).collect();
    // assert!(self.num_vars_x >= 1);
    let Z = std::mem::take(&mut self.Z);
    self.Z = Z.into_iter().enumerate().map(|(p, Z_p)| {
      Z_p.into_par_iter().map(|mut Z_pq| {
        for w in 0..self.num_witness_secs {
          for x in 0..new_num_inputs[p][w] {
            let Z_low = if 2 * x >= self.num_inputs[p][w] { ZERO } else { Z_pq[w][2 * x] };
            let Z_high = if 2 * x + 1 >= self.num_inputs[p][w] { ZERO } else { Z_pq[w][2 * x + 1] };
            Z_pq[w][x] = Z_low + r.clone() * (Z_high - Z_low);
          }
        }
        Z_pq
      }).collect::<Vec<Vec<Vec<S>>>>()
    }).collect::<Vec<Vec<Vec<Vec<S>>>>>();
    self.num_inputs = new_num_inputs;
    if self.num_vars_x >= 1 {
      self.num_vars_x -= 1;
    }
  }

  // Bound the last variable of "x" section to r
  fn bound_poly_x(&mut self, r: &S) {
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
  pub fn bound_poly_vars_rp(&mut self, r_p: &[S]) {
    for r in r_p {
      self.bound_poly_p(r);
    }
  }

  // Bound the entire "q" section to r_q in reverse
  pub fn bound_poly_vars_rq_parallel(
    &mut self, 
    r_q: &[S],
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
          let c = left_over_rq.into_iter().fold(S::field_one(), |acc, n| acc * (S::field_one() - *n));
          for w in 0..inst[0].len() {
            for x in 0..inst[0][w].len() {
              inst[0][w][x] *= c;
            }
          }
        }

        inst
      }).collect::<Vec<Vec<Vec<Vec<S>>>>>();

    self.num_vars_q = 0;
    self.num_proofs = vec![1; self.num_instances];
  }

  // Bound the entire "q" section to r_q in reverse
  pub fn bound_poly_vars_rq(&mut self, r_q: &[S]) {
    for r in r_q {
      self.bound_poly_q(r);
    }
  }

  // Bound the entire "w" section to r_w in reverse
  pub fn bound_poly_vars_rw(&mut self, r_w: &[S]) {
    for r in r_w {
      self.bound_poly_w(r);
    }
  }

  // Bound the entire "x_rev" section to r_x
  pub fn bound_poly_vars_rx(&mut self, r_x: &[S]) {
    for r in r_x {
      if self.num_vars_q >= 1 { self.bound_poly_x_parallel(r) } else { self.bound_poly_x(r) };
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