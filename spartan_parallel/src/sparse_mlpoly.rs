#![allow(clippy::type_complexity)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::needless_range_loop)]
use super::dense_mlpoly::DensePolynomial;
use super::dense_mlpoly::{EqPolynomial, IdentityPolynomial, PolyEvalProof};
use super::errors::ProofVerifyError;
use super::math::Math;
use super::product_tree::{DotProductCircuit, ProductCircuit, ProductCircuitEvalProofBatched};
use super::random::RandomTape;
use super::timer::Timer;
use super::transcript::{Transcript, append_field_to_transcript, append_field_vector_to_transcript, append_protocol_name, challenge_vector};
use core::cmp::Ordering;
use ff_ext::ExtensionField;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SparseMatEntry<E: ExtensionField> {
  row: usize,
  col: usize,
  val: E,
}

impl<E: ExtensionField> SparseMatEntry<E> {
  pub fn new(row: usize, col: usize, val: E) -> Self {
    SparseMatEntry { row, col, val }
  }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SparseMatPolynomial<E: ExtensionField> {
  pub num_vars_x: usize,
  pub num_vars_y: usize,
  pub M: Vec<SparseMatEntry<E>>,
}

pub struct Derefs<E: ExtensionField> {
  row_ops_val: Vec<DensePolynomial<E>>,
  col_ops_val: Vec<DensePolynomial<E>>,
  comb: DensePolynomial<E>,
}

impl<E: ExtensionField> Derefs<E> {
  pub fn new(row_ops_val: Vec<DensePolynomial<E>>, col_ops_val: Vec<DensePolynomial<E>>) -> Self {
    assert_eq!(row_ops_val.len(), col_ops_val.len());

    let ret_row_ops_val = row_ops_val.clone();
    let ret_col_ops_val = col_ops_val.clone();

    let derefs = {
      // combine all polynomials into a single polynomial (used below to produce a single commitment)
      let comb = DensePolynomial::merge(row_ops_val.into_iter().chain(col_ops_val.into_iter()));

      Derefs {
        row_ops_val: ret_row_ops_val,
        col_ops_val: ret_col_ops_val,
        comb,
      }
    };

    derefs
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DerefsEvalProof<E: ExtensionField> {
  proof_derefs: PolyEvalProof<E>,
}

impl<E: ExtensionField> DerefsEvalProof<E> {
  fn protocol_name() -> &'static [u8] {
    b"Derefs evaluation proof"
  }

  fn prove_single(
    joint_poly: &DensePolynomial<E>,
    r: &[E],
    evals: Vec<E>,
    transcript: &mut Transcript<E>,
    random_tape: &mut RandomTape<E>,
  ) -> PolyEvalProof<E> {
    assert_eq!(joint_poly.get_num_vars(), r.len() + evals.len().log_2());

    // append the claimed evaluations to transcript
    append_field_vector_to_transcript(transcript, &evals);

    // n-to-1 reduction
    let (r_joint, eval_joint) = {
      let challenges =
        challenge_vector(transcript, b"challenge_combine_n_to_one", evals.len().log_2());
      let mut poly_evals = DensePolynomial::new(evals);
      for i in (0..challenges.len()).rev() {
        poly_evals.bound_poly_var_bot(&challenges[i]);
      }
      assert_eq!(poly_evals.len(), 1);
      let joint_claim_eval = poly_evals[0];
      let mut r_joint = challenges;
      r_joint.extend(r);

      debug_assert_eq!(joint_poly.evaluate(&r_joint), joint_claim_eval);
      (r_joint, joint_claim_eval)
    };
    // decommit the joint polynomial at r_joint
    append_field_to_transcript(transcript, eval_joint);

    let proof_derefs =
      PolyEvalProof::prove(joint_poly, &r_joint, &eval_joint, transcript, random_tape);

    proof_derefs
  }

  // evalues both polynomials at r and produces a joint proof of opening
  pub fn prove(
    derefs: &Derefs<E>,
    eval_row_ops_val_vec: &[E],
    eval_col_ops_val_vec: &[E],
    r: &[E],
    transcript: &mut Transcript<E>,
    random_tape: &mut RandomTape<E>,
  ) -> Self {
    append_protocol_name(
      transcript,
      DerefsEvalProof::<E>::protocol_name(),
    );

    let evals = {
      let mut evals = eval_row_ops_val_vec.to_owned();
      evals.extend(eval_col_ops_val_vec);
      evals.resize(evals.len().next_power_of_two(), E::ZERO);
      evals
    };
    let proof_derefs =
      DerefsEvalProof::prove_single(&derefs.comb, r, evals, transcript, random_tape);

    DerefsEvalProof { proof_derefs }
  }

  fn verify_single(
    proof: &PolyEvalProof<E>,
    r: &[E],
    evals: Vec<E>,
    transcript: &mut Transcript<E>,
  ) -> Result<(), ProofVerifyError> {
    // append the claimed evaluations to transcript
    append_field_vector_to_transcript(transcript, &evals);

    // n-to-1 reduction
    let challenges =
      challenge_vector(transcript, b"challenge_combine_n_to_one", evals.len().log_2());
    let mut poly_evals = DensePolynomial::new(evals);
    for i in (0..challenges.len()).rev() {
      poly_evals.bound_poly_var_bot(&challenges[i]);
    }
    assert_eq!(poly_evals.len(), 1);
    let joint_claim_eval = poly_evals[0];
    let mut r_joint = challenges;
    r_joint.extend(r);

    // decommit the joint polynomial at r_joint
    append_field_to_transcript(transcript, joint_claim_eval);

    proof.verify_plain(transcript, &r_joint, &joint_claim_eval)
  }

  // verify evaluations of both polynomials at r
  pub fn verify(
    &self,
    r: &[E],
    eval_row_ops_val_vec: &[E],
    eval_col_ops_val_vec: &[E],
    transcript: &mut Transcript<E>,
  ) -> Result<(), ProofVerifyError> {
    append_protocol_name(
      transcript,
      DerefsEvalProof::<E>::protocol_name(),
    );

    let mut evals = eval_row_ops_val_vec.to_owned();
    evals.extend(eval_col_ops_val_vec);
    evals.resize(evals.len().next_power_of_two(), E::ZERO);

    DerefsEvalProof::verify_single(&self.proof_derefs, r, evals, transcript)
  }
}

#[derive(Clone)]
struct AddrTimestamps<E: ExtensionField> {
  ops_addr_usize: Vec<Vec<usize>>,
  ops_addr: Vec<DensePolynomial<E>>,
  read_ts: Vec<DensePolynomial<E>>,
  audit_ts: DensePolynomial<E>,
}

impl<E: ExtensionField> AddrTimestamps<E> {
  pub fn new(num_cells: usize, num_ops: usize, ops_addr: Vec<Vec<usize>>) -> Self {
    for item in ops_addr.iter() {
      assert_eq!(item.len(), num_ops);
    }

    let mut audit_ts = vec![0usize; num_cells];
    let mut ops_addr_vec: Vec<DensePolynomial<E>> = Vec::new();
    let mut read_ts_vec: Vec<DensePolynomial<E>> = Vec::new();
    for ops_addr_inst in ops_addr.iter() {
      let mut read_ts = vec![0usize; num_ops];

      // since read timestamps are trustworthy, we can simply increment the r-ts to obtain a w-ts
      // this is sufficient to ensure that the write-set, consisting of (addr, val, ts) tuples, is a set
      for i in 0..num_ops {
        let addr = ops_addr_inst[i];
        assert!(addr < num_cells);
        let r_ts = audit_ts[addr];
        read_ts[i] = r_ts;

        let w_ts = r_ts + 1;
        audit_ts[addr] = w_ts;
      }

      ops_addr_vec.push(DensePolynomial::from_usize(ops_addr_inst));
      read_ts_vec.push(DensePolynomial::from_usize(&read_ts));
    }

    AddrTimestamps {
      ops_addr: ops_addr_vec,
      ops_addr_usize: ops_addr,
      read_ts: read_ts_vec,
      audit_ts: DensePolynomial::from_usize(&audit_ts),
    }
  }

  fn deref_mem(addr: &[usize], mem_val: &[E]) -> DensePolynomial<E> {
    DensePolynomial::new(
      (0..addr.len())
        .map(|i| {
          let a = addr[i];
          mem_val[a]
        })
        .collect::<Vec<E>>(),
    )
  }

  pub fn deref(&self, mem_val: &[E]) -> Vec<DensePolynomial<E>> {
    (0..self.ops_addr.len())
      .map(|i| AddrTimestamps::deref_mem(&self.ops_addr_usize[i], mem_val))
      .collect::<Vec<DensePolynomial<E>>>()
  }
}

pub struct MultiSparseMatPolynomialAsDense<E: ExtensionField> {
  batch_size: usize,
  val: Vec<DensePolynomial<E>>,
  row: AddrTimestamps<E>,
  col: AddrTimestamps<E>,
  comb_ops: DensePolynomial<E>,
  comb_mem: DensePolynomial<E>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct SparseMatPolyCommitment<E: ExtensionField> {
  batch_size: usize,
  num_ops: usize,
  num_mem_cells: usize,
  _phantom: E,
}

impl<E: ExtensionField> SparseMatPolyCommitment<E> {
  pub fn append_to_transcript(&self, transcript: &mut Transcript<E>) {
    append_field_to_transcript(transcript, E::from(self.batch_size as u64));
    append_field_to_transcript(transcript, E::from(self.num_ops as u64));
    append_field_to_transcript(transcript, E::from(self.num_mem_cells as u64));
  }
}

impl<E: ExtensionField> SparseMatPolynomial<E> {
  pub fn new(num_vars_x: usize, num_vars_y: usize, M: Vec<SparseMatEntry<E>>) -> Self {
    SparseMatPolynomial {
      num_vars_x,
      num_vars_y,
      M,
    }
  }

  pub fn get_num_nz_entries(&self) -> usize {
    self.M.len().next_power_of_two()
  }

  fn sparse_to_dense_vecs(&self, N: usize) -> (Vec<usize>, Vec<usize>, Vec<E>) {
    assert!(N >= self.get_num_nz_entries());
    let mut ops_row: Vec<usize> = vec![0; N];
    let mut ops_col: Vec<usize> = vec![0; N];
    let mut val: Vec<E> = vec![E::ZERO; N];

    for i in 0..self.M.len() {
      ops_row[i] = self.M[i].row;
      ops_col[i] = self.M[i].col;
      val[i] = self.M[i].val;
    }
    (ops_row, ops_col, val)
  }

  fn multi_sparse_to_dense_rep(
    sparse_polys: &[&SparseMatPolynomial<E>],
  ) -> MultiSparseMatPolynomialAsDense<E> {
    assert!(!sparse_polys.is_empty());
    for i in 1..sparse_polys.len() {
      assert_eq!(sparse_polys[i].num_vars_x, sparse_polys[0].num_vars_x);
      assert_eq!(sparse_polys[i].num_vars_y, sparse_polys[0].num_vars_y);
    }

    let N = (0..sparse_polys.len())
      .map(|i| sparse_polys[i].get_num_nz_entries())
      .max()
      .unwrap();

    let mut ops_row_vec: Vec<Vec<usize>> = Vec::new();
    let mut ops_col_vec: Vec<Vec<usize>> = Vec::new();
    let mut val_vec: Vec<DensePolynomial<E>> = Vec::new();
    for poly in sparse_polys {
      let (ops_row, ops_col, val) = poly.sparse_to_dense_vecs(N);
      ops_row_vec.push(ops_row);
      ops_col_vec.push(ops_col);
      val_vec.push(DensePolynomial::new(val));
    }

    let any_poly = &sparse_polys[0];

    let num_mem_cells = if any_poly.num_vars_x > any_poly.num_vars_y {
      any_poly.num_vars_x.pow2()
    } else {
      any_poly.num_vars_y.pow2()
    };

    let row = AddrTimestamps::new(num_mem_cells, N, ops_row_vec);
    let col = AddrTimestamps::new(num_mem_cells, N, ops_col_vec);

    let ret_row = row.clone();
    let ret_col = col.clone();
    let ret_val_vec = val_vec.clone();

    // combine polynomials into a single polynomial for commitment purposes
    let comb_ops = DensePolynomial::merge(
      row
        .ops_addr
        .into_iter()
        .chain(row.read_ts.into_iter())
        .chain(col.ops_addr.into_iter())
        .chain(col.read_ts.into_iter())
        .chain(val_vec.into_iter()),
    );
    let mut comb_mem = row.audit_ts.clone();
    comb_mem.extend(&col.audit_ts);

    MultiSparseMatPolynomialAsDense {
      batch_size: sparse_polys.len(),
      row: ret_row,
      col: ret_col,
      val: ret_val_vec,
      comb_ops,
      comb_mem,
    }
  }

  fn evaluate_with_tables(&self, eval_table_rx: &[E], eval_table_ry: &[E]) -> E {
    assert_eq!(self.num_vars_x.pow2(), eval_table_rx.len());
    assert_eq!(self.num_vars_y.pow2(), eval_table_ry.len());

    (0..self.M.len())
      .map(|i| {
        let row = self.M[i].row;
        let col = self.M[i].col;
        let val = &self.M[i].val;
        eval_table_rx[row] * eval_table_ry[col] * *val
      })
      .sum()
  }

  pub fn multi_evaluate(polys: &[&SparseMatPolynomial<E>], rx: &[E], ry: &[E]) -> Vec<E> {
    let eval_table_rx = EqPolynomial::new(rx.to_vec()).evals();
    let eval_table_ry = EqPolynomial::new(ry.to_vec()).evals();

    (0..polys.len())
      .map(|i| polys[i].evaluate_with_tables(&eval_table_rx, &eval_table_ry))
      .collect::<Vec<E>>()
  }

  pub fn _multiply_vec(&self, num_rows: usize, num_cols: usize, z: &[E]) -> Vec<E> {
    assert_eq!(z.len(), num_cols);

    (0..self.M.len())
      .map(|i| {
        let row = self.M[i].row;
        let col = self.M[i].col;
        let val = &self.M[i].val;
        assert!(col < num_cols);
        (row, *val * z[col])
      })
      .fold(vec![E::ZERO; num_rows], |mut Mz, (r, v)| {
        Mz[r] = Mz[r] + v;
        Mz
      })
  }

  // Z is consisted of vector segments
  // Z[i] contains entries i * max_num_cols ~ i * max_num_cols + num_cols
  pub fn multiply_vec_disjoint_rounds(
    &self, 
    num_rows: usize, 
    max_num_cols: usize, 
    z: &Vec<Vec<E>>,
  ) -> Vec<E> {
    (0..self.M.len())
      .map(|i| {
        let row = self.M[i].row;
        let col = self.M[i].col;
        let val = self.M[i].val.clone();
        let w = col / max_num_cols;
        let y = col % max_num_cols;
        (row, if w < z.len() && y < z[w].len() { val * z[w][y] } else { E::ZERO })
      })
      .fold(vec![E::ZERO; num_rows], |mut Mz, (r, v)| {
        Mz[r] += v;
        Mz
      })
  }

  pub fn compute_eval_table_sparse(&self, rx: &[E], num_rows: usize, num_cols: usize) -> Vec<E> {
    assert_eq!(rx.len(), num_rows);

    let mut M_evals: Vec<E> = vec![E::ZERO; num_cols];

    for i in 0..self.M.len() {
      let entry = &self.M[i];
      M_evals[entry.col] = M_evals[entry.col] + rx[entry.row] * entry.val;
    }
    M_evals
  }

  // Store the result in a vector divided into num_segs segments
  // output[i] stores entry i * max_num_cols ~ i * max_num_cols + num_cols of the original vector
  pub fn compute_eval_table_sparse_disjoint_rounds(
    &self,
    rx: &[E],
    num_rows: usize,
    num_segs: usize,
    max_num_cols: usize,
    num_cols: usize,
  ) -> Vec<Vec<E>> {
    assert!(rx.len() >= num_rows);

    let mut M_evals: Vec<Vec<E>> = vec![vec![E::ZERO; num_cols]; num_segs];

    for i in 0..self.M.len() {
      let entry = &self.M[i];
      M_evals[entry.col / max_num_cols][entry.col % max_num_cols] += rx[entry.row] * entry.val;
    }
    M_evals
  }

  pub fn multi_commit(
    sparse_polys: &[&SparseMatPolynomial<E>],
  ) -> (
    SparseMatPolyCommitment<E>,
    MultiSparseMatPolynomialAsDense<E>,
  ) {
    let batch_size = sparse_polys.len();
    let dense = SparseMatPolynomial::multi_sparse_to_dense_rep(sparse_polys);

    (
      SparseMatPolyCommitment {
        batch_size,
        num_mem_cells: dense.row.audit_ts.len(),
        num_ops: dense.row.read_ts[0].len(),
        _phantom: E::ZERO,
      },
      dense,
    )
  }
}

impl<E: ExtensionField> MultiSparseMatPolynomialAsDense<E> {
  pub fn deref(&self, row_mem_val: &[E], col_mem_val: &[E]) -> Derefs<E> {
    let row_ops_val = self.row.deref(row_mem_val);
    let col_ops_val = self.col.deref(col_mem_val);

    Derefs::new(row_ops_val, col_ops_val)
  }
}

#[derive(Debug)]
struct ProductLayer<E: ExtensionField> {
  init: ProductCircuit<E>,
  read_vec: Vec<ProductCircuit<E>>,
  write_vec: Vec<ProductCircuit<E>>,
  audit: ProductCircuit<E>,
}

#[derive(Debug)]
struct Layers<E: ExtensionField> {
  prod_layer: ProductLayer<E>,
}

impl<E: ExtensionField> Layers<E> {
  fn build_hash_layer(
    eval_table: &[E],
    addrs_vec: &[DensePolynomial<E>],
    derefs_vec: &[DensePolynomial<E>],
    read_ts_vec: &[DensePolynomial<E>],
    audit_ts: &DensePolynomial<E>,
    r_mem_check: &(E, E),
  ) -> (
    DensePolynomial<E>,
    Vec<DensePolynomial<E>>,
    Vec<DensePolynomial<E>>,
    DensePolynomial<E>,
  ) {
    let (r_hash, r_multiset_check) = r_mem_check;

    //hash(addr, val, ts) = ts * r_hash_sqr + val * r_hash + addr
    let r_hash_sqr = *r_hash * *r_hash;
    let hash_func = |addr: &E, val: &E, ts: &E| -> E { *ts * r_hash_sqr + *val * *r_hash + *addr };

    // hash init and audit that does not depend on #instances
    let num_mem_cells = eval_table.len();
    let poly_init_hashed = DensePolynomial::new(
      (0..num_mem_cells)
        .map(|i| {
          // at init time, addr is given by i, init value is given by eval_table, and ts = 0
          hash_func(&E::from(i as u64), &eval_table[i], &E::ZERO) - *r_multiset_check
        })
        .collect::<Vec<E>>(),
    );
    let poly_audit_hashed = DensePolynomial::new(
      (0..num_mem_cells)
        .map(|i| {
          // at audit time, addr is given by i, value is given by eval_table, and ts is given by audit_ts
          hash_func(&E::from(i as u64), &eval_table[i], &audit_ts[i]) - *r_multiset_check
        })
        .collect::<Vec<E>>(),
    );

    // hash read and write that depends on #instances
    let mut poly_read_hashed_vec: Vec<DensePolynomial<E>> = Vec::new();
    let mut poly_write_hashed_vec: Vec<DensePolynomial<E>> = Vec::new();
    for i in 0..addrs_vec.len() {
      let (addrs, derefs, read_ts) = (&addrs_vec[i], &derefs_vec[i], &read_ts_vec[i]);
      assert_eq!(addrs.len(), derefs.len());
      assert_eq!(addrs.len(), read_ts.len());
      let num_ops = addrs.len();
      let poly_read_hashed = DensePolynomial::new(
        (0..num_ops)
          .map(|i| {
            // at read time, addr is given by addrs, value is given by derefs, and ts is given by read_ts
            hash_func(&addrs[i], &derefs[i], &read_ts[i]) - *r_multiset_check
          })
          .collect::<Vec<E>>(),
      );
      poly_read_hashed_vec.push(poly_read_hashed);

      let poly_write_hashed = DensePolynomial::new(
        (0..num_ops)
          .map(|i| {
            // at write time, addr is given by addrs, value is given by derefs, and ts is given by write_ts = read_ts + 1
            hash_func(&addrs[i], &derefs[i], &(read_ts[i] + E::ONE)) - *r_multiset_check
          })
          .collect::<Vec<E>>(),
      );
      poly_write_hashed_vec.push(poly_write_hashed);
    }

    (
      poly_init_hashed,
      poly_read_hashed_vec,
      poly_write_hashed_vec,
      poly_audit_hashed,
    )
  }

  pub fn new(
    eval_table: &[E],
    addr_timestamps: &AddrTimestamps<E>,
    poly_ops_val: &[DensePolynomial<E>],
    r_mem_check: &(E, E),
  ) -> Self {
    let (poly_init_hashed, poly_read_hashed_vec, poly_write_hashed_vec, poly_audit_hashed) =
      Layers::build_hash_layer(
        eval_table,
        &addr_timestamps.ops_addr,
        poly_ops_val,
        &addr_timestamps.read_ts,
        &addr_timestamps.audit_ts,
        r_mem_check,
      );

    let prod_init = ProductCircuit::new(&poly_init_hashed);
    let prod_read_vec = (0..poly_read_hashed_vec.len())
      .map(|i| ProductCircuit::new(&poly_read_hashed_vec[i]))
      .collect::<Vec<ProductCircuit<E>>>();
    let prod_write_vec = (0..poly_write_hashed_vec.len())
      .map(|i| ProductCircuit::new(&poly_write_hashed_vec[i]))
      .collect::<Vec<ProductCircuit<E>>>();
    let prod_audit = ProductCircuit::new(&poly_audit_hashed);

    // subset audit check
    let hashed_writes: E = (0..prod_write_vec.len())
      .map(|i| prod_write_vec[i].evaluate())
      .product();
    let hashed_write_set: E = prod_init.evaluate() * hashed_writes;

    let hashed_reads: E = (0..prod_read_vec.len())
      .map(|i| prod_read_vec[i].evaluate())
      .product();
    let hashed_read_set: E = hashed_reads * prod_audit.evaluate();

    //assert_eq!(hashed_read_set, hashed_write_set);
    debug_assert_eq!(hashed_read_set, hashed_write_set);

    Layers {
      prod_layer: ProductLayer {
        init: prod_init,
        read_vec: prod_read_vec,
        write_vec: prod_write_vec,
        audit: prod_audit,
      },
    }
  }
}

#[derive(Debug)]
struct PolyEvalNetwork<E: ExtensionField> {
  row_layers: Layers<E>,
  col_layers: Layers<E>,
}

impl<E: ExtensionField> PolyEvalNetwork<E> {
  pub fn new(
    dense: &MultiSparseMatPolynomialAsDense<E>,
    derefs: &Derefs<E>,
    mem_rx: &[E],
    mem_ry: &[E],
    r_mem_check: &(E, E),
  ) -> Self {
    let row_layers = Layers::new(mem_rx, &dense.row, &derefs.row_ops_val, r_mem_check);
    let col_layers = Layers::new(mem_ry, &dense.col, &derefs.col_ops_val, r_mem_check);

    PolyEvalNetwork {
      row_layers,
      col_layers,
    }
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct HashLayerProof<E: ExtensionField> {
  eval_row: (Vec<E>, Vec<E>, E),
  eval_col: (Vec<E>, Vec<E>, E),
  eval_val: Vec<E>,
  eval_derefs: (Vec<E>, Vec<E>),
  pub proof_ops: PolyEvalProof<E>,
  pub proof_mem: PolyEvalProof<E>,
  pub proof_derefs: DerefsEvalProof<E>,
}

impl<E: ExtensionField> HashLayerProof<E> {
  fn protocol_name() -> &'static [u8] {
    b"Sparse polynomial hash layer proof"
  }

  fn prove_helper(
    rand: (&Vec<E>, &Vec<E>),
    addr_timestamps: &AddrTimestamps<E>,
  ) -> (Vec<E>, Vec<E>, E) {
    let (rand_mem, rand_ops) = rand;

    // decommit ops-addr at rand_ops
    let mut eval_ops_addr_vec: Vec<E> = Vec::new();
    for i in 0..addr_timestamps.ops_addr.len() {
      let eval_ops_addr = addr_timestamps.ops_addr[i].evaluate(rand_ops);
      eval_ops_addr_vec.push(eval_ops_addr);
    }

    // decommit read_ts at rand_ops
    let mut eval_read_ts_vec: Vec<E> = Vec::new();
    for i in 0..addr_timestamps.read_ts.len() {
      let eval_read_ts = addr_timestamps.read_ts[i].evaluate(rand_ops);
      eval_read_ts_vec.push(eval_read_ts);
    }

    // decommit audit-ts at rand_mem
    let eval_audit_ts = addr_timestamps.audit_ts.evaluate(rand_mem);

    (eval_ops_addr_vec, eval_read_ts_vec, eval_audit_ts)
  }

  fn prove(
    rand: (&Vec<E>, &Vec<E>),
    dense: &MultiSparseMatPolynomialAsDense<E>,
    derefs: &Derefs<E>,
    transcript: &mut Transcript<E>,
    random_tape: &mut RandomTape<E>,
  ) -> Self {
    append_protocol_name(
      transcript,
      HashLayerProof::<E>::protocol_name(),
    );

    let (rand_mem, rand_ops) = rand;

    // decommit derefs at rand_ops
    let eval_row_ops_val = (0..derefs.row_ops_val.len())
      .map(|i| derefs.row_ops_val[i].evaluate(rand_ops))
      .collect::<Vec<E>>();
    let eval_col_ops_val = (0..derefs.col_ops_val.len())
      .map(|i| derefs.col_ops_val[i].evaluate(rand_ops))
      .collect::<Vec<E>>();
    let proof_derefs = DerefsEvalProof::prove(
      derefs,
      &eval_row_ops_val,
      &eval_col_ops_val,
      rand_ops,
      transcript,
      random_tape,
    );
    let eval_derefs = (eval_row_ops_val, eval_col_ops_val);

    // evaluate row_addr, row_read-ts, col_addr, col_read-ts, val at rand_ops
    // evaluate row_audit_ts and col_audit_ts at rand_mem
    let (eval_row_addr_vec, eval_row_read_ts_vec, eval_row_audit_ts) =
      HashLayerProof::prove_helper((rand_mem, rand_ops), &dense.row);
    let (eval_col_addr_vec, eval_col_read_ts_vec, eval_col_audit_ts) =
      HashLayerProof::prove_helper((rand_mem, rand_ops), &dense.col);
    let eval_val_vec = (0..dense.val.len())
      .map(|i| dense.val[i].evaluate(rand_ops))
      .collect::<Vec<E>>();

    // form a single decommitment using comm_comb_ops
    let mut evals_ops: Vec<E> = Vec::new();
    evals_ops.extend(&eval_row_addr_vec);
    evals_ops.extend(&eval_row_read_ts_vec);
    evals_ops.extend(&eval_col_addr_vec);
    evals_ops.extend(&eval_col_read_ts_vec);
    evals_ops.extend(&eval_val_vec);
    evals_ops.resize(evals_ops.len().next_power_of_two(), E::ZERO);
    append_field_vector_to_transcript(transcript, &evals_ops);
    let challenges_ops =
      challenge_vector(transcript, b"challenge_combine_n_to_one", evals_ops.len().log_2());

    let mut poly_evals_ops = DensePolynomial::new(evals_ops);
    for i in (0..challenges_ops.len()).rev() {
      poly_evals_ops.bound_poly_var_bot(&challenges_ops[i]);
    }
    assert_eq!(poly_evals_ops.len(), 1);
    let joint_claim_eval_ops = poly_evals_ops[0];
    let mut r_joint_ops = challenges_ops;
    r_joint_ops.extend(rand_ops);
    debug_assert_eq!(dense.comb_ops.evaluate(&r_joint_ops), joint_claim_eval_ops);
    append_field_to_transcript(transcript, joint_claim_eval_ops);

    let proof_ops = PolyEvalProof::prove(
      &dense.comb_ops,
      &r_joint_ops,
      &joint_claim_eval_ops,
      transcript,
      random_tape,
    );

    // form a single decommitment using comb_comb_mem at rand_mem
    let evals_mem: Vec<E> = vec![eval_row_audit_ts, eval_col_audit_ts];
    append_field_vector_to_transcript(transcript, &evals_mem);
    let challenges_mem =
      challenge_vector(transcript, b"challenge_combine_two_to_one", evals_mem.len().log_2());

    let mut poly_evals_mem = DensePolynomial::new(evals_mem);
    for i in (0..challenges_mem.len()).rev() {
      poly_evals_mem.bound_poly_var_bot(&challenges_mem[i]);
    }
    assert_eq!(poly_evals_mem.len(), 1);
    let joint_claim_eval_mem = poly_evals_mem[0];
    let mut r_joint_mem = challenges_mem;
    r_joint_mem.extend(rand_mem);
    debug_assert_eq!(dense.comb_mem.evaluate(&r_joint_mem), joint_claim_eval_mem);
    append_field_to_transcript(transcript, joint_claim_eval_mem);

    let proof_mem = PolyEvalProof::prove(
      &dense.comb_mem,
      &r_joint_mem,
      &joint_claim_eval_mem,
      transcript,
      random_tape,
    );

    HashLayerProof {
      eval_row: (eval_row_addr_vec, eval_row_read_ts_vec, eval_row_audit_ts),
      eval_col: (eval_col_addr_vec, eval_col_read_ts_vec, eval_col_audit_ts),
      eval_val: eval_val_vec,
      eval_derefs,
      proof_ops,
      proof_mem,
      proof_derefs,
    }
  }

  fn verify_helper(
    rand: &(&Vec<E>, &Vec<E>),
    claims: &(E, Vec<E>, Vec<E>, E),
    eval_ops_val: &[E],
    eval_ops_addr: &[E],
    eval_read_ts: &[E],
    eval_audit_ts: &E,
    r: &[E],
    r_hash: &E,
    r_multiset_check: &E,
  ) -> Result<(), ProofVerifyError> {
    let r_hash_sqr = *r_hash * *r_hash;
    let hash_func = |addr: &E, val: &E, ts: &E| -> E { *ts * r_hash_sqr + *val * *r_hash + *addr };

    let (rand_mem, _rand_ops) = rand;
    let (claim_init, claim_read, claim_write, claim_audit) = claims;

    // init
    let eval_init_addr = IdentityPolynomial::new(rand_mem.len()).evaluate(rand_mem);
    let eval_init_val = EqPolynomial::new(r.to_vec()).evaluate(rand_mem);
    let hash_init_at_rand_mem =
      hash_func(&eval_init_addr, &eval_init_val, &E::ZERO) - *r_multiset_check;

    // verify the claim_last of init chunk
    assert_eq!(&hash_init_at_rand_mem, claim_init);

    // read
    for i in 0..eval_ops_addr.len() {
      let hash_read_at_rand_ops =
        hash_func(&eval_ops_addr[i], &eval_ops_val[i], &eval_read_ts[i]) - *r_multiset_check;
      // verify the claim_last of init chunk
      assert_eq!(&hash_read_at_rand_ops, &claim_read[i]);
    }

    // write: shares addr, val component; only decommit write_ts
    for i in 0..eval_ops_addr.len() {
      let eval_write_ts = eval_read_ts[i] + E::ONE;
      let hash_write_at_rand_ops =
        hash_func(&eval_ops_addr[i], &eval_ops_val[i], &eval_write_ts) - *r_multiset_check;
      // verify the claim_last of init chunk
      assert_eq!(&hash_write_at_rand_ops, &claim_write[i]);
    }

    // audit: shares addr and val with init
    let eval_audit_addr = eval_init_addr;
    let eval_audit_val = eval_init_val;
    let hash_audit_at_rand_mem =
      hash_func(&eval_audit_addr, &eval_audit_val, eval_audit_ts) - *r_multiset_check;
    assert_eq!(&hash_audit_at_rand_mem, claim_audit); // verify the last step of the sum-check for audit

    Ok(())
  }

  fn verify(
    &self,
    rand: (&Vec<E>, &Vec<E>),
    claims_row: &(E, Vec<E>, Vec<E>, E),
    claims_col: &(E, Vec<E>, Vec<E>, E),
    claims_dotp: &[E],
    _comm: &SparseMatPolyCommitment<E>,
    rx: &[E],
    ry: &[E],
    r_hash: &E,
    r_multiset_check: &E,
    transcript: &mut Transcript<E>,
  ) -> Result<(), ProofVerifyError> {
    let timer = Timer::new("verify_hash_proof");
    append_protocol_name(
      transcript,
      HashLayerProof::<E>::protocol_name(),
    );

    let (rand_mem, rand_ops) = rand;

    // verify derefs at rand_ops
    let (eval_row_ops_val, eval_col_ops_val) = &self.eval_derefs;
    assert_eq!(eval_row_ops_val.len(), eval_col_ops_val.len());
    self
      .proof_derefs
      .verify(rand_ops, eval_row_ops_val, eval_col_ops_val, transcript)?;

    // verify the decommitments used in evaluation sum-check
    let eval_val_vec = &self.eval_val;
    assert_eq!(claims_dotp.len(), 3 * eval_row_ops_val.len());
    for i in 0..claims_dotp.len() / 3 {
      let claim_row_ops_val = claims_dotp[3 * i];
      let claim_col_ops_val = claims_dotp[3 * i + 1];
      let claim_val = claims_dotp[3 * i + 2];

      assert_eq!(claim_row_ops_val, eval_row_ops_val[i]);
      assert_eq!(claim_col_ops_val, eval_col_ops_val[i]);
      assert_eq!(claim_val, eval_val_vec[i]);
    }

    // verify addr-timestamps using comm_comb_ops at rand_ops
    let (eval_row_addr_vec, eval_row_read_ts_vec, eval_row_audit_ts) = &self.eval_row;
    let (eval_col_addr_vec, eval_col_read_ts_vec, eval_col_audit_ts) = &self.eval_col;

    let mut evals_ops: Vec<E> = Vec::new();
    evals_ops.extend(eval_row_addr_vec);
    evals_ops.extend(eval_row_read_ts_vec);
    evals_ops.extend(eval_col_addr_vec);
    evals_ops.extend(eval_col_read_ts_vec);
    evals_ops.extend(eval_val_vec);
    evals_ops.resize(evals_ops.len().next_power_of_two(), E::ZERO);
    append_field_vector_to_transcript(transcript, &evals_ops);
    let challenges_ops =
      challenge_vector(transcript, b"challenge_combine_n_to_one", evals_ops.len().log_2());

    let mut poly_evals_ops = DensePolynomial::new(evals_ops);
    for i in (0..challenges_ops.len()).rev() {
      poly_evals_ops.bound_poly_var_bot(&challenges_ops[i]);
    }
    assert_eq!(poly_evals_ops.len(), 1);
    let joint_claim_eval_ops = poly_evals_ops[0];
    let mut r_joint_ops = challenges_ops;
    r_joint_ops.extend(rand_ops);
    append_field_to_transcript(transcript, joint_claim_eval_ops);
    self
      .proof_ops
      .verify_plain(transcript, &r_joint_ops, &joint_claim_eval_ops)?;

    // verify proof-mem using comm_comb_mem at rand_mem
    // form a single decommitment using comb_comb_mem at rand_mem
    let evals_mem: Vec<E> = vec![*eval_row_audit_ts, *eval_col_audit_ts];
    append_field_vector_to_transcript(transcript, &evals_mem);
    let challenges_mem =
      challenge_vector(transcript, b"challenge_combine_two_to_one", evals_mem.len().log_2());

    let mut poly_evals_mem = DensePolynomial::new(evals_mem);
    for i in (0..challenges_mem.len()).rev() {
      poly_evals_mem.bound_poly_var_bot(&challenges_mem[i]);
    }
    assert_eq!(poly_evals_mem.len(), 1);
    let joint_claim_eval_mem = poly_evals_mem[0];
    let mut r_joint_mem = challenges_mem;
    r_joint_mem.extend(rand_mem);
    append_field_to_transcript(transcript, joint_claim_eval_mem);

    self
      .proof_mem
      .verify_plain(transcript, &r_joint_mem, &joint_claim_eval_mem)?;

    // verify the claims from the product layer
    let (eval_ops_addr, eval_read_ts, eval_audit_ts) = &self.eval_row;
    HashLayerProof::verify_helper(
      &(rand_mem, rand_ops),
      claims_row,
      eval_row_ops_val,
      eval_ops_addr,
      eval_read_ts,
      eval_audit_ts,
      rx,
      r_hash,
      r_multiset_check,
    )?;

    let (eval_ops_addr, eval_read_ts, eval_audit_ts) = &self.eval_col;
    HashLayerProof::verify_helper(
      &(rand_mem, rand_ops),
      claims_col,
      eval_col_ops_val,
      eval_ops_addr,
      eval_read_ts,
      eval_audit_ts,
      ry,
      r_hash,
      r_multiset_check,
    )?;

    timer.stop();
    Ok(())
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ProductLayerProof<E: ExtensionField> {
  eval_row: (E, Vec<E>, Vec<E>, E),
  eval_col: (E, Vec<E>, Vec<E>, E),
  eval_val: (Vec<E>, Vec<E>),
  pub proof_mem: ProductCircuitEvalProofBatched<E>,
  pub proof_ops: ProductCircuitEvalProofBatched<E>,
}

impl<E: ExtensionField> ProductLayerProof<E> {
  fn protocol_name() -> &'static [u8] {
    b"Sparse polynomial product layer proof"
  }

  pub fn prove(
    row_prod_layer: &mut ProductLayer<E>,
    col_prod_layer: &mut ProductLayer<E>,
    dense: &MultiSparseMatPolynomialAsDense<E>,
    derefs: &Derefs<E>,
    r_header: E,
    eval: &[E],
    transcript: &mut Transcript<E>,
  ) -> (Self, Vec<E>, Vec<E>) {
    append_protocol_name(
      transcript,
      ProductLayerProof::<E>::protocol_name(),
    );

    let row_eval_init = row_prod_layer.init.evaluate();
    let row_eval_audit = row_prod_layer.audit.evaluate();
    let row_eval_read = (0..row_prod_layer.read_vec.len())
      .map(|i| row_prod_layer.read_vec[i].evaluate())
      .collect::<Vec<E>>();
    let row_eval_write = (0..row_prod_layer.write_vec.len())
      .map(|i| row_prod_layer.write_vec[i].evaluate())
      .collect::<Vec<E>>();

    // subset check
    let ws: E = (0..row_eval_write.len())
      .map(|i| row_eval_write[i])
      .product();
    let rs: E = (0..row_eval_read.len()).map(|i| row_eval_read[i]).product();
    assert_eq!(row_eval_init * ws, rs * row_eval_audit);

    append_field_to_transcript(transcript, row_eval_init);
    append_field_vector_to_transcript(transcript, &row_eval_read);
    append_field_vector_to_transcript(transcript, &row_eval_write);
    append_field_to_transcript(transcript, row_eval_audit);

    let col_eval_init = col_prod_layer.init.evaluate();
    let col_eval_audit = col_prod_layer.audit.evaluate();
    let col_eval_read: Vec<E> = (0..col_prod_layer.read_vec.len())
      .map(|i| col_prod_layer.read_vec[i].evaluate())
      .collect();
    let col_eval_write: Vec<E> = (0..col_prod_layer.write_vec.len())
      .map(|i| col_prod_layer.write_vec[i].evaluate())
      .collect();

    // subset check
    let ws: E = (0..col_eval_write.len())
      .map(|i| col_eval_write[i])
      .product();
    let rs: E = (0..col_eval_read.len()).map(|i| col_eval_read[i]).product();
    assert_eq!(col_eval_init * ws, rs * col_eval_audit);

    append_field_to_transcript(transcript, col_eval_init);
    append_field_vector_to_transcript(transcript, &col_eval_read);
    append_field_vector_to_transcript(transcript, &col_eval_write);
    append_field_to_transcript(transcript, col_eval_audit);

    // prepare dotproduct circuit for batching then with ops-related product circuits
    assert_eq!(eval.len(), derefs.row_ops_val.len());
    assert_eq!(eval.len(), derefs.col_ops_val.len());
    assert_eq!(eval.len(), dense.val.len());
    let mut dotp_circuit_left_vec: Vec<DotProductCircuit<E>> = Vec::new();
    let mut dotp_circuit_right_vec: Vec<DotProductCircuit<E>> = Vec::new();
    let mut eval_dotp_left_vec: Vec<E> = Vec::new();
    let mut eval_dotp_right_vec: Vec<E> = Vec::new();
    for i in 0..derefs.row_ops_val.len() {
      // evaluate sparse polynomial evaluation using two dotp checks
      let left = derefs.row_ops_val[i].clone();
      let right = derefs.col_ops_val[i].clone();
      let weights = dense.val[i].clone();

      // build two dot product circuits to prove evaluation of sparse polynomial
      let mut dotp_circuit = DotProductCircuit::new(left, right, weights);
      let (dotp_circuit_left, dotp_circuit_right) = dotp_circuit.split();

      let (eval_dotp_left, eval_dotp_right) =
        (dotp_circuit_left.evaluate(), dotp_circuit_right.evaluate());

      append_field_to_transcript(transcript, eval_dotp_left);
      append_field_to_transcript(transcript, eval_dotp_right);

      assert_eq!(r_header * (eval_dotp_left + eval_dotp_right), eval[i]);

      eval_dotp_left_vec.push(eval_dotp_left);
      eval_dotp_right_vec.push(eval_dotp_right);

      dotp_circuit_left_vec.push(dotp_circuit_left);
      dotp_circuit_right_vec.push(dotp_circuit_right);
    }

    // The number of operations into the memory encoded by rx and ry are always the same (by design)
    // So we can produce a batched product proof for all of them at the same time.
    // prove the correctness of claim_row_eval_read, claim_row_eval_write, claim_col_eval_read, and claim_col_eval_write
    // TODO: we currently only produce proofs for 3 batched sparse polynomial evaluations
    let num_instances = row_prod_layer.read_vec.len();
    let mut prod_circuit_list = Vec::new();
    let mut dotp_circuit_list = Vec::new();
    let (_, dotp_left_vec) = dotp_circuit_left_vec.split_at_mut(0);
    let (_, dotp_right_vec) = dotp_circuit_right_vec.split_at_mut(0);
    // row_read
    for i in 0..num_instances {
      prod_circuit_list.push(row_prod_layer.read_vec[i].clone());
      dotp_circuit_list.push(dotp_left_vec[i].clone());
      dotp_circuit_list.push(dotp_right_vec[i].clone());
    }
    // row_write
    for i in 0..num_instances {
      prod_circuit_list.push(row_prod_layer.write_vec[i].clone());
    }
    // col_read
    for i in 0..num_instances {
      prod_circuit_list.push(col_prod_layer.read_vec[i].clone());
    }
    // col_write
    for i in 0..num_instances {
      prod_circuit_list.push(col_prod_layer.write_vec[i].clone());
    }

    let (proof_ops, rand_ops) = ProductCircuitEvalProofBatched::prove(
      &mut prod_circuit_list.iter_mut().map(|i| &mut *i).collect(),
      &mut dotp_circuit_list.iter_mut().map(|i| &mut *i).collect(),
      transcript,
    );

    // produce a batched proof of memory-related product circuits
    let (proof_mem, rand_mem) = ProductCircuitEvalProofBatched::prove(
      &mut vec![
        &mut row_prod_layer.init,
        &mut row_prod_layer.audit,
        &mut col_prod_layer.init,
        &mut col_prod_layer.audit,
      ],
      &mut Vec::new(),
      transcript,
    );

    let product_layer_proof = ProductLayerProof {
      eval_row: (row_eval_init, row_eval_read, row_eval_write, row_eval_audit),
      eval_col: (col_eval_init, col_eval_read, col_eval_write, col_eval_audit),
      eval_val: (eval_dotp_left_vec, eval_dotp_right_vec),
      proof_mem,
      proof_ops,
    };

    let product_layer_proof_encoded: Vec<u8> = bincode::serialize(&product_layer_proof).unwrap();
    let msg = format!(
      "len_product_layer_proof {:?}",
      product_layer_proof_encoded.len()
    );
    Timer::print(&msg);

    (product_layer_proof, rand_mem, rand_ops)
  }

  pub fn verify(
    &self,
    num_ops: usize,
    num_cells: usize,
    r_header: E,
    eval: &[E],
    transcript: &mut Transcript<E>,
  ) -> Result<(Vec<E>, Vec<E>, Vec<E>, Vec<E>, Vec<E>), ProofVerifyError> {
    append_protocol_name(
      transcript,
      ProductLayerProof::<E>::protocol_name(),
    );
    let timer = Timer::new("verify_prod_proof");
    let num_instances = eval.len();

    // subset check
    let (row_eval_init, row_eval_read, row_eval_write, row_eval_audit) = &self.eval_row;
    assert_eq!(row_eval_write.len(), num_instances);
    assert_eq!(row_eval_read.len(), num_instances);
    let ws: E = (0..row_eval_write.len())
      .map(|i| row_eval_write[i])
      .product();
    let rs: E = (0..row_eval_read.len()).map(|i| row_eval_read[i]).product();
    assert_eq!(*row_eval_init * ws, rs * *row_eval_audit);

    append_field_to_transcript(transcript, *row_eval_init);
    append_field_vector_to_transcript(transcript, &row_eval_read);
    append_field_vector_to_transcript(transcript, &row_eval_write);
    append_field_to_transcript(transcript, *row_eval_audit);

    // subset check
    let (col_eval_init, col_eval_read, col_eval_write, col_eval_audit) = &self.eval_col;
    assert_eq!(col_eval_write.len(), num_instances);
    assert_eq!(col_eval_read.len(), num_instances);
    let ws: E = (0..col_eval_write.len())
      .map(|i| col_eval_write[i])
      .product();
    let rs: E = (0..col_eval_read.len()).map(|i| col_eval_read[i]).product();
    assert_eq!(*col_eval_init * ws, rs * *col_eval_audit);

    append_field_to_transcript(transcript, *col_eval_init);
    append_field_vector_to_transcript(transcript, &col_eval_read);
    append_field_vector_to_transcript(transcript, &col_eval_write);
    append_field_to_transcript(transcript, *col_eval_audit);

    // verify the evaluation of the sparse polynomial
    let (eval_dotp_left, eval_dotp_right) = &self.eval_val;
    assert_eq!(eval_dotp_left.len(), eval_dotp_left.len());
    assert_eq!(eval_dotp_left.len(), num_instances);
    let mut claims_dotp_circuit: Vec<E> = Vec::new();
    for i in 0..num_instances {
      assert_eq!(r_header * (eval_dotp_left[i] + eval_dotp_right[i]), eval[i]);
      append_field_to_transcript(transcript, eval_dotp_left[i]);
      append_field_to_transcript(transcript, eval_dotp_right[i]);

      claims_dotp_circuit.push(eval_dotp_left[i]);
      claims_dotp_circuit.push(eval_dotp_right[i]);
    }

    // verify the correctness of claim_row_eval_read, claim_row_eval_write, claim_col_eval_read, and claim_col_eval_write
    let mut claims_prod_circuit: Vec<E> = Vec::new();
    claims_prod_circuit.extend(row_eval_read);
    claims_prod_circuit.extend(row_eval_write);
    claims_prod_circuit.extend(col_eval_read);
    claims_prod_circuit.extend(col_eval_write);

    let (claims_ops, claims_dotp, rand_ops) = self.proof_ops.verify(
      &claims_prod_circuit,
      &claims_dotp_circuit,
      num_ops,
      transcript,
    );
    // verify the correctness of claim_row_eval_init and claim_row_eval_audit
    let (claims_mem, _claims_mem_dotp, rand_mem) = self.proof_mem.verify(
      &[
        *row_eval_init,
        *row_eval_audit,
        *col_eval_init,
        *col_eval_audit,
      ],
      &Vec::new(),
      num_cells,
      transcript,
    );
    timer.stop();

    Ok((claims_mem, rand_mem, claims_ops, claims_dotp, rand_ops))
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PolyEvalNetworkProof<E: ExtensionField> {
  pub proof_prod_layer: ProductLayerProof<E>,
  pub proof_hash_layer: HashLayerProof<E>,
}

impl<E: ExtensionField> PolyEvalNetworkProof<E> {
  fn protocol_name() -> &'static [u8] {
    b"Sparse polynomial evaluation proof"
  }

  pub fn prove(
    network: &mut PolyEvalNetwork<E>,
    dense: &MultiSparseMatPolynomialAsDense<E>,
    derefs: &Derefs<E>,
    r_header: E,
    evals: &[E],
    transcript: &mut Transcript<E>,
    random_tape: &mut RandomTape<E>,
  ) -> Self {
    append_protocol_name(
      transcript,
      PolyEvalNetworkProof::<E>::protocol_name(),
    );

    let (proof_prod_layer, rand_mem, rand_ops) = ProductLayerProof::prove(
      &mut network.row_layers.prod_layer,
      &mut network.col_layers.prod_layer,
      dense,
      derefs,
      r_header,
      evals,
      transcript,
    );

    // proof of hash layer for row and col
    let proof_hash_layer = HashLayerProof::prove(
      (&rand_mem, &rand_ops),
      dense,
      derefs,
      transcript,
      random_tape,
    );

    PolyEvalNetworkProof {
      proof_prod_layer,
      proof_hash_layer,
    }
  }

  pub fn verify(
    &self,
    comm: &SparseMatPolyCommitment<E>,
    r_header: E,
    evals: &[E],
    rx: &[E],
    ry: &[E],
    r_mem_check: &(E, E),
    nz: usize,
    transcript: &mut Transcript<E>,
  ) -> Result<(), ProofVerifyError> {
    let timer = Timer::new("verify_polyeval_proof");
    append_protocol_name(
      transcript,
      PolyEvalNetworkProof::<E>::protocol_name(),
    );

    let num_instances = evals.len();
    let (r_hash, r_multiset_check) = r_mem_check;

    let num_ops = nz.next_power_of_two();
    let num_cells = rx.len().pow2();
    assert_eq!(rx.len(), ry.len());

    let (claims_mem, rand_mem, mut claims_ops, claims_dotp, rand_ops) = self
      .proof_prod_layer
      .verify(num_ops, num_cells, r_header, evals, transcript)?;
    assert_eq!(claims_mem.len(), 4);
    assert_eq!(claims_ops.len(), 4 * num_instances);
    assert_eq!(claims_dotp.len(), 3 * num_instances);

    let (claims_ops_row, claims_ops_col) = claims_ops.split_at_mut(2 * num_instances);
    let (claims_ops_row_read, claims_ops_row_write) = claims_ops_row.split_at_mut(num_instances);
    let (claims_ops_col_read, claims_ops_col_write) = claims_ops_col.split_at_mut(num_instances);

    // verify the proof of hash layer
    self.proof_hash_layer.verify(
      (&rand_mem, &rand_ops),
      &(
        claims_mem[0],
        claims_ops_row_read.to_vec(),
        claims_ops_row_write.to_vec(),
        claims_mem[1],
      ),
      &(
        claims_mem[2],
        claims_ops_col_read.to_vec(),
        claims_ops_col_write.to_vec(),
        claims_mem[3],
      ),
      &claims_dotp,
      comm,
      rx,
      ry,
      r_hash,
      r_multiset_check,
      transcript,
    )?;
    timer.stop();

    Ok(())
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct SparseMatPolyEvalProof<E: ExtensionField> {
  pub poly_eval_network_proof: PolyEvalNetworkProof<E>,
}

impl<E: ExtensionField> SparseMatPolyEvalProof<E> {
  fn protocol_name() -> &'static [u8] {
    b"Sparse polynomial evaluation proof"
  }

  fn equalize(rx: &[E], ry: &[E]) -> (Vec<E>, Vec<E>) {
    match rx.len().cmp(&ry.len()) {
      Ordering::Less => {
        let diff = ry.len() - rx.len();
        let mut rx_ext = vec![E::ZERO; diff];
        rx_ext.extend(rx);
        (rx_ext, ry.to_vec())
      }
      Ordering::Greater => {
        let diff = rx.len() - ry.len();
        let mut ry_ext = vec![E::ZERO; diff];
        ry_ext.extend(ry);
        (rx.to_vec(), ry_ext)
      }
      Ordering::Equal => (rx.to_vec(), ry.to_vec()),
    }
  }

  pub fn prove(
    dense: &MultiSparseMatPolynomialAsDense<E>,
    r_header: E,
    rx: &[E], // point at which the polynomial is evaluated
    ry: &[E],
    evals: &[E], // a vector evaluation of \widetilde{M}(r = (rx,ry)) for each M
    transcript: &mut Transcript<E>,
    random_tape: &mut RandomTape<E>,
  ) -> SparseMatPolyEvalProof<E> {
    append_protocol_name(
      transcript,
      SparseMatPolyEvalProof::<E>::protocol_name(),
    );

    // ensure there is one eval for each polynomial in dense
    assert_eq!(evals.len(), dense.batch_size);

    let (mem_rx, mem_ry) = {
      // equalize the lengths of rx and ry
      let (rx_ext, ry_ext) = SparseMatPolyEvalProof::equalize(rx, ry);
      let poly_rx = EqPolynomial::new(rx_ext).evals();
      let poly_ry = EqPolynomial::new(ry_ext).evals();
      (poly_rx, poly_ry)
    };

    let derefs = dense.deref(&mem_rx, &mem_ry);

    // commit to non-deterministic choices of the prover
    let timer_commit = Timer::new("commit_nondet_witness");

    timer_commit.stop();

    let poly_eval_network_proof = {
      // produce a random element from the transcript for hash function
      let r_mem_check = challenge_vector(transcript, b"challenge_r_hash", 2);

      // build a network to evaluate the sparse polynomial
      let timer_build_network = Timer::new("build_layered_network");
      let mut net = PolyEvalNetwork::new(
        dense,
        &derefs,
        &mem_rx,
        &mem_ry,
        &(r_mem_check[0], r_mem_check[1]),
      );
      timer_build_network.stop();

      let timer_eval_network = Timer::new("evalproof_layered_network");
      let poly_eval_network_proof = PolyEvalNetworkProof::prove(
        &mut net,
        dense,
        &derefs,
        r_header,
        evals,
        transcript,
        random_tape,
      );
      timer_eval_network.stop();

      poly_eval_network_proof
    };

    SparseMatPolyEvalProof {
      poly_eval_network_proof,
    }
  }

  pub fn verify(
    &self,
    comm: &SparseMatPolyCommitment<E>,
    r_header: E,
    rx: &[E], // point at which the polynomial is evaluated
    ry: &[E],
    evals: &[E], // evaluation of \widetilde{M}(r = (rx,ry))
    transcript: &mut Transcript<E>,
  ) -> Result<(), ProofVerifyError> {
    append_protocol_name(
      transcript,
      SparseMatPolyEvalProof::<E>::protocol_name(),
    );

    // equalize the lengths of rx and ry
    let (rx_ext, ry_ext) = SparseMatPolyEvalProof::equalize(rx, ry);

    let (nz, num_mem_cells) = (comm.num_ops, comm.num_mem_cells);
    assert_eq!(rx_ext.len().pow2(), num_mem_cells);

    // produce a random element from the transcript for hash function
    let r_mem_check = challenge_vector(transcript, b"challenge_r_hash", 2);

    self.poly_eval_network_proof.verify(
      comm,
      r_header,
      evals,
      &rx_ext,
      &ry_ext,
      &(r_mem_check[0], r_mem_check[1]),
      nz,
      transcript,
    )
  }
}

/*
#[cfg(test)]
mod tests {
  use super::*;
  use crate::scalar::Scalar;
  use rand::rngs::OsRng;
  use rand::RngCore;
  #[test]
  fn check_sparse_polyeval_proof() {
    let mut csprng: OsRng = OsRng;

    let num_nz_entries: usize = 256;
    let num_rows: usize = 256;
    let num_cols: usize = 256;
    let num_vars_x: usize = num_rows.log_2();
    let num_vars_y: usize = num_cols.log_2();

    let mut M: Vec<SparseMatEntry<Scalar>> = Vec::new();

    for _i in 0..num_nz_entries {
      M.push(SparseMatEntry::new(
        (csprng.next_u64() % (num_rows as u64)) as usize,
        (csprng.next_u64() % (num_cols as u64)) as usize,
        Scalar::random(&mut csprng),
      ));
    }

    let poly_M = SparseMatPolynomial::new(num_vars_x, num_vars_y, M);

    // commitment
    let (poly_comm, dense) = SparseMatPolynomial::multi_commit(&[&poly_M, &poly_M, &poly_M]);

    // evaluation
    let rx: Vec<Scalar> = (0..num_vars_x)
      .map(|_i| Scalar::random(&mut csprng))
      .collect::<Vec<Scalar>>();
    let ry: Vec<Scalar> = (0..num_vars_y)
      .map(|_i| Scalar::random(&mut csprng))
      .collect::<Vec<Scalar>>();
    let eval = SparseMatPolynomial::multi_evaluate(&[&poly_M], &rx, &ry);
    let evals = vec![eval[0], eval[0], eval[0]];

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let proof = SparseMatPolyEvalProof::prove(
      &dense,
      Scalar::one(),
      &rx,
      &ry,
      &evals,
      &mut prover_transcript,
      &mut random_tape,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(
        &poly_comm,
        Scalar::one(),
        &rx,
        &ry,
        &evals,
        &mut verifier_transcript,
      )
      .is_ok());
  }
}
*/
