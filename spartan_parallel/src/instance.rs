use std::cmp::max;

use crate::errors::R1CSError;
use crate::math::Math;
use crate::scalar::SpartanExtensionField;
use crate::R1CSInstance;

/// `Instance` holds the description of R1CS matrices and a hash of the matrices
#[derive(Clone)]
pub struct Instance<S: SpartanExtensionField> {
  /// Matrix of Instance
  pub inst: crate::R1CSInstance<S>,
  /// Digest of Instance
  pub digest: Vec<u8>,
}

impl<S: SpartanExtensionField> Instance<S> {
  /// Constructs a new `Instance` and an associated satisfying assignment
  pub fn new(
    num_instances: usize,
    max_num_cons: usize,
    num_cons: Vec<usize>,
    max_num_vars: usize,
    num_vars: Vec<usize>,
    A: &Vec<Vec<(usize, usize, [u8; 32])>>,
    B: &Vec<Vec<(usize, usize, [u8; 32])>>,
    C: &Vec<Vec<(usize, usize, [u8; 32])>>,
  ) -> Result<Instance<S>, R1CSError> {
    let (max_num_vars_padded, num_vars_padded, max_num_cons_padded, num_cons_padded) = {
      let max_num_vars_padded = {
        let mut max_num_vars_padded = max_num_vars;

        // ensure that num_vars_padded a power of two
        if max_num_vars_padded.next_power_of_two() != max_num_vars_padded {
          max_num_vars_padded = max_num_vars_padded.next_power_of_two();
        }
        max_num_vars_padded
      };

      let mut num_vars_padded = Vec::new();
      for i in 0..num_vars.len() {
        if num_vars[i] == 0 || num_vars[i] == 1 {
          num_vars_padded.push(2);
        } else {
          num_vars_padded.push(num_vars[i].next_power_of_two());
        }
      }

      let max_num_cons_padded = {
        let mut max_num_cons_padded = max_num_cons;

        // ensure that num_cons_padded is at least 2
        if max_num_cons_padded == 0 || max_num_cons_padded == 1 {
          max_num_cons_padded = 2;
        }

        // ensure that num_cons_padded is power of 2
        if max_num_cons.next_power_of_two() != max_num_cons {
          max_num_cons_padded = max_num_cons.next_power_of_two();
        }
        max_num_cons_padded
      };

      let mut num_cons_padded = Vec::new();
      for i in 0..num_cons.len() {
        if num_cons[i] == 0 || num_cons[i] == 1 {
          num_cons_padded.push(2);
        } else {
          num_cons_padded.push(num_cons[i].next_power_of_two());
        }
      }

      (max_num_vars_padded, num_vars_padded, max_num_cons_padded, num_cons_padded)
    };

    let bytes_to_scalar =
      |b: usize, tups: &[(usize, usize, [u8; 32])]| -> Result<Vec<(usize, usize, S)>, R1CSError> {
        let mut mat: Vec<(usize, usize, S)> = Vec::new();
        for &(row, col, val_bytes) in tups {
          // row must be smaller than num_cons
          if row >= num_cons[b] {
            println!("ROW: {}, NUM_CONS: {}", row, num_cons[b]);
            return Err(R1CSError::InvalidIndex);
          }

          // col must be smaller than num_vars
          if col >= num_vars[b] {
            println!("COL: {}, NUM_VARS: {}", col, num_vars[b]);
            return Err(R1CSError::InvalidIndex);
          }

          let val = S::from_bytes(&val_bytes);
          if val.is_some().unwrap_u8() == 1 {
            // if col >= num_vars, it means that it is referencing a 1 or input in the satisfying
            // assignment
            if col >= num_vars[b] {
              mat.push((row, col + num_vars_padded[b] - num_vars[b], val.unwrap()));
            } else {
              mat.push((row, col, val.unwrap()));
            }
          } else {
            return Err(R1CSError::InvalidScalar);
          }
        }

        // pad with additional constraints up until num_cons_padded if the original constraints were 0 or 1
        // we do not need to pad otherwise because the dummy constraints are implicit in the sum-check protocol
        if num_cons[b] == 0 || num_cons[b] == 1 {
          for i in tups.len()..num_cons_padded[b] {
            mat.push((i, num_vars[b], S::field_zero()));
          }
        }

        Ok(mat)
      };

    let mut A_scalar_list = Vec::new();
    let mut B_scalar_list = Vec::new();
    let mut C_scalar_list = Vec::new();

    for i in 0..num_instances {
      let A_scalar = bytes_to_scalar(i, &A[i]);
      if A_scalar.is_err() {
        return Err(A_scalar.err().unwrap());
      }
      A_scalar_list.push(A_scalar.unwrap());

      let B_scalar = bytes_to_scalar(i, &B[i]);
      if B_scalar.is_err() {
        return Err(B_scalar.err().unwrap());
      }
      B_scalar_list.push(B_scalar.unwrap());

      let C_scalar = bytes_to_scalar(i, &C[i]);
      if C_scalar.is_err() {
        return Err(C_scalar.err().unwrap());
      }
      C_scalar_list.push(C_scalar.unwrap());
    }

    let inst = R1CSInstance::new(
      num_instances,
      max_num_cons_padded,
      num_cons_padded,
      max_num_vars_padded,
      num_vars_padded,
      &A_scalar_list,
      &B_scalar_list,
      &C_scalar_list,
    );

    let digest = inst.get_digest();

    Ok(Instance { inst, digest })
  }

  /// Sort the instances based on index
  // index[i] = j => the original jth entry should now be at the ith position
  pub fn sort(&mut self, num_instances: usize, index: &Vec<usize>) {
    self.inst.sort(num_instances, index);
    self.digest = self.inst.get_digest();
  }

  // Generates a constraints based on supplied (variable, constant) pairs
  fn gen_constr(
    mut A: Vec<(usize, usize, [u8; 32])>,
    mut B: Vec<(usize, usize, [u8; 32])>,
    mut C: Vec<(usize, usize, [u8; 32])>,
    i: usize,
    args_A: Vec<(usize, isize)>,
    args_B: Vec<(usize, isize)>,
    args_C: Vec<(usize, isize)>,
  ) -> (
    Vec<(usize, usize, [u8; 32])>,
    Vec<(usize, usize, [u8; 32])>,
    Vec<(usize, usize, [u8; 32])>,
  ) {
    let int_to_scalar = |i: isize| {
      let abs_scalar = S::from(i.abs() as u64);
      if i < 0 {
        abs_scalar.negate().to_bytes()
      } else {
        abs_scalar.to_bytes()
      }
    };
    for vars in &args_A {
      let sc = int_to_scalar(vars.1);
      A.push((i, vars.0, sc));
    }
    for vars in &args_B {
      let sc = int_to_scalar(vars.1);
      B.push((i, vars.0, sc));
    }
    for vars in &args_C {
      let sc = int_to_scalar(vars.1);
      C.push((i, vars.0, sc));
    }
    (A, B, C)
  }

  // gen_constr from byte lists
  fn gen_constr_bytes(
    mut A: Vec<(usize, usize, [u8; 32])>,
    mut B: Vec<(usize, usize, [u8; 32])>,
    mut C: Vec<(usize, usize, [u8; 32])>,
    i: usize,
    args_A: Vec<(usize, [u8; 32])>,
    args_B: Vec<(usize, [u8; 32])>,
    args_C: Vec<(usize, [u8; 32])>,
  ) -> (
    Vec<(usize, usize, [u8; 32])>,
    Vec<(usize, usize, [u8; 32])>,
    Vec<(usize, usize, [u8; 32])>,
  ) {
    for vars in &args_A {
      A.push((i, vars.0, vars.1));
    }
    for vars in &args_B {
      B.push((i, vars.0, vars.1));
    }
    for vars in &args_C {
      C.push((i, vars.0, vars.1));
    }
    (A, B, C)
  }

  /// Generates BLOCK_CORRECTNESS and MEM_EXTRACT
  /// Verify the correctness of each block execution, as well as extracting all memory operations
  ///
  /// Input composition: (if every segment exists)
  ///             INPUT + VAR                   Challenges                           BLOCK_W2                                              BLOCK_W3                      BLOCK_W3_SHIFTED
  ///  0   1   2  IOW  +1  +2  +3  +4  +5  |  0   1   2   3   |  0   1   2   3   4  NIU  1   2   3  2NP  +1  +2  +3  +4      |  0   1   2   3   4   5   6   7   |  0   1   2   3   4   5   6   7
  ///  v  i0  ... PA0 PD0 ... VA0 VD0 ...  |  tau r  r^2 ...  |  _   _  ZO r*i1 ...  MR  MC  MR ... MR1 MR2 MR3  MC MR1 ...  |  v   x  pi   D  pi   D  pi   D   |  v   x  pi   D  pi   D  pi   D
  ///                                                                INPUT                PHY                VIR                    INPUT        PHY     VIR           INPUT        PHY     VIR
  ///
  /// VAR:
  /// We assume that the witnesses are of the following format:
  ///         0: W, valid bit
  /// next 2*NP: (PA, PD) pair for all physical memory ops
  /// next 4*NV: (VA, VD, VL, VT) 4-tuples for all virtual memory ops
  ///
  /// BLOCK_W2: INPUT_W2 | PHY_W2 | VIR_W2
  /// PHY_W2 processes all physical memory accesses in the witness list to a single polynomial root, given by the formula
  ///                           PI(tau - PA - r * PD)
  /// Which is then divided into 2 witnesses for each (PA, PD)
  /// - PMR = r * PD
  /// - PMC = (1 or PMC[i-1]) * (tau - PA - PMR)
  /// The final product is stored in X = MC[NP - 1]
  /// VIR_W2 is similar to PHY_W2, except now with 4-tuples
  ///                           PI(tau - VA - r * VD - r^2 * VL - r^3 * VT)
  /// Which is then divided into 4 witnesses for each (VA, VD, VL, VT), starting at entry 2 * num_phy_ops
  /// - VMR1 = r * VD
  /// - VMR2 = r^2 * VL
  /// - VMR3 = r^3 * VT
  /// - VMC = (1 or VMC[i-1]) * (tau - VA - VMR1 - VMR2 - VMR3)
  /// The final product is stored in X = MC[NV - 1]
  pub fn gen_block_inst<const PRINT_SIZE: bool>(
    num_instances: usize,
    num_vars: usize,
    args: &Vec<
      Vec<(
        Vec<(usize, [u8; 32])>,
        Vec<(usize, [u8; 32])>,
        Vec<(usize, [u8; 32])>,
      )>,
    >,
    num_inputs_unpadded: usize,
    // Number of physical & memory accesses per block
    num_phy_ops: &Vec<usize>,
    num_vir_ops: &Vec<usize>,
    // Information used only by printing
    num_vars_per_block: &Vec<usize>,
    block_num_proofs: &Vec<usize>,
  ) -> (usize, usize, usize, Instance<S>) {
    assert_eq!(num_instances, args.len());

    if PRINT_SIZE {
      println!("\n\n--\nBLOCK INSTS");
      println!(
        "{:10} {:>4}   {:>4} {:>4} {:>4}",
        "", "con", "var", "nnz", "exec"
      );
    }

    let mut block_max_num_cons = 0;
    let mut block_num_cons = Vec::new();
    let mut block_num_non_zero_entries = 0;

    let mut A_list = Vec::new();
    let mut B_list = Vec::new();
    let mut C_list = Vec::new();

    // in INPUT
    let io_width = 2 * num_inputs_unpadded;
    let V_valid = 0;
    let V_cnst = 0;
    let V_input = |i: usize| 2 + i;
    let V_output = |i: usize| 2 + (num_inputs_unpadded - 1) + i;
    // in VAR
    let V_PA = |i: usize| io_width + 2 * i;
    let V_PD = |i: usize| io_width + 2 * i + 1;
    let V_VA = |b: usize, i: usize| io_width + 2 * num_phy_ops[b] + 4 * i;
    let V_VD = |b: usize, i: usize| io_width + 2 * num_phy_ops[b] + 4 * i + 1;
    let V_VL = |b: usize, i: usize| io_width + 2 * num_phy_ops[b] + 4 * i + 2;
    let V_VT = |b: usize, i: usize| io_width + 2 * num_phy_ops[b] + 4 * i + 3;
    // in CHALLENGES, not used if !has_mem_op
    let V_tau = num_vars;
    let V_r = |i: usize| num_vars + i;
    // in BLOCK_W2 / INPUT_W2
    let V_input_dot_prod = |i: usize| {
      if i == 0 {
        V_input(0)
      } else {
        2 * num_vars + 2 + i
      }
    };
    let V_output_dot_prod = |i: usize| 2 * num_vars + 2 + (num_inputs_unpadded - 1) + i;
    // in BLOCK_W2 / PHY_W2
    let V_PMR = |i: usize| 2 * num_vars + 2 * num_inputs_unpadded + 2 * i;
    let V_PMC = |i: usize| 2 * num_vars + 2 * num_inputs_unpadded + 2 * i + 1;
    // in BLOCK_W2 / VIR_W2
    let V_VMR1 =
      |b: usize, i: usize| 2 * num_vars + 2 * num_inputs_unpadded + 2 * num_phy_ops[b] + 4 * i;
    let V_VMR2 =
      |b: usize, i: usize| 2 * num_vars + 2 * num_inputs_unpadded + 2 * num_phy_ops[b] + 4 * i + 1;
    let V_VMR3 =
      |b: usize, i: usize| 2 * num_vars + 2 * num_inputs_unpadded + 2 * num_phy_ops[b] + 4 * i + 2;
    let V_VMC =
      |b: usize, i: usize| 2 * num_vars + 2 * num_inputs_unpadded + 2 * num_phy_ops[b] + 4 * i + 3;
    // in BLOCK_W3
    let V_v = 3 * num_vars;
    let V_x = 3 * num_vars + 1;
    let V_pi = 3 * num_vars + 2;
    let V_d = 3 * num_vars + 3;
    let V_Pp = 3 * num_vars + 4;
    let V_Pd = 3 * num_vars + 5;
    let V_Vp = 3 * num_vars + 6;
    let V_Vd = 3 * num_vars + 7;
    // in BLOCK_W3_SHIFTED
    let V_sv = 4 * num_vars;
    let V_spi = 4 * num_vars + 2;
    let V_Psp = 4 * num_vars + 4;
    let V_Vsp = 4 * num_vars + 6;

    // Variable used by printing
    let mut total_inst_commit_size = 0;
    let mut total_var_commit_size = 0;
    let mut total_cons_exec_size = 0;

    for b in 0..num_instances {
      let arg = &args[b];
      let mut counter = arg.len();
      let mut tmp_nnz_A = 0;
      let mut tmp_nnz_B = 0;
      let mut tmp_nnz_C = 0;
      let (A, B, C) = {
        let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

        // constraints for correctness
        for i in 0..arg.len() {
          tmp_nnz_A += arg[i].0.len();
          tmp_nnz_B += arg[i].1.len();
          tmp_nnz_C += arg[i].2.len();
          (A, B, C) = Instance::<S>::gen_constr_bytes(
            A,
            B,
            C,
            i,
            arg[i].0.clone(),
            arg[i].1.clone(),
            arg[i].2.clone(),
          );
        }

        // constraints for input permutation
        {
          // correctness of w2
          // for i1..
          for i in 1..num_inputs_unpadded - 1 {
            (A, B, C) = Instance::<S>::gen_constr(
              A,
              B,
              C,
              counter,
              vec![(V_input(i), 1)],
              vec![(V_r(i), 1)],
              vec![(V_input_dot_prod(i), 1)],
            );
            counter += 1;
          }
          // for o0, o1..
          for i in 0..num_inputs_unpadded - 1 {
            (A, B, C) = Instance::<S>::gen_constr(
              A,
              B,
              C,
              counter,
              vec![(V_output(i), 1)],
              vec![(V_r(i + num_inputs_unpadded - 1), 1)],
              vec![(V_output_dot_prod(i), 1)],
            );
            counter += 1;
          }
          // v[k]
          (A, B, C) = Instance::<S>::gen_constr(
            A,
            B,
            C,
            counter,
            vec![],
            vec![],
            vec![(V_valid, 1), (V_v, -1)],
          );
          counter += 1;
          // x[k]
          (A, B, C) = Instance::<S>::gen_constr(
            A,
            B,
            C,
            counter,
            [
              vec![(V_tau, 1)],
              (0..2 * num_inputs_unpadded - 2)
                .map(|i| (V_input_dot_prod(i), -1))
                .collect(),
            ]
            .concat(),
            vec![(V_cnst, 1)],
            vec![(V_x, 1)],
          );
          counter += 1;
          // D[k] = x[k] * (pi[k + 1] + (1 - v[k + 1]))
          (A, B, C) = Instance::<S>::gen_constr(
            A,
            B,
            C,
            counter,
            vec![(V_x, 1)],
            vec![(V_spi, 1), (V_cnst, 1), (V_sv, -1)],
            vec![(V_d, 1)],
          );
          counter += 1;
          // pi[k] = v[k] * D[k]
          (A, B, C) = Instance::<S>::gen_constr(
            A,
            B,
            C,
            counter,
            vec![(V_v, 1)],
            vec![(V_d, 1)],
            vec![(V_pi, 1)],
          );
          counter += 1;

          tmp_nnz_A += 4 * num_inputs_unpadded - 2;
          tmp_nnz_B += 2 * num_inputs_unpadded + 2;
          tmp_nnz_C += 2 * num_inputs_unpadded + 2;
        }

        // constraints for memory extraction
        // Note that we do not need v nor x
        // Physical Memory
        for i in 0..num_phy_ops[b] {
          // PMR = r * PD
          (A, B, C) = Instance::<S>::gen_constr(
            A,
            B,
            C,
            counter,
            vec![(V_r(1), 1)],
            vec![(V_PD(i), 1)],
            vec![(V_PMR(i), 1)],
          );
          counter += 1;
          // PMC = (1 or PMC[i-1]) * (tau - PA - PMR)
          if i == 0 {
            (A, B, C) = Instance::<S>::gen_constr(
              A,
              B,
              C,
              counter,
              vec![(V_cnst, 1)],
              vec![(V_tau, 1), (V_PA(i), -1), (V_PMR(i), -1)],
              vec![(V_PMC(i), 1)],
            );
          } else {
            (A, B, C) = Instance::<S>::gen_constr(
              A,
              B,
              C,
              counter,
              vec![(V_PMC(i - 1), 1)],
              vec![(V_tau, 1), (V_PA(i), -1), (V_PMR(i), -1)],
              vec![(V_PMC(i), 1)],
            );
          }
          counter += 1;
        }
        counter += 1;
        // Pd
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          counter,
          // Incorporate Px directly into Pd
          vec![if num_phy_ops[b] == 0 {
            (V_cnst, 1)
          } else {
            (V_PMC(num_phy_ops[b] - 1), 1)
          }],
          vec![(V_Psp, 1), (V_cnst, 1), (V_sv, -1)],
          vec![(V_Pd, 1)],
        );
        counter += 1;
        // Pp
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          counter,
          vec![(V_v, 1)],
          vec![(V_Pd, 1)],
          vec![(V_Pp, 1)],
        );
        counter += 1;

        tmp_nnz_A += 3 * num_phy_ops[b] + 2;
        tmp_nnz_B += 7 * num_phy_ops[b] + 4;
        tmp_nnz_C += 3 * num_phy_ops[b] + 2;

        // Virtual Memory
        for i in 0..num_vir_ops[b] {
          // VMR1 = r * VD
          (A, B, C) = Instance::<S>::gen_constr(
            A,
            B,
            C,
            counter,
            vec![(V_r(1), 1)],
            vec![(V_VD(b, i), 1)],
            vec![(V_VMR1(b, i), 1)],
          );
          counter += 1;
          // VMR2 = r^2 * VL
          (A, B, C) = Instance::<S>::gen_constr(
            A,
            B,
            C,
            counter,
            vec![(V_r(2), 1)],
            vec![(V_VL(b, i), 1)],
            vec![(V_VMR2(b, i), 1)],
          );
          counter += 1;
          // VMR3 = r^3 * VT
          (A, B, C) = Instance::<S>::gen_constr(
            A,
            B,
            C,
            counter,
            vec![(V_r(3), 1)],
            vec![(V_VT(b, i), 1)],
            vec![(V_VMR3(b, i), 1)],
          );
          counter += 1;
          // VMC = (1 or VMC[i-1]) * (tau - VA - VMR1 - VMR2 - VMR3)
          if i == 0 {
            (A, B, C) = Instance::<S>::gen_constr(
              A,
              B,
              C,
              counter,
              vec![(V_cnst, 1)],
              vec![
                (V_tau, 1),
                (V_VA(b, i), -1),
                (V_VMR1(b, i), -1),
                (V_VMR2(b, i), -1),
                (V_VMR3(b, i), -1),
              ],
              vec![(V_VMC(b, i), 1)],
            );
          } else {
            (A, B, C) = Instance::<S>::gen_constr(
              A,
              B,
              C,
              counter,
              vec![(V_VMC(b, i - 1), 1)],
              vec![
                (V_tau, 1),
                (V_VA(b, i), -1),
                (V_VMR1(b, i), -1),
                (V_VMR2(b, i), -1),
                (V_VMR3(b, i), -1),
              ],
              vec![(V_VMC(b, i), 1)],
            );
          }
          counter += 1;
        }
        counter += 1;
        // Vd
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          counter,
          // Incorporate Vx directly into Vd
          vec![if num_vir_ops[b] == 0 {
            (V_cnst, 1)
          } else {
            (V_VMC(b, num_vir_ops[b] - 1), 1)
          }],
          vec![(V_Vsp, 1), (V_cnst, 1), (V_sv, -1)],
          vec![(V_Vd, 1)],
        );
        counter += 1;
        // Vp
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          counter,
          vec![(V_v, 1)],
          vec![(V_Vd, 1)],
          vec![(V_Vp, 1)],
        );
        counter += 1;

        tmp_nnz_A += 5 * num_vir_ops[b] + 2;
        tmp_nnz_B += 13 * num_vir_ops[b] + 4;
        tmp_nnz_C += 5 * num_vir_ops[b] + 2;

        (A, B, C)
      };

      // Check if num_cons > block_num_cons
      block_max_num_cons = max(block_max_num_cons, counter);
      block_num_cons.push(counter);

      // Recalculate num_non_zero_entries
      block_num_non_zero_entries = max(
        max(max(block_num_non_zero_entries, tmp_nnz_A), tmp_nnz_B),
        tmp_nnz_C,
      );
      A_list.push(A);
      B_list.push(B);
      C_list.push(C);

      if PRINT_SIZE {
        let max_nnz = max(tmp_nnz_A, max(tmp_nnz_B, tmp_nnz_C));
        let total_var = num_vars_per_block[b]
          + 2 * num_inputs_unpadded.next_power_of_two()
          + (2 * num_phy_ops[b] + 4 * num_vir_ops[b]).next_power_of_two()
          + 2 * 8;
        let num_exec = block_num_proofs[b];
        println!(
          "{:10} {:4} x {:4} {:4} {:4}",
          format!("Block {}", b),
          counter,
          total_var,
          max_nnz,
          num_exec
        );
        total_inst_commit_size += max_nnz;
        total_var_commit_size += total_var * num_exec;
        total_cons_exec_size += counter * num_exec;
      }
    }

    if PRINT_SIZE {
      println!("Total Num of Blocks: {}", num_instances);
      println!("Total Inst Commit Size: {}", total_inst_commit_size);
      println!("Total Var Commit Size: {}", total_var_commit_size);
      println!("Total Cons Exec Size: {}", total_cons_exec_size);
    }

    let block_num_vars = 8 * num_vars;
    let block_inst = Instance::new(
      num_instances,
      block_max_num_cons,
      block_num_cons,
      block_num_vars,
      vec![block_num_vars; num_instances],
      &A_list,
      &B_list,
      &C_list,
    )
    .unwrap();
    (
      block_num_vars,
      block_max_num_cons,
      block_num_non_zero_entries,
      block_inst,
    )
  }

  /// PAIRWISE_CHECK is consisted of two parts:
  ///
  /// CONSIS_CHECK
  /// takes in consis_w3 = <_, _, _, _, i, o, _, _>
  /// and verifies (o[k] - i[k + 1]) * i[k + 1] = 0 for all k
  ///
  /// Input composition:
  ///           Op[k]                        Op[k + 1]
  ///   0   1   2   3   4   5 ...  |   0   1   2   3   4   5
  ///   _   _   _   _   i   o      |   _   _   _   _   i   o
  ///
  /// --
  ///
  /// PHY_MEM_COHERE
  /// takes in addr_mem = <v, D, addr, val>
  /// and verifies that
  /// 1. (v[k] - 1) * v[k + 1] = 0: if the current entry is invalid, the next entry is also invalid
  /// 2. v[k + 1] * (1 - (addr[k + 1] - addr[k])) * (addr[k + 1] - addr[k]) = 0: address difference is 0 or 1, unless the next entry is invalid
  /// 3. v[k + 1] * (1 - (addr[k + 1] - addr[k])) * (val[k + 1] - val[k]) = 0: either address difference is 1, or value are the same, unless the next entry is invalid
  /// So we set D = v[k + 1] * (1 - addr[k + 1] + addr[k])
  ///
  /// Input composition:
  ///     Op[k]           Op[k + 1]
  /// 0   1   2   3  |  4   5   6   7
  /// v   D addr val |  v   D addr val
  ///
  /// --
  ///
  /// VIR_MEM_COHERE
  /// takes in addr_mem = <v, D1, addr, data, ls, ts, _, _> (need to keep the last entry 0 for permutation)
  /// and verifies that
  /// 1. (v[k] - 1) * v[k + 1] = 0: if the current entry is invalid, the next entry is also invalid
  /// 2. v[k + 1] * (1 - (addr[k + 1] - addr[k])) * (addr[k + 1] - addr[k]) = 0: addr difference is 0 or 1, unless the next entry is invalid
  /// 3. v[k + 1] * (1 - (addr[k + 1] - addr[k])) * C_>=(ts[k + 1], ts[k]) = 0: either addr difference is 1, or ts is increasing
  /// 4. v[k + 1] * (1 - (addr[k + 1] - addr[k])) * (ls[k + 1] - STORE) * (data[k + 1] - data[k]) = 0: either addr difference is 1, or next op is STORE, or data are the same
  /// 5. v[k + 1] * (addr[k + 1] - addr[k]) * (ls[k + 1] - STORE) = 0: either phy addr are the same, or next op is STORE
  /// So we set D1 = v[k + 1] * (1 - phy_addr[k + 1] + phy_addr[k])
  ///           D2 = D1 * (ls[i+1] - STORE)
  /// Where STORE = 0
  /// Input composition:
  ///             Op[k]                           Op[k + 1]              D2 & bits of ts[k + 1] - ts[k]
  /// 0   1   2   3   4   5   6   7  |  0   1   2   3   4   5   6   7  |  0   1   2   3   4
  /// v  D1   a   d  ls  ts   _   _  |  v  D1   a   d  ls  ts   _   _  | D2  EQ  B0  B1  ...
  pub fn gen_pairwise_check_inst<const PRINT_SIZE: bool>(
    max_ts_width: usize,
    mem_addr_ts_bits_size: usize,
    // Remaining parameters used only by printing
    consis_num_proofs: usize,
    total_num_phy_mem_accesses: usize,
    total_num_vir_mem_accesses: usize,
  ) -> (usize, usize, usize, Instance<S>) {
    if PRINT_SIZE {
      println!("\n\n--\nPAIRWISE INSTS");
      println!(
        "{:10} {:>4}   {:>4} {:>4} {:>4}",
        "", "con", "var", "nnz", "exec"
      );
    }
    // Variable used by printing
    let mut total_inst_commit_size = 0;
    let mut total_var_commit_size = 0;
    let mut total_cons_exec_size = 0;

    let pairwise_check_num_vars = max(8, mem_addr_ts_bits_size);
    let pairwise_check_max_num_cons = 8 + max_ts_width;
    let pairwise_check_num_cons = vec![2, 4, 8 + max_ts_width];
    let pairwise_check_num_non_zero_entries: usize = max(13 + max_ts_width, 5 + 2 * max_ts_width);

    let pairwise_check_inst = {
      let mut A_list = Vec::new();
      let mut B_list = Vec::new();
      let mut C_list = Vec::new();

      // CONSIS_CHECK
      let (A, B, C) = {
        let width = pairwise_check_num_vars;

        let V_i = 4;
        let V_o = 5;

        let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

        // R1CS:
        // Output matches input
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          0,
          vec![(V_o, 1), (width + V_i, -1)],
          vec![(width + V_i, 1)],
          vec![],
        );

        if PRINT_SIZE {
          let max_nnz = 2;
          let total_var = 16;
          let num_exec = consis_num_proofs;
          println!(
            "{:10} {:4} x {:4} {:4} {:4}",
            "Cohere", 1, total_var, max_nnz, consis_num_proofs
          );
          total_inst_commit_size += max_nnz;
          total_var_commit_size += total_var * num_exec;
          total_cons_exec_size += num_exec;
        }
        (A, B, C)
      };
      A_list.push(A);
      B_list.push(B);
      C_list.push(C);

      // PHY_MEM_COHERE
      let (A, B, C) = {
        let width = pairwise_check_num_vars;

        let V_valid = 0;
        let V_cnst = V_valid;
        let V_D = 1;
        let V_addr = 2;
        let V_val = 3;

        let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

        let mut num_cons = 0;
        // (v[k] - 1) * v[k + 1] = 0
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          num_cons,
          vec![(V_valid, 1), (V_cnst, -1)],
          vec![(width + V_valid, 1)],
          vec![],
        );
        num_cons += 1;
        // v[k + 1] * (1 - addr[k + 1] + addr[k]) = D[k]
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          num_cons,
          vec![(width + V_valid, 1)],
          vec![(V_cnst, 1), (width + V_addr, -1), (V_addr, 1)],
          vec![(V_D, 1)],
        );
        num_cons += 1;
        // D[k] * (addr[k + 1] - addr[k]) = 0
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          num_cons,
          vec![(V_D, 1)],
          vec![(width + V_addr, 1), (V_addr, -1)],
          vec![],
        );
        num_cons += 1;
        // D[k] * (val[k + 1] - val[k]) = 0
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          num_cons,
          vec![(V_D, 1)],
          vec![(width + V_val, 1), (V_val, -1)],
          vec![],
        );
        num_cons += 1;

        if PRINT_SIZE {
          let max_nnz = 8;
          let total_var = 16;
          let num_exec = total_num_phy_mem_accesses;
          println!(
            "{:10} {:4} x {:4} {:4} {:4}",
            "Phy Mem", num_cons, total_var, max_nnz, total_num_phy_mem_accesses
          );
          total_inst_commit_size += max_nnz;
          total_var_commit_size += total_var * num_exec;
          total_cons_exec_size += num_cons * num_exec;
        }
        (A, B, C)
      };
      A_list.push(A);
      B_list.push(B);
      C_list.push(C);

      // VIR_MEM_COHERE
      let (A, B, C) = {
        let width = pairwise_check_num_vars;

        let V_valid = 0;
        let V_cnst = V_valid;
        let V_D1 = 1;
        let V_addr = 2;
        let V_data = 3;
        let V_ls = 4;
        let V_ts = 5;
        let V_D2 = 2 * width;
        let V_EQ = 2 * width + 1;
        let V_B = |i| 2 * width + 2 + i;

        let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

        let mut num_cons = 0;
        // Sortedness
        // (v[k] - 1) * v[k + 1] = 0
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          num_cons,
          vec![(V_valid, 1), (V_cnst, -1)],
          vec![(width + V_valid, 1)],
          vec![],
        );
        num_cons += 1;
        // D1[k] = v[k + 1] * (1 - addr[k + 1] + addr[k])
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          num_cons,
          vec![(width + V_valid, 1)],
          vec![(V_cnst, 1), (width + V_addr, -1), (V_addr, 1)],
          vec![(V_D1, 1)],
        );
        num_cons += 1;
        // D1[k] * (addr[k + 1] - addr[k]) = 0
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          num_cons,
          vec![(V_D1, 1)],
          vec![(width + V_addr, 1), (V_addr, -1)],
          vec![],
        );
        num_cons += 1;
        // EQ
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          num_cons,
          vec![(V_EQ, 1)],
          vec![(V_EQ, 1)],
          vec![(V_EQ, 1)],
        );
        num_cons += 1;
        // C>=
        for i in 0..max_ts_width {
          // Bi * Bi = Bi
          (A, B, C) = Instance::<S>::gen_constr(
            A,
            B,
            C,
            num_cons,
            vec![(V_B(i), 1)],
            vec![(V_B(i), 1)],
            vec![(V_B(i), 1)],
          );
          num_cons += 1;
        }
        // D1[k] * (ts[k + 1] - ts[k]) = EQ + \Sum_i B_i
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          num_cons,
          vec![(V_D1, 1)],
          vec![(width + V_ts, 1), (V_ts, -1)],
          [
            vec![(V_EQ, 1)],
            (0..max_ts_width)
              .map(|i| (V_B(i), i.pow2() as isize))
              .collect(),
          ]
          .concat(),
        );
        num_cons += 1;

        // Consistency
        // D1[k] * (ls[k + 1] - STORE) = D2[k], where STORE = 0
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          num_cons,
          vec![(V_D1, 1)],
          vec![(width + V_ls, 1)],
          vec![(V_D2, 1)],
        );
        num_cons += 1;
        // D2[k] * (data[k + 1] - data[k]) = 0
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          num_cons,
          vec![(V_D2, 1)],
          vec![(width + V_data, 1), (V_data, -1)],
          vec![],
        );
        num_cons += 1;
        // (1 - D1[k]) * (ls[k + 1] - STORE) = 0, where STORE = 0
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          num_cons,
          vec![(V_cnst, 1), (V_D1, -1)],
          vec![(width + V_ls, 1)],
          vec![],
        );
        num_cons += 1;

        if PRINT_SIZE {
          let max_nnz = pairwise_check_num_non_zero_entries;
          let total_var = 2 * pairwise_check_num_vars;
          let num_exec = total_num_phy_mem_accesses;
          println!(
            "{:10} {:4} x {:4} {:4} {:4}",
            "Vir Mem", num_cons, total_var, max_nnz, total_num_vir_mem_accesses
          );
          total_inst_commit_size += max_nnz;
          total_var_commit_size += total_var * num_exec;
          total_cons_exec_size += num_cons * num_exec;
        }
        (A, B, C)
      };
      A_list.push(A);
      B_list.push(B);
      C_list.push(C);

      if PRINT_SIZE {
        let mut num_instances = 1;
        if total_num_phy_mem_accesses > 0 {
          num_instances += 1;
        }
        if total_num_vir_mem_accesses > 0 {
          num_instances += 1;
        }
        println!("Total Num of Blocks: {}", num_instances);
        println!("Total Inst Commit Size: {}", total_inst_commit_size);
        println!("Total Var Commit Size: {}", total_var_commit_size);
        println!("Total Cons Exec Size: {}", total_cons_exec_size);
      }

      let pairwise_check_inst = Instance::new(
        3,
        pairwise_check_max_num_cons,
        pairwise_check_num_cons,
        4 * pairwise_check_num_vars,
        vec![4 * pairwise_check_num_vars; 3],
        &A_list,
        &B_list,
        &C_list,
      )
      .unwrap();
      pairwise_check_inst
    };
    (
      pairwise_check_num_vars,
      pairwise_check_max_num_cons,
      pairwise_check_num_non_zero_entries,
      pairwise_check_inst,
    )
  }

  /// Generates PERM_ROOT instance based on parameters
  /// Witnesses of PERM_ROOT is consisted of [w0, w1, w2, w3], each of size num_vars
  /// w0: tau, r, r^2, ...
  /// w1: one block_inputs entry: v, _, i0, i1, ..., o0, o1, ...
  /// w2: one block_inputs entry dot product <r>: _, _, ZO, r * i1, r^2 * i2, r^3 * i3, ...
  /// w3: one root of the polynomial: v, x, pi, D, I, O, _, _
  /// w4: shifted w3: v[k+1], x[k+1], pi[k+1], D[k+1], ...
  /// where I = v * (v + i0 + r * i1 + r^2 * i2 + ...),
  ///       O = v * (v + ZO)
  ///       ZO * r^n = r^n * o0 + r^(n + 1) * o1, ...,
  /// are used by the consistency check, AND
  /// v[k]  <- whether the entry is valid
  /// x[k]  <- one root of the polynomial: v * (tau - i0 - r * i1 - r^2 * i2 - ...)
  /// pi[k] <- v[k] * D[k]
  /// D[k] <- x[k] * (pi[k + 1] + (1 - v[k + 1]))
  /// Note: Only process the first num_inputs_unpadded inputs since the rest are unused
  pub fn gen_perm_root_inst<const PRINT_SIZE: bool>(
    num_inputs_unpadded: usize,
    num_vars: usize,
    // Remaining parameters used only by printing
    consis_num_proofs: usize,
    total_num_phy_mem_accesses: usize,
    total_num_vir_mem_accesses: usize,
  ) -> (usize, usize, Instance<S>) {
    if PRINT_SIZE {
      println!("\n\n--\nPERM INSTS");
      println!(
        "{:10} {:>4}   {:>4} {:>4} {:>4}",
        "", "con", "var", "nnz", "exec"
      );
    }
    // Variable used by printing
    let mut total_inst_commit_size = 0;
    let mut total_var_commit_size = 0;
    let mut total_cons_exec_size = 0;

    let perm_root_num_cons = 2 * num_inputs_unpadded + 4;
    let perm_root_num_non_zero_entries = 4 * num_inputs_unpadded + 5;
    let perm_root_inst = {
      let (A, B, C) = {
        let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

        let V_tau = 0;
        // V_r(0) == tau and should be skipped!
        let V_r = |i: usize| i;

        let V_valid = num_vars;
        let V_cnst = V_valid;
        let V_input = |i: usize| num_vars + 2 + i;
        let V_output = |i: usize| num_vars + 2 + (num_inputs_unpadded - 1) + i;

        let V_ZO = 2 * num_vars + 2;
        let V_input_dot_prod = |i: usize| {
          if i == 0 {
            V_input(0)
          } else {
            2 * num_vars + 2 + i
          }
        };
        let V_output_dot_prod = |i: usize| 2 * num_vars + 2 + (num_inputs_unpadded - 1) + i;

        let V_v = 3 * num_vars;
        let V_x = 3 * num_vars + 1;
        let V_pi = 3 * num_vars + 2;
        let V_d = 3 * num_vars + 3;
        let V_I = 3 * num_vars + 4;
        let V_O = 3 * num_vars + 5;

        let V_sv = 4 * num_vars;
        let V_spi = 4 * num_vars + 2;

        let mut constraint_count = 0;

        // correctness of w2
        // for i1..
        for i in 1..num_inputs_unpadded - 1 {
          (A, B, C) = Instance::<S>::gen_constr(
            A,
            B,
            C,
            constraint_count,
            vec![(V_input(i), 1)],
            vec![(V_r(i), 1)],
            vec![(V_input_dot_prod(i), 1)],
          );
          constraint_count += 1;
        }
        // for o0, o1..
        for i in 0..num_inputs_unpadded - 1 {
          (A, B, C) = Instance::<S>::gen_constr(
            A,
            B,
            C,
            constraint_count,
            vec![(V_output(i), 1)],
            vec![(V_r(i + num_inputs_unpadded - 1), 1)],
            vec![(V_output_dot_prod(i), 1)],
          );
          constraint_count += 1;
        }
        // ZO * r^n = r^n * o0 + r^(n + 1) * o1, ...
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          constraint_count,
          vec![(V_ZO, 1)],
          vec![(V_r(num_inputs_unpadded - 1), 1)],
          (0..num_inputs_unpadded - 1)
            .map(|i| (V_output_dot_prod(i), 1))
            .collect(),
        );
        constraint_count += 1;
        // I = v * (v + i0 + r * i1 + r^2 * i2 + ...)
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          constraint_count,
          vec![(V_valid, 1)],
          [
            vec![(V_cnst, 1)],
            (0..num_inputs_unpadded - 1)
              .map(|i| (V_input_dot_prod(i), 1))
              .collect(),
          ]
          .concat(),
          vec![(V_I, 1)],
        );
        constraint_count += 1;
        // O = v * (v + ZO)
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          constraint_count,
          vec![(V_valid, 1)],
          vec![(V_valid, 1), (V_ZO, 1)],
          vec![(V_O, 1)],
        );
        constraint_count += 1;
        // v[k]
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          constraint_count,
          vec![],
          vec![],
          vec![(V_valid, 1), (V_v, -1)],
        );
        constraint_count += 1;
        // x[k]
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          constraint_count,
          [
            vec![(V_tau, 1)],
            (0..2 * num_inputs_unpadded - 2)
              .map(|i| (V_input_dot_prod(i), -1))
              .collect(),
          ]
          .concat(),
          vec![(num_vars, 1)],
          vec![(V_x, 1)],
        );
        constraint_count += 1;
        // D[k] = x[k] * (pi[k + 1] + (1 - v[k + 1]))
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          constraint_count,
          vec![(V_x, 1)],
          vec![(V_spi, 1), (V_cnst, 1), (V_sv, -1)],
          vec![(V_d, 1)],
        );
        constraint_count += 1;
        // pi[k] = v[k] * D[k]
        (A, B, C) = Instance::<S>::gen_constr(
          A,
          B,
          C,
          constraint_count,
          vec![(V_v, 1)],
          vec![(V_d, 1)],
          vec![(V_pi, 1)],
        );
        constraint_count += 1;

        if PRINT_SIZE {
          let max_nnz = perm_root_num_non_zero_entries;
          let total_var = 3 * num_vars + 16;
          let num_exec = total_num_phy_mem_accesses;
          println!(
            "{:10} {:4} x {:4} {:4} {:4}",
            "Perm Root",
            constraint_count,
            total_var,
            max_nnz,
            consis_num_proofs + total_num_phy_mem_accesses + total_num_vir_mem_accesses
          );
          total_inst_commit_size += max_nnz;
          total_var_commit_size += total_var * num_exec;
          total_cons_exec_size += constraint_count * num_exec;
        }
        (A, B, C)
      };

      let A_list = vec![A.clone()];
      let B_list = vec![B.clone()];
      let C_list = vec![C.clone()];

      if PRINT_SIZE {
        let mut num_instances = 1;
        if total_num_phy_mem_accesses > 0 {
          num_instances += 1;
        }
        if total_num_vir_mem_accesses > 0 {
          num_instances += 1;
        }
        println!("Total Num of Blocks: {}", num_instances);
        println!("Total Inst Commit Size: {}", total_inst_commit_size);
        println!("Total Var Commit Size: {}", total_var_commit_size);
        println!("Total Cons Exec Size: {}", total_cons_exec_size);
      }

      let perm_root_inst = Instance::new(
        1,
        perm_root_num_cons,
        vec![perm_root_num_cons],
        8 * num_vars,
        vec![8 * num_vars],
        &A_list,
        &B_list,
        &C_list,
      )
      .unwrap();
      perm_root_inst
    };
    (
      perm_root_num_cons,
      perm_root_num_non_zero_entries,
      perm_root_inst,
    )
  }
}
