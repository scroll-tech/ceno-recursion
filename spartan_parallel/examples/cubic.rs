//! Demonstrates how to produces a proof for canonical cubic equation: `x^3 + x + 5 = y`.
//! The example is described in detail [here].
//!
//! The R1CS for this problem is:
//! Instance 1:
//! `Z0 * Z0 - Z1 = 0`
//! `Z1 * Z0 - Z2 = 0`
//! `(Z2 + Z0) * 1 - Z3 = 0`
//! `(Z3 + 5) * 1 - Z4 = 0`
//! Instance 2:
//! `Z0 * 2 - Z1 = 0`
//! `Z1 * Z0 - 2 * Z2 = 0`
//! `(Z2 + Z1 + Z0) * 4 - Z3 = 0`
//! `(Z3 + Z1 + 5) * 2 - Z4 = 0`
//!
//! [here]: https://medium.com/@VitalikButerin/quadratic-arithmetic-programs-from-zero-to-hero-f6d558cea649
#![allow(clippy::assertions_on_result_states)]
use curve25519_dalek::scalar::Scalar;
use libspartan::{Instance, SNARKGens, VarsAssignment, SNARK, InputsAssignment};
use merlin::Transcript;
use rand::rngs::OsRng;

#[allow(non_snake_case)]
fn produce_r1cs() -> (
  usize,
  usize,
  usize,
  usize,
  usize,
  Vec<usize>,
  Instance,
  Vec<Vec<VarsAssignment>>,
  Vec<Vec<InputsAssignment>>,
) {
  // bad test cases
  // set them to unreachable values to prevent bad tests
  let bad_instance = 3;
  let bad_proof = 1;
  // parameters of the R1CS instance
  // maximum value among the R1CS instances
  let num_cons = 4;
  // num_vars = num_inputs
  // Divide inputs into (1, input, 1, output)
  let num_vars = 4;
  let num_inputs = num_vars;
  let num_non_zero_entries = 8;
  // Number of R1CS instances
  let num_instances = 2;
  // Number of proofs of each R1CS instance
  let max_num_proofs = 4;
  let num_proofs = vec![4, 2];

  let one = Scalar::one().to_bytes();
  let two = Scalar::from(2u32).to_bytes();
  let mut assignment_vars_matrix = Vec::new();
  let mut assignment_inputs_matrix = Vec::new();

  let mut A_list = Vec::new();
  let mut B_list = Vec::new();
  let mut C_list = Vec::new();

  // --
  // Instance 0
  // --
  let instance = 0;
  // We will encode the above constraints into three matrices, where
  // the coefficients in the matrix are in the little-endian byte order
  let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
  let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
  let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

  // R1CS is a set of three sparse matrices A B C, where is a row for every
  // constraint and a column for every entry in z = (vars, 1, inputs)
  // An R1CS instance is satisfiable iff:
  // Az \circ Bz = Cz, where z = (vars, 1, inputs)

  // constraint 0 entries in (A,B,C)
  // constraint 0 is Z0 * Z0 - Z1 = 0.
  A.push((0, 0, one));
  B.push((0, 0, one));
  C.push((0, 1, one));

  // constraint 1 entries in (A,B,C)
  // constraint 1 is Z1 * Z0 - Z2 = 0.
  A.push((1, 1, one));
  B.push((1, 0, one));
  C.push((1, 2, one));

  // constraint 2 entries in (A,B,C)
  // constraint 2 is (Z2 + Z0) * 1 - Z3 = 0.
  A.push((2, 2, one));
  A.push((2, 0, one));
  B.push((2, num_vars, one));
  C.push((2, 3, one));

  // constraint 3 entries in (A,B,C)
  // constraint 3 is (Z3 + 5) * 1 - I0 = 0.
  A.push((3, 3, one));
  A.push((3, num_vars, Scalar::from(5u32).to_bytes()));
  B.push((3, num_vars, one));
  C.push((3, num_vars + 1, one));

  A_list.push(A);
  B_list.push(B);
  C_list.push(C);

  let mut assignment_vars = Vec::new();
  let mut assignment_inputs = Vec::new();

  for proof in 0..num_proofs[instance] {
    // compute a satisfying assignment
    let mut csprng: OsRng = OsRng;
    let z0 = Scalar::random(&mut csprng);
    let z1 = z0 * z0; // constraint 0
    let z2 = z1 * z0; // constraint 1
    // let z3 = z2 + z0; // constraint 2
    let z3 = if instance == bad_instance && proof == bad_proof {z2 - z0} else {z2 + z0};
    let i0 = z3 + Scalar::from(5u32); // constraint 3

    // create a VarsAssignment
    let mut vars = vec![Scalar::zero().to_bytes(); num_vars];
    vars[0] = z0.to_bytes();
    vars[1] = z1.to_bytes();
    vars[2] = z2.to_bytes();
    vars[3] = z3.to_bytes();
    let next_assignment_vars = VarsAssignment::new(&vars).unwrap();

    // create an InputsAssignment (1, input, 1, output)
    let mut inputs = vec![Scalar::zero().to_bytes(); num_inputs];
    inputs[0] = Scalar::one().to_bytes();
    inputs[1] = i0.to_bytes();
    inputs[num_inputs / 2] = Scalar::one().to_bytes();
    let next_assignment_inputs = InputsAssignment::new(&inputs).unwrap();

    // check if the instance we created is satisfiable
    // let res = inst.is_sat(&next_assignment_vars, &next_assignment_inputs);
    // assert!(res.unwrap(), "should be satisfied");

    assignment_vars.push(next_assignment_vars);
    assignment_inputs.push(next_assignment_inputs);
  }

  assignment_vars_matrix.push(assignment_vars);
  assignment_inputs_matrix.push(assignment_inputs);

  // --
  // Instance 1
  // --
  let instance = 1;
  // We will encode the above constraints into three matrices, where
  // the coefficients in the matrix are in the little-endian byte order
  let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
  let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
  let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

  // R1CS is a set of three sparse matrices A B C, where is a row for every
  // constraint and a column for every entry in z = (vars, 1, inputs)
  // An R1CS instance is satisfiable iff:
  // Az \circ Bz = Cz, where z = (vars, 1, inputs)

  // constraint 0 entries in (A,B,C)
  // constraint 0 is Z0 * 2 - Z1 = 0
  A.push((0, 0, one));
  B.push((0, num_vars, two));
  C.push((0, 1, one));

  // constraint 1 entries in (A,B,C)
  // constraint 1 is Z1 * Z0 - Z2 = 0.
  A.push((1, 1, one));
  B.push((1, 0, one));
  C.push((1, 2, one));

  // constraint 2 entries in (A,B,C)
  // constraint 2 is (Z2 + Z1 + Z0) * 4 - Z3 = 0.
  A.push((2, 2, one));
  A.push((2, 1, one));
  A.push((2, 0, one));
  B.push((2, num_vars, two));
  C.push((2, 3, one));

  // constraint 3 entries in (A,B,C)
  // constraint 3 is (Z3 + Z1 + 5) * 2 - I0 = 0.
  A.push((3, 3, one));
  A.push((3, 1, one));
  A.push((3, num_vars, Scalar::from(5u32).to_bytes()));
  B.push((3, num_vars, two));
  C.push((3, num_vars + 1, one));

  A_list.push(A);
  B_list.push(B);
  C_list.push(C);

  let mut assignment_vars = Vec::new();
  let mut assignment_inputs = Vec::new();

  for proof in 0..num_proofs[instance] {
    // compute a satisfying assignment
    let mut csprng: OsRng = OsRng;
    let z0 = Scalar::random(&mut csprng);
    let z1 = z0 + z0; // constraint 0
    let z2 = z1 * z0; // constraint 1
    // let z3 = z2 + z1 + z0 + z2 + z1 + z0; // constraint 2
    let z3 = if instance == bad_instance && proof == bad_proof {z2} else {z2 + z1 + z0 + z2 + z1 + z0};
    let i0 = z3 + z1 + Scalar::from(5u32) + z3 + z1 + Scalar::from(5u32); // constraint 3

    // create a VarsAssignment
    let mut vars = vec![Scalar::zero().to_bytes(); num_vars];
    vars[0] = z0.to_bytes();
    vars[1] = z1.to_bytes();
    vars[2] = z2.to_bytes();
    vars[3] = z3.to_bytes();
    let next_assignment_vars = VarsAssignment::new(&vars).unwrap();

    // create an InputsAssignment (1, input, 1, output)
    let mut inputs = vec![Scalar::zero().to_bytes(); num_inputs];
    inputs[0] = Scalar::one().to_bytes();
    inputs[1] = i0.to_bytes();
    inputs[num_inputs / 2] = Scalar::one().to_bytes();
    let next_assignment_inputs = InputsAssignment::new(&inputs).unwrap();

    // check if the instance we created is satisfiable
    // let res = inst.is_sat(&next_assignment_vars, &next_assignment_inputs);
    // assert!(res.unwrap(), "should be satisfied");

    assignment_vars.push(next_assignment_vars);
    assignment_inputs.push(next_assignment_inputs);
  }

  assignment_vars_matrix.push(assignment_vars);
  assignment_inputs_matrix.push(assignment_inputs);

  // --
  // End Instances
  // --

  let inst = Instance::new(num_instances, num_cons, 2 * num_vars, &A_list, &B_list, &C_list).unwrap();

  (
    num_cons,
    num_vars,
    num_non_zero_entries,
    num_instances,
    max_num_proofs,
    num_proofs,
    inst,
    assignment_vars_matrix,
    assignment_inputs_matrix,
  )
}

fn main() {
  // produce an R1CS instance
  let (
    num_cons,
    // num_inputs == num_vars
    num_vars,
    num_non_zero_entries,
    num_instances,
    max_num_proofs,
    num_proofs,
    inst,
    assignment_vars_matrix,
    assignment_inputs_matrix
  ) = produce_r1cs();

  assert_eq!(num_instances, assignment_vars_matrix.len());
  assert_eq!(num_instances, assignment_inputs_matrix.len());
  for p in 0..num_instances {
    assert_eq!(assignment_vars_matrix[p].len(), assignment_inputs_matrix[p].len());
  }

  // produce public parameters
  let gens = SNARKGens::new(num_cons, num_vars, num_instances, num_non_zero_entries);

  // create a commitment to the R1CS instance
  // TODO: change to encoding all r1cs instances
  let (comm, decomm) = SNARK::encode(&inst, &gens);

  // produce a proof of satisfiability
  let mut prover_transcript = Transcript::new(b"snark_example");
  let proof = SNARK::prove(
    max_num_proofs,
    &num_proofs,
    &inst,
    &comm,
    &decomm,
    assignment_vars_matrix,
    assignment_inputs_matrix,
    &gens,
    &mut prover_transcript,
  );

  // verify the proof of satisfiability
  let mut verifier_transcript = Transcript::new(b"snark_example");
  assert!(proof
    .verify(num_instances, max_num_proofs, &num_proofs, num_cons, &comm, &mut verifier_transcript, &gens)
    .is_ok());
  println!("proof verification successful!");
}
