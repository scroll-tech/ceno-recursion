/*
use bellman::gadgets::test::TestConstraintSystem;
use bellman::groth16::{
    create_random_proof, generate_parameters, generate_random_parameters, prepare_verifying_key,
    verify_proof, Parameters, Proof, VerifyingKey,
};
use bellman::Circuit;
use bls12_381::{Bls12, Scalar};
*/
use core::cmp::min;
use rug::Integer;
use circ::front::zsharp::{self, ZSharpFE};
use circ::front::{FrontEnd, Mode};
use circ::ir::opt::{opt, Opt};
use circ_fields::FieldV;
/*
use circ::target::r1cs::bellman::parse_instance;
*/
use circ::target::r1cs::{R1cs, VarType, Lc};
use circ::target::r1cs::opt::reduce_linearities;
use circ::target::r1cs::trans::to_r1cs;
/*
use std::fs::File;
use std::io::Read;
use std::io::Write;
*/
use circ::cfg::{
    cfg,
    clap::{self, Parser, ValueEnum},
    CircOpt,
};
use std::path::PathBuf;
use zokrates_pest_ast::*;

#[derive(Debug, Parser)]
#[command(name = "zxc", about = "CirC: the circuit compiler")]
struct Options {
    /// Input file
    #[arg(name = "PATH")]
    path: PathBuf,

    /*
    #[arg(long, default_value = "P", parse(from_os_str))]
    prover_key: PathBuf,

    #[arg(long, default_value = "V", parse(from_os_str))]
    verifier_key: PathBuf,

    #[arg(long, default_value = "pi", parse(from_os_str))]
    proof: PathBuf,

    #[arg(long, default_value = "x", parse(from_os_str))]
    instance: PathBuf,
    */
    #[arg(short = 'L')]
    /// skip linearity reduction entirely
    skip_linred: bool,

    #[command(flatten)]
    /// CirC options
    circ: CircOpt,

    #[arg(long, default_value = "count")]
    action: ProofAction,

    #[arg(short = 'q')]
    /// quiet mode: don't print R1CS at the end
    quiet: bool,
}

#[derive(PartialEq, Eq, Debug, Clone, ValueEnum)]
enum ProofAction {
    Count,
    Setup,
    Prove,
    Verify,
}

#[derive(PartialEq, Debug, Clone, ValueEnum)]
enum ProofOption {
    Count,
    Prove,
}

struct BlockConstraint {
    // Instance entry -> (input?, entry)
    io_map: Vec<(bool, usize)>,
    r1cs: R1cs
}

struct SparseMatEntry {
    row: usize,
    // Which column is the constant (valid) value?
    v_cnst: usize,
    args_a: Vec<(usize, i32)>,
    args_b: Vec<(usize, i32)>,
    args_c: Vec<(usize, i32)>
}

// When adding the validity check, how many constraints will it become?
fn get_num_cons_with_v_check(c: &(Lc, Lc, Lc)) -> usize {
    // Original Constraint: A * B = C
    // If C contains no constant, and A and B do not both contain constants, we don't need V
    if (c.0.constant_is_zero() || c.1.constant_is_zero()) && c.2.constant_is_zero() {
        return 1;
    }
    // If C contains no constant, then we only need two constraints: V * A = Z0; Z0 * B = C
    else if c.2.constant_is_zero() {
        return 2;
    }
    // If C contains constant and either A or B is zero, then we only need to switch around: C = 0 -> V * B = 0, so still one
    else if !c.2.constant_is_zero() && (c.0.is_zero() || c.1.is_zero()) {
        return 1;
    }
    // If C contains constant and neither A nor B contains constant, then we need two: V * C = Z0; A * B = Z0
    else if !c.2.constant_is_zero() && c.0.constant_is_zero() && c.1.constant_is_zero() {
        return 2;
    }
    // Otherwise (C contains zero, at least one of A and B contains constant), need three: V * A = Z0, V * C = Z1, Z0 * B = Z1
    else {
        return 3;
    }
}

// When adding the validity check, what does the sparse format look like?
fn get_sparse_cons_with_v_check(
    c: &(Lc, Lc, Lc), 
    row: usize, 
    v_cnst: usize,
    io_relabel: impl FnOnce(usize) -> usize + std::marker::Copy,
    witness_relabel: impl FnOnce(usize) -> usize + std::marker::Copy,
    next_valid_check_witness: usize,
) -> (Vec<SparseMatEntry>, usize, usize) {
    // Extract all entries from A, B, C
    let (args_a, args_b, args_c) = {
        let mut args_a = Vec::new();
        let mut args_b = Vec::new();
        let mut args_c = Vec::new();
        if !c.0.constant_is_zero() {
            args_a.push((v_cnst, c.0.constant.signed_int().to_i32().unwrap()));
        }
        for (var, coeff) in c.0.monomials.iter() {
            match var.ty() {
                VarType::Inst => args_a.push((io_relabel(var.number()), coeff.signed_int().to_i32().unwrap())),
                VarType::FinalWit => args_a.push((witness_relabel(var.number()), coeff.signed_int().to_i32().unwrap())),
                _ => panic!("Unsupported variable type!")
            }
        }
        if !c.1.constant_is_zero() {
            args_b.push((v_cnst, c.1.constant.signed_int().to_i32().unwrap()));
        }
        for (var, coeff) in c.1.monomials.iter() {
            match var.ty() {
                VarType::Inst => args_b.push((io_relabel(var.number()), coeff.signed_int().to_i32().unwrap())),
                VarType::FinalWit => args_b.push((witness_relabel(var.number()), coeff.signed_int().to_i32().unwrap())),
                _ => panic!("Unsupported variable type!")
            }
        }
        if !c.2.constant_is_zero() {
            args_c.push((v_cnst, c.2.constant.signed_int().to_i32().unwrap()));
        }
        for (var, coeff) in c.2.monomials.iter() {
            match var.ty() {
                VarType::Inst => args_c.push((io_relabel(var.number()), coeff.signed_int().to_i32().unwrap())),
                VarType::FinalWit => args_c.push((witness_relabel(var.number()), coeff.signed_int().to_i32().unwrap())),
                _ => panic!("Unsupported variable type!")
            }
        }
        (args_a, args_b, args_c)
    };

    let args_v = vec![(v_cnst, 1)];
    let args_z0 = vec![(next_valid_check_witness, 1)];
    let args_z1 = vec![(next_valid_check_witness - 1, 1)];
    // Original Constraint: A * B = C
    // If C contains no constant, and A and B do not both contain constants, we don't need V
    if (c.0.constant_is_zero() || c.1.constant_is_zero()) && c.2.constant_is_zero() {
        return (vec![SparseMatEntry { row, v_cnst, args_a, args_b, args_c }], row + 1, next_valid_check_witness);
    }
    // If C contains no constant, then we only need two constraints: V * A = Z0; Z0 * B = C
    else if c.2.constant_is_zero() {
        return (vec![
            SparseMatEntry { row, v_cnst, args_a: args_v, args_b: args_a, args_c: args_z0.clone() },
            SparseMatEntry { row, v_cnst, args_a: args_z0, args_b, args_c }
        ], row + 2, next_valid_check_witness - 1);
    }
    // If C contains constant and either A or B is zero, then we only need to switch around: 0 = C -> V * C = 0, so still one
    else if !c.2.constant_is_zero() && (c.0.is_zero() || c.1.is_zero()) {
        return (vec![
            SparseMatEntry { row, v_cnst, args_a: args_v, args_b: args_c, args_c: Vec::new() }
        ], row + 1, next_valid_check_witness);
    }
    // If C contains constant and neither A nor B contains constant, then we need two: V * C = Z0; A * B = Z0
    else if !c.2.constant_is_zero() && c.0.constant_is_zero() && c.1.constant_is_zero() {
        return (vec![
            SparseMatEntry { row, v_cnst, args_a: args_v, args_b: args_c, args_c: args_z0.clone() },
            SparseMatEntry { row, v_cnst, args_a, args_b, args_c: args_z0 }
        ], row + 2, next_valid_check_witness - 1);
    }
    // Otherwise (C contains zero, at least one of A and B contains constant), need three: V * A = Z0, V * C = Z1, Z0 * B = Z1
    else {
        return (vec![
            SparseMatEntry { row, v_cnst, args_a: args_v.clone(), args_b: args_a, args_c: args_z0.clone() },
            SparseMatEntry { row, v_cnst, args_a: args_v, args_b: args_c, args_c: args_z1.clone() },
            SparseMatEntry { row, v_cnst, args_a: args_z0, args_b, args_c: args_z1 },
        ], row + 3, next_valid_check_witness - 2);
    }
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options::parse();
    circ::cfg::set(&options.circ);
    println!("{options:?}");

    let (cs, io_size, live_io_list) = {
        let inputs = zsharp::Inputs {
            file: options.path,
            mode: Mode::Proof,
            entry_regs: vec![LiteralExpression::DecimalLiteral(
                DecimalLiteralExpression {
                    value: DecimalNumber {
                        value: "5".to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    },
                    suffix: Some(DecimalSuffix::Field(FieldSuffix {
                        span: Span::new("", 0, 0).unwrap()
                    })),
                    span: Span::new("", 0, 0).unwrap()
                }
            )]
        };
        ZSharpFE::gen(inputs)
    };

    /*
    println!("Optimizing IR... ");
    let cs = opt(
        cs,
        vec![
            Opt::ScalarizeVars,
            Opt::Flatten,
            Opt::Sha,
            Opt::ConstantFold(Box::new([])),
            Opt::Flatten,
            Opt::Inline,
            // Tuples must be eliminated before oblivious array elim
            Opt::Tuple,
            Opt::ConstantFold(Box::new([])),
            Opt::Obliv,
            // The obliv elim pass produces more tuples, that must be eliminated
            Opt::Tuple,
            Opt::LinearScan,
            // The linear scan pass produces more tuples, that must be eliminated
            Opt::Tuple,
            Opt::Flatten,
            Opt::ConstantFold(Box::new([])),
            Opt::Inline,
            Opt::SkolemizeChallenges
        ],
    );
    println!("done.");
    */

    for (name, c) in &cs.comps {
        println!("\n--\nName: {}", name);
        println!("VariableMetadata:");
        for v in &c.metadata.ordered_input_names() {
            let m = &c.metadata.lookup(v);
            println!("{}: vis: {}, round: {}, random: {}, committed: {}", 
                v, if m.vis == None {"PUBLIC"} else {if m.vis == Some(0) {"PROVER"} else {"VERIFIER"}}, m.round.to_string(), m.random.to_string(), m.committed.to_string());
        }
        println!("Output:");
        for t in &c.outputs {
            println!("  {}", t);
        }
    }

    println!("Converting to r1cs");
    let mut block_num = 0;
    let mut block_name = format!("Block_{}", block_num);
    // Obtain a list of (r1cs, io_map) for all blocks
    // As we generate R1Cs for each block:
    // 1. Add validity check to every constraint: if a constraint cannot be satisfied by setting all variables to 0, need to multiply by %V
    //    If the constraint is already of form A * B = C, need to divide into Z = V * A, Z * B = c
    // 2. Compute the maximum number of witnesses within any constraint to obtain final io width
    let mut r1cs_list = Vec::new();
    let mut max_num_witnesses = 2 * io_size;
    let mut max_num_cons = 1;
    while let Some(c) = cs.comps.get(&block_name) {
        // println!("{}:", block_name);
        let mut r1cs = to_r1cs(c, cfg());
        // Remove the last constraint because it is about the return value
        r1cs.constraints.pop();

        /*
        let r1cs = if options.skip_linred {
            println!("Skipping linearity reduction, as requested.");
            r1cs
        } else {
            println!(
                "R1cs size before linearity reduction: {}",
                r1cs.constraints().len()
            );
            reduce_linearities(r1cs, cfg())
        };
        */
        let mut num_witnesses = r1cs.num_vars();
        // Include the V * V = V constraint
        let mut num_cons = r1cs.constraints().len() + 1;
        // Add witnesses that will be used by validity check
        // Note: we don't modify the r1cs, only modify the sparse format
        for c in r1cs.constraints() {
            let num_cons_with_v_check = get_num_cons_with_v_check(&c);
            num_cons += num_cons_with_v_check;
            num_witnesses += num_cons_with_v_check - 1;
        }
        // println!("Num wits: {}", num_witnesses);
        // println!("Num cons: {}", num_cons);
        if num_witnesses > max_num_witnesses { max_num_witnesses = num_witnesses };
        if num_cons > max_num_cons { max_num_cons = num_cons };
        r1cs_list.push(r1cs);
        block_num += 1;
        block_name = format!("Block_{}", block_num);
    }
    
    max_num_witnesses = max_num_witnesses.next_power_of_two();
    let max_num_io = max_num_witnesses / 2;
    let max_num_cons = max_num_cons.next_power_of_two();

    // Convert R1CS into Spartan sparse format
    // According to the final io width, re-label all inputs and witnesses to the form (witness, input, output)
    let io_relabel = |b: usize, i: usize| -> usize {
        if i < live_io_list[b].0.len() { 
            live_io_list[b].0[i]
        } else {
            live_io_list[b].1[i - live_io_list[b].0.len()] + max_num_io
        }
    };
    let witness_relabel = |i: usize| i + max_num_witnesses;
    // 0th entry is constant
    let v_cnst = 0;
    let mut sparse_mat_entry: Vec<Vec<SparseMatEntry>> = Vec::new();
    for b in 0..r1cs_list.len() {
        let r1cs = &r1cs_list[b];
        sparse_mat_entry.push(Vec::new());
        // Start assigning validity check witnesses from max_num_witnesses - 1 to the front
        let next_valid_check_witness = 2 * max_num_witnesses - 1;
        // First constraint is V * V = V
        let args_a = vec![(v_cnst, 1)];
        let args_b = vec![(v_cnst, 1)];
        let args_c = vec![(v_cnst, 1)];
        sparse_mat_entry[b].push(SparseMatEntry { row: 0, v_cnst, args_a, args_b, args_c });
        let row_count = 1;
        // Iterate
        for c in r1cs.constraints() {
            let (next_sparse_cons, row_count, next_valid_check_witness) = get_sparse_cons_with_v_check(c, row_count, v_cnst, |i| io_relabel(b, i), witness_relabel, next_valid_check_witness);
            for nsc in next_sparse_cons {
                sparse_mat_entry[b].push(nsc);
            }
        }
    }

    // Print out the sparse matrix
    println!("NUM_VARS: {}", max_num_witnesses);
    println!("NUM_CONS: {}", max_num_cons);
    for b in 0..sparse_mat_entry.len() {
        println!("\nBLOCK {}", b);
        for i in 0..min(10, sparse_mat_entry[b].len()) {
            println!("  ROW {}", i);
            let e = &sparse_mat_entry[b][i];
            println!("    A: {:?}\n    B: {:?}\n    C: {:?}", e.args_a, e.args_b, e.args_c);
        }
        if sparse_mat_entry[b].len() > 10 {
            println!("...");
        }
    }
}
