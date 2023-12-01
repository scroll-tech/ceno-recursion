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

struct SparseMatEntry {
    args_a: Vec<(usize, i32)>,
    args_b: Vec<(usize, i32)>,
    args_c: Vec<(usize, i32)>
}

// When adding the validity check, what does the sparse format look like?
fn get_sparse_cons_with_v_check(
    c: &(Lc, Lc, Lc), 
    v_cnst: usize,
    io_relabel: impl FnOnce(usize) -> usize + std::marker::Copy,
    witness_relabel: impl FnOnce(usize) -> usize + std::marker::Copy,
) -> SparseMatEntry {
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
    return SparseMatEntry { args_a, args_b, args_c };
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
    // 1. Add checks on validity: V * V = V and 0 = W - V, where W is the validity bit in the witnesses used by the backend
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
        // Add W to witness
        let num_witnesses = r1cs.num_vars() + 1;
        // Include V * V = V and 0 = W - V
        let num_cons = r1cs.constraints().len() + 2;
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
    // The final version will be of form: (v, i, _, o, wv, ma, mv, w), where
    //   v is the valid bit
    //   i are the inputs
    //   _ is a dummy
    //   o are the outputs
    //  wv is the valid bit, but in witnesses
    //  ma are addresses of all memory accesses
    //  mv are values of all memory accesses
    //   w are witnesses
    // According to the final io width, re-label all inputs and witnesses to the form (witness, input, output)
    let io_relabel = |b: usize, i: usize| -> usize {
        if i < live_io_list[b].0.len() { 
            live_io_list[b].0[i]
        } else {
            live_io_list[b].1[i - live_io_list[b].0.len()] + max_num_io
        }
    };
    // Add all IOs and WV in front
    let witness_relabel = |i: usize| max_num_witnesses + 1 + i;
    // 0th entry is constant
    let v_cnst = 0;
    let mut sparse_mat_entry: Vec<Vec<SparseMatEntry>> = Vec::new();
    for b in 0..r1cs_list.len() {
        let r1cs = &r1cs_list[b];
        sparse_mat_entry.push(Vec::new());
        // First constraint is V * V = V
        let (args_a, args_b, args_c) =
            (vec![(v_cnst, 1)], vec![(v_cnst, 1)], vec![(v_cnst, 1)]);
        sparse_mat_entry[b].push(SparseMatEntry { args_a, args_b, args_c });
        // Second constraint is 0 = W - V
        let (args_a, args_b, args_c) =
            (vec![], vec![], vec![(max_num_witnesses, 1), (v_cnst, -1)]);
        sparse_mat_entry[b].push(SparseMatEntry { args_a, args_b, args_c });
        // Iterate
        for c in r1cs.constraints() {
            sparse_mat_entry[b].push(get_sparse_cons_with_v_check(c, v_cnst, |i| io_relabel(b, i), witness_relabel));
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
