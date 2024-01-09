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
use circ::target::r1cs::wit_comp::StagedWitCompEvaluator;
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

impl SparseMatEntry {
    fn verify(&self, vars: &Vec<usize>) {
        let mut a = 0;
        let mut b = 0;
        let mut c = 0;
        for (i, m) in &self.args_a {
            a += vars[*i] as i32 * m;
        }
        for (i, m) in &self.args_b {
            b += vars[*i] as i32 * m;
        }
        for (i, m) in &self.args_c {
            c += vars[*i] as i32 * m;
        }
        assert_eq!(a * b, c);
    }
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

// Convert an integer into a little-endian byte array
fn integer_to_bytes(mut raw: Integer) -> [u8; 32] {
    let mut res = [0; 32];
    let width = Integer::from(256);
    let mut i = 0;
    while raw != 0 {
        if i >= 32 {
            panic!("Failed to convert integer to byte array: integer is too large! Remainder is: {:?}", raw)
        }
        res[i] = (raw.clone() % width.clone()).to_u8().unwrap();
        raw /= width.clone();
        i += 1;
    }
    res
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options::parse();
    circ::cfg::set(&options.circ);
    println!("{options:?}");

    // --
    // Generate Constraints
    // --
    let (cs, io_size, live_io_list) = {
        let inputs = zsharp::Inputs {
            file: options.path.clone(),
            mode: Mode::Proof
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

    let max_num_io: usize;
    println!("Converting to r1cs:");
    let mut block_num = 0;
    let mut block_name = format!("Block_{}", block_num);
    // Obtain a list of (r1cs, io_map) for all blocks
    // As we generate R1Cs for each block:
    // 1. Add checks on validity: V * V = V and 0 = W - V, where W is the validity bit in the witnesses used by the backend
    // 2. Compute the maximum number of witnesses within any constraint to obtain final io width
    let mut r1cs_list = Vec::new();
    let mut max_num_witnesses = 2 * io_size;
    let mut max_num_cons = 1;
    // Obtain a list of prover data by block
    let mut prover_data_list = Vec::new();
    while let Some(c) = cs.comps.get(&block_name) {
        // println!("{}:", block_name);
        let mut r1cs = to_r1cs(c, cfg());

        // Remove the last constraint because it is about the return value
        r1cs.constraints.pop();

        // Add prover data
        let (prover_data, _) = r1cs.clone().finalize(c);
        prover_data_list.push(prover_data);

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
    max_num_io = max_num_witnesses / 2;
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

    // --
    // Generate Witnesses
    // --
    // Start from entry block, compute value of witnesses
    let (_, block_id_list, block_inputs_list) = {
        let inputs = zsharp::Inputs {
            file: options.path,
            mode: Mode::Proof
        };
        let entry_regs = vec![
            LiteralExpression::DecimalLiteral(
                DecimalLiteralExpression {
                    value: DecimalNumber {
                        value: "0".to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    },
                    suffix: Some(DecimalSuffix::Field(FieldSuffix {
                        span: Span::new("", 0, 0).unwrap()
                    })),
                    span: Span::new("", 0, 0).unwrap()
                }
            ), 
            LiteralExpression::DecimalLiteral(
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
            ), 
            LiteralExpression::DecimalLiteral(
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
            )
        ];
        ZSharpFE::interpret(inputs, &entry_regs)
    };

    let mut inputs_list: Vec<Vec<[u8; 32]>> = Vec::new();
    for i in 0..block_id_list.len() {
        let id = block_id_list[i];
        let input = block_inputs_list[i].clone();
        println!("ID: {}", id);
        let mut evaluator = StagedWitCompEvaluator::new(&prover_data_list[id].precompute);
        let mut eval = Vec::new();
        eval.extend(evaluator.eval_stage(input).into_iter().cloned());
        eval.extend(evaluator.eval_stage(Default::default()).into_iter().cloned());

        // Inputs are described in a length-(4 x max_num_io) array, consisted of input / output / witnesses
        let mut inputs: Vec<Integer> = vec![Integer::from(0); 4 * max_num_io];
        // Valid bit should be 1
        inputs[0] = Integer::from(1);
        inputs[2 * max_num_io] = Integer::from(1);
        for i in 0..eval.len() {
            if i < live_io_list[id].0.len() {
                // inputs
                inputs[live_io_list[id].0[i]] = eval[i].as_integer().unwrap();
            } else if i - live_io_list[id].0.len() < live_io_list[id].1.len() {
                // outputs
                let j = i - live_io_list[id].0.len();
                inputs[max_num_io + live_io_list[id].1[j]] = eval[i].as_integer().unwrap();
            } else {
                // witnesses, skip the 0th entry for the valid bit
                let j = i - live_io_list[id].0.len() - live_io_list[id].1.len();
                inputs[2 * max_num_io + j + 1] = eval[i].as_integer().unwrap();
            }
        }
        print!("{:3} ", " ");
        for i in 0..max_num_io {
            print!("{:3} ", i);
        }
        println!();
        print!("{:3} ", "I");
        for i in 0..max_num_io {
            print!("{:3} ", inputs[i]);
        }
        println!();
        print!("{:3} ", "O");
        for i in max_num_io..2 * max_num_io {
            print!("{:3} ", inputs[i]);
        }
        println!();
        print!("{:3} ", "W");
        for i in 2 * max_num_io..4 * max_num_io {
            print!("{:3} ", inputs[i]);
        }
        println!();

        inputs_list.push(inputs.iter().map(|i| integer_to_bytes(i.clone())).collect());
    }
}
