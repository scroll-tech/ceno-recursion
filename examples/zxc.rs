// TODO: Program broke down when there is a dead program parameter
// TODO: Need to reorder the blocks by number of execution
// TODO: PMR needs rework

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
use circ::target::r1cs::ProverData;

use std::fs::File;
// use std::io::Read;
use std::io::Write;

use circ::cfg::{
    cfg,
    clap::{self, Parser, ValueEnum},
    CircOpt,
};
use std::path::PathBuf;
use zokrates_pest_ast::*;

const INPUT_OFFSET: usize = 6;
const OUTPUT_OFFSET: usize = 5;

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
    args_a: Vec<(usize, isize)>,
    args_b: Vec<(usize, isize)>,
    args_c: Vec<(usize, isize)>
}

impl SparseMatEntry {
    // Note: Only works if value does not wrap around the field
    fn verify(&self, vars: &Vec<usize>) {
        let mut a = 0;
        let mut b = 0;
        let mut c = 0;
        for (i, m) in &self.args_a {
            a += vars[*i] as isize * m;
        }
        for (i, m) in &self.args_b {
            b += vars[*i] as isize * m;
        }
        for (i, m) in &self.args_c {
            c += vars[*i] as isize * m;
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
            args_a.push((v_cnst, c.0.constant.signed_int().to_isize().unwrap()));
        }
        for (var, coeff) in c.0.monomials.iter() {
            match var.ty() {
                VarType::Inst => args_a.push((io_relabel(var.number()), coeff.signed_int().to_isize().unwrap())),
                VarType::FinalWit => args_a.push((witness_relabel(var.number()), coeff.signed_int().to_isize().unwrap())),
                _ => panic!("Unsupported variable type!")
            }
        }
        if !c.1.constant_is_zero() {
            args_b.push((v_cnst, c.1.constant.signed_int().to_isize().unwrap()));
        }
        for (var, coeff) in c.1.monomials.iter() {
            match var.ty() {
                VarType::Inst => args_b.push((io_relabel(var.number()), coeff.signed_int().to_isize().unwrap())),
                VarType::FinalWit => args_b.push((witness_relabel(var.number()), coeff.signed_int().to_isize().unwrap())),
                _ => panic!("Unsupported variable type!")
            }
        }
        if !c.2.constant_is_zero() {
            args_c.push((v_cnst, c.2.constant.signed_int().to_isize().unwrap()));
        }
        for (var, coeff) in c.2.monomials.iter() {
            match var.ty() {
                VarType::Inst => args_c.push((io_relabel(var.number()), coeff.signed_int().to_isize().unwrap())),
                VarType::FinalWit => args_c.push((witness_relabel(var.number()), coeff.signed_int().to_isize().unwrap())),
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

// --
// Structures to match Spartan
// --
struct CompileTimeKnowledge {
    block_num_instances: usize,
    num_vars: usize,
    total_num_proofs_bound: usize,
    block_num_mem_accesses: Vec<usize>,
    total_num_mem_accesses_bound: usize,
  
    args: Vec<Vec<(Vec<(usize, isize)>, Vec<(usize, isize)>, Vec<(usize, isize)>)>>,
  
    func_input_width: usize,
    input_offset: usize,
    input_block_num: usize,
    output_offset: usize,
    output_block_num: usize
}

impl CompileTimeKnowledge {
    fn write_to_file(&self, benchmark_name: String) -> std::io::Result<()> {
        let file_name = format!("../zok_tests/constraints/{}.ctk", benchmark_name);
        let mut f = File::create(file_name)?;
        writeln!(&mut f, "{}", self.block_num_instances)?;
        writeln!(&mut f, "{}", self.num_vars)?;
        writeln!(&mut f, "{}", self.total_num_proofs_bound)?;
        for i in &self.block_num_mem_accesses {
            write!(&mut f, "{} ", i)?;
        }
        writeln!(&mut f, "")?;
        writeln!(&mut f, "{}", self.total_num_mem_accesses_bound)?;

        // Instances
        let mut counter = 0;
        for inst in &self.args {
            writeln!(&mut f, "INST {}", counter)?;
            for cons in inst {
                write!(&mut f, "A ")?;
                for (var, val) in &cons.0 {
                    write!(&mut f, "{} {} ", var, val)?;
                }
                writeln!(&mut f, "")?;
                write!(&mut f, "B ")?;
                for (var, val) in &cons.1 {
                    write!(&mut f, "{} {} ", var, val)?;
                }
                writeln!(&mut f, "")?;
                write!(&mut f, "C ")?;
                for (var, val) in &cons.2 {
                    write!(&mut f, "{} {} ", var, val)?;
                }
                writeln!(&mut f, "")?;
            }
            counter += 1;
        }
        writeln!(&mut f, "INST_END")?;

        writeln!(&mut f, "{}", self.func_input_width)?;
        writeln!(&mut f, "{}", self.input_offset)?;
        writeln!(&mut f, "{}", self.input_block_num)?;
        writeln!(&mut f, "{}", self.output_offset)?;
        writeln!(&mut f, "{}", self.output_block_num)?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct Assignment {
    assignment: Vec<[u8; 32]>,
}
impl Assignment {
    fn new(list: Vec<[u8; 32]>) -> Assignment {
        Assignment {
            assignment: list
        }
    }

    fn write(&self, mut f: &File) -> std::io::Result<()> {
        for assg in &self.assignment {
            for i in assg {
                write!(&mut f, "{} ", i)?;
            }
            writeln!(&mut f, "")?;
        }
        Ok(())
    }
}

pub type VarsAssignment = Assignment;
pub type InputsAssignment = Assignment;
pub type MemsAssignment = Assignment;

struct RunTimeKnowledge {
    block_max_num_proofs: usize,
    block_num_proofs: Vec<usize>,
    consis_num_proofs: usize,
    total_num_mem_accesses: usize,
  
    block_vars_matrix: Vec<Vec<VarsAssignment>>,
    block_inputs_matrix: Vec<Vec<InputsAssignment>>,
    exec_inputs: Vec<InputsAssignment>,
    addr_mems_list: Vec<MemsAssignment>,
  
    input: Assignment,
    // Output can only have one entry
    output: Assignment,
    output_exec_num: usize
}

impl RunTimeKnowledge {
    fn write_to_file(&self, benchmark_name: String) -> std::io::Result<()> {
        let file_name = format!("../zok_tests/inputs/{}.rtk", benchmark_name);
        let mut f = File::create(file_name)?;
        writeln!(&mut f, "{}", self.block_max_num_proofs)?;
        for i in &self.block_num_proofs {
            write!(&mut f, "{} ", i)?;
        }
        writeln!(&mut f, "")?;
        writeln!(&mut f, "{}", self.consis_num_proofs)?;
        writeln!(&mut f, "{}", self.total_num_mem_accesses)?;

        writeln!(&mut f, "BLOCK_VARS")?;
        let mut block_counter = 0;
        for block in &self.block_vars_matrix {
            writeln!(&mut f, "BLOCK {}", block_counter)?;
            let mut exec_counter = 0;
            for exec in block {
                writeln!(&mut f, "EXEC {}", exec_counter)?;
                exec.write(&mut f)?;
                exec_counter += 1;
            }
            block_counter += 1;
        }
        writeln!(&mut f, "BLOCK_INPUTS")?;
        let mut block_counter = 0;
        for block in &self.block_inputs_matrix {
            writeln!(&mut f, "BLOCK {}", block_counter)?;
            let mut exec_counter = 0;
            for exec in block {
                writeln!(&mut f, "EXEC {}", exec_counter)?;
                exec.write(&mut f)?;
                exec_counter += 1;
            }
            block_counter += 1;
        }
        writeln!(&mut f, "EXEC_INPUTS")?;
        let mut exec_counter = 0;
        for exec in &self.exec_inputs {
            writeln!(&mut f, "EXEC {}", exec_counter)?;
            exec.write(&mut f)?;
            exec_counter += 1;
        }
        writeln!(&mut f, "ADDR_MEMS")?;
        let mut addr_counter = 0;
        for addr in &self.addr_mems_list {
            writeln!(&mut f, "ACCESS {}", addr_counter)?;
            addr.write(&mut f)?;
            addr_counter += 1;
        }
        writeln!(&mut f, "INPUTS")?;
        self.input.write(&mut f)?;
        writeln!(&mut f, "OUTPUTS")?;
        self.output.write(&mut f)?;
        writeln!(&mut f, "OUTPUTS_END")?;
        writeln!(&mut f, "{}", self.output_exec_num)?;
        Ok(())
    }
}

// --
// Generate constraints and others
// --
fn get_compile_time_knowledge<const VERBOSE: bool>(
    path: PathBuf
) -> (CompileTimeKnowledge, usize, Vec<(Vec<usize>, Vec<usize>)>, Vec<ProverData>) {
    println!("Generating Compiler Time Data...");

    let (cs, func_input_width, io_size, live_io_list, block_num_mem_accesses) = {
        let inputs = zsharp::Inputs {
            file: path.clone(),
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

    if VERBOSE {
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
    }

    let max_num_io: usize;
    if VERBOSE { println!("Converting to r1cs:"); }
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
    if VERBOSE {
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

    // Collect all necessary info
    let block_num_instances = r1cs_list.len();
    let num_vars = 2 * max_num_io;
    let total_num_proofs_bound = r1cs_list.len();
    let total_num_mem_accesses_bound = 10;
    let args: Vec<Vec<(Vec<(usize, isize)>, Vec<(usize, isize)>, Vec<(usize, isize)>)>> = 
        sparse_mat_entry.iter().map(|v| v.iter().map(|i| (i.args_a.clone(), i.args_b.clone(), i.args_c.clone())).collect()).collect();
    let input_block_num = 0;
    let output_block_num = 0;
    
    (CompileTimeKnowledge {
        block_num_instances,
        num_vars,
        total_num_proofs_bound,
        block_num_mem_accesses,
        total_num_mem_accesses_bound,
        args,
        func_input_width,
        input_offset: INPUT_OFFSET,
        input_block_num,
        output_offset: OUTPUT_OFFSET,
        output_block_num
      },
      max_num_io,
      live_io_list,
      prover_data_list
    )
}

// --
// Generate witnesses and others
// --
fn get_run_time_knowledge<const VERBOSE: bool>(
    path: PathBuf,
    entry_regs: Vec<Integer>,
    ctk: &CompileTimeKnowledge,
    max_num_io: usize,
    live_io_list: Vec<(Vec<usize>, Vec<usize>)>,
    prover_data_list: Vec<ProverData>
) -> RunTimeKnowledge {
    let num_blocks = ctk.block_num_instances;
    let num_vars = ctk.num_vars;

    let (_, block_id_list, block_inputs_list, mem_list) = {
        let inputs = zsharp::Inputs {
            file: path,
            mode: Mode::Proof
        };

        ZSharpFE::interpret(inputs, &entry_regs)
    };

    // Meta info
    // The most time any block is executed
    let mut block_max_num_proofs = 0;
    // Number of times each block is executed
    let mut block_num_proofs = vec![0; num_blocks];
    // Total number of blocks executed
    let mut consis_num_proofs = 0;
    for i in &block_id_list {
        block_num_proofs[*i] += 1;
        if block_num_proofs[*i] > block_max_num_proofs {
            block_max_num_proofs = block_num_proofs[*i];
        }
        consis_num_proofs += 1;
    }
    let total_num_mem_accesses = mem_list.len();
    let output_exec_num = block_id_list.len() - 1;

    // Block-specific info
    let zero = Integer::from(0);
    let one = Integer::from(1);
    // Start from entry block, compute value of witnesses
    let mut block_vars_matrix = vec![Vec::new(); num_blocks];
    let mut block_inputs_matrix = vec![Vec::new(); num_blocks];
    let mut exec_inputs = Vec::new();

    let mut func_outputs = Integer::from(0);
    for i in 0..block_id_list.len() {
        let id = block_id_list[i];
        let input = block_inputs_list[i].clone();
        if VERBOSE { println!("ID: {}", id); }
        let mut evaluator = StagedWitCompEvaluator::new(&prover_data_list[id].precompute);
        let mut eval = Vec::new();
        eval.extend(evaluator.eval_stage(input).into_iter().cloned());
        // Drop the last entry of io, which is the dummy return 0
        eval.pop();
        eval.extend(evaluator.eval_stage(Default::default()).into_iter().cloned());

        // Inputs are described in a length-(num_vars) array, consisted of input + output
        // Vars are described in a length-(num_vars) array, consisted of witnesses
        let mut inputs: Vec<Integer> = vec![zero.clone(); num_vars];
        let mut vars: Vec<Integer> = vec![zero.clone(); num_vars];
        // Valid bit should be 1
        inputs[0] = one.clone();
        vars[0] = one.clone();
        let input_len = live_io_list[id].0.len();
        let output_len = live_io_list[id].1.len();
        for j in 0..eval.len() {
            if j < input_len {
                // inputs
                inputs[live_io_list[id].0[j]] = eval[j].as_integer().unwrap();
            } else if j < input_len + output_len {
                // outputs
                let k = j - input_len;
                inputs[max_num_io + live_io_list[id].1[k]] = eval[j].as_integer().unwrap();
            } else {
                // witnesses, skip the 0th entry for the valid bit
                let k = j - input_len - output_len;
                vars[k + 1] = eval[j].as_integer().unwrap();
            }
        }
        if i == block_id_list.len() - 1 {
            func_outputs = inputs[max_num_io + 5].clone();
        }
        if VERBOSE {
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
            for i in max_num_io..num_vars {
                print!("{:3} ", inputs[i]);
            }
            println!();
            print!("{:3} ", "W");
            for i in 0..num_vars {
                print!("{:3} ", vars[i]);
            }
            println!();
        }

        let inputs_assignment = Assignment::new(inputs.iter().map(|i| integer_to_bytes(i.clone())).collect());
        let vars_assignment = Assignment::new(vars.iter().map(|i| integer_to_bytes(i.clone())).collect());

        exec_inputs.push(inputs_assignment.clone());
        block_vars_matrix[id].push(vars_assignment);
        block_inputs_matrix[id].push(inputs_assignment);
    }

    let mut addr_mems_list = Vec::new();
    let mut mem_last = vec![one.clone(); 4];
    for i in 0..mem_list.len() {
        let m = &mem_list[i];
        let mut mem: Vec<Integer> = vec![zero.clone(); 4];
        mem[0] = one.clone();
        mem[1] = m.0.as_integer().unwrap();
        mem[2] = m.1.as_integer().unwrap();
        // backend requires the 3rd entry to be v[k + 1] * (1 - addr[k + 1] + addr[k])
        if i != 0 {
            mem_last[3] = mem[0].clone() * (one.clone() - mem[1].clone() + mem_last[1].clone());
            addr_mems_list.push(Assignment::new(mem_last.iter().map(|i| integer_to_bytes(i.clone())).collect()));
        }
        if i == mem_list.len() - 1 {
            addr_mems_list.push(Assignment::new(mem.iter().map(|i| integer_to_bytes(i.clone())).collect()));
        } else {
            mem_last = mem;
        }
    }

    if VERBOSE {
        println!("\n--\nFUNC");
        print!("{:3} ", " ");
        for i in 0..max_num_io {
            print!("{:3} ", i);
        }
        println!();
        print!("{:3} ", "I");
        for i in 0..entry_regs.len() {
            print!("{:3} ", entry_regs[i]);
        }
        println!();
        print!("{:3} ", "O");
        println!("{:3} ", func_outputs);
    }
    let func_inputs = Assignment::new(entry_regs.iter().map(|i| integer_to_bytes(i.clone())).collect());
    let func_outputs = Assignment::new(vec![integer_to_bytes(func_outputs)]);

    RunTimeKnowledge {
        block_max_num_proofs,
        block_num_proofs,
        consis_num_proofs,
        total_num_mem_accesses,
      
        block_vars_matrix,
        block_inputs_matrix,
        exec_inputs,
        addr_mems_list,
      
        input: func_inputs,
        output: func_outputs,
        output_exec_num
    }
}

fn main() {
    let func_inputs: Vec<usize> = vec![2, 5];

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
    let (ctk, max_num_io, live_io_list, prover_data_list) = 
        get_compile_time_knowledge::<false>(options.path.clone());

    // --
    // Generate Witnesses
    // --
    let entry_regs: Vec<Integer> = func_inputs.iter().map(|i| Integer::from(*i)).collect();
    let rtk = get_run_time_knowledge::<true>(options.path.clone(), entry_regs, &ctk, max_num_io, live_io_list, prover_data_list);

    // --
    // Write CTK, RTK to file
    // --
    let _ = ctk.write_to_file("2pc_demo".to_string());
    let _ = rtk.write_to_file("2pc_demo".to_string());
}
