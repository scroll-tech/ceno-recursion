// TODO: Might want to simplify Liveness Analysis & PMR now that scope changes are handled in optimization

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
use core::cmp::max;
use rug::Integer;
use circ::front::zsharp::{self, ZSharpFE};
use circ::front::{FrontEnd, Mode};
use circ::ir::opt::{opt, Opt};
/*
use circ::target::r1cs::bellman::parse_instance;
*/
use circ::target::r1cs::{R1cs, VarType, Lc};
use circ::target::r1cs::opt::reduce_linearities;
use circ::target::r1cs::trans::to_r1cs;
use circ::target::r1cs::wit_comp::StagedWitCompEvaluator;
use circ::target::r1cs::ProverData;

use std::fs::File;
use std::io::{BufReader, BufRead, Write};

use circ::cfg::{
    cfg,
    clap::{self, Parser, ValueEnum},
    CircOpt,
};
use std::path::PathBuf;
use core::cmp::Ordering;

use std::time::*;

// How many reserved variables (EXCLUDING V) are in front of the actual input / output?
// %BN, %RET, %TS, %AS, %RP, %SP, %BP
const NUM_RESERVED_VARS: usize = 7;
// Which index in the output (INCLUDING V) denotes %RET?
const OUTPUT_OFFSET: usize = 2;
// What is the maximum width (# of bits) of %TS?
const MAX_TS_WIDTH: usize = 10;

const VARS_PER_ST_ACCESS: usize = 2;
const VARS_PER_VM_ACCESS: usize = 4;

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
    args_a: Vec<(usize, Integer)>,
    args_b: Vec<(usize, Integer)>,
    args_c: Vec<(usize, Integer)>
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
            args_a.push((v_cnst, c.0.constant.i()));
        }
        for (var, coeff) in c.0.monomials.iter() {
            match var.ty() {
                VarType::Inst => args_a.push((io_relabel(var.number()), coeff.i())),
                VarType::FinalWit => args_a.push((witness_relabel(var.number()), coeff.i())),
                _ => panic!("Unsupported variable type!")
            }
        }
        if !c.1.constant_is_zero() {
            args_b.push((v_cnst, c.1.constant.i()));
        }
        for (var, coeff) in c.1.monomials.iter() {
            match var.ty() {
                VarType::Inst => args_b.push((io_relabel(var.number()), coeff.i())),
                VarType::FinalWit => args_b.push((witness_relabel(var.number()), coeff.i())),
                _ => panic!("Unsupported variable type!")
            }
        }
        if !c.2.constant_is_zero() {
            args_c.push((v_cnst, c.2.constant.i()));
        }
        for (var, coeff) in c.2.monomials.iter() {
            match var.ty() {
                VarType::Inst => {
                    args_c.push((io_relabel(var.number()), coeff.i()))
                },
                VarType::FinalWit => args_c.push((witness_relabel(var.number()), coeff.i())),
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
    let field = Integer::from_str_radix("7237005577332262213973186563042994240857116359379907606001950938285454250989", 10).unwrap();
    // Cast negative number to the other side of the field
    if raw < 0 {
        raw += field;
    }
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

fn write_bytes(mut f: &File, bytes: &[u8; 32]) -> std::io::Result<()> {
    // Disregard the trailing zeros
    let mut size = 32;
    while size > 0 && bytes[size - 1] == 0 {
        size -= 1;
    }
    for i in 0..size {
        write!(&mut f, "{} ", bytes[i])?;
    }
    writeln!(&mut f, "")?;

    Ok(())
}

// --
// Structures to match Spartan
// --
struct CompileTimeKnowledge {
    block_num_instances: usize,
    num_vars: usize,
    num_inputs_unpadded: usize,
    num_vars_per_block: Vec<usize>,
    block_num_phy_mem_accesses: Vec<usize>,
    block_num_vir_mem_accesses: Vec<usize>,
    max_ts_width: usize,
  
    args: Vec<Vec<(Vec<(usize, Integer)>, Vec<(usize, Integer)>, Vec<(usize, Integer)>)>>,
  
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
        writeln!(&mut f, "{}", self.num_inputs_unpadded)?;
        for i in &self.num_vars_per_block {
            write!(&mut f, "{} ", i)?;
        }
        writeln!(&mut f, "")?;
        for i in &self.block_num_phy_mem_accesses {
            write!(&mut f, "{} ", i)?;
        }
        writeln!(&mut f, "")?;
        for i in &self.block_num_vir_mem_accesses {
            write!(&mut f, "{} ", i)?;
        }
        writeln!(&mut f, "")?;
        writeln!(&mut f, "{}", self.max_ts_width)?;

        // Instances
        let mut counter = 0;
        for inst in &self.args {
            writeln!(&mut f, "INST {}", counter)?;
            for cons in inst {
                writeln!(&mut f, "A")?;
                for (var, val) in &cons.0 {
                    writeln!(&mut f, "{}", var)?;
                    write_bytes(&mut f, &integer_to_bytes(val.clone()))?;
                }
                writeln!(&mut f, "B")?;
                for (var, val) in &cons.1 {
                    writeln!(&mut f, "{}", var)?;
                    write_bytes(&mut f, &integer_to_bytes(val.clone()))?;
                }
                writeln!(&mut f, "C")?;
                for (var, val) in &cons.2 {
                    writeln!(&mut f, "{}", var)?;
                    write_bytes(&mut f, &integer_to_bytes(val.clone()))?;
                }
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
            write_bytes(&mut f, assg)?;
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
    total_num_phy_mem_accesses: usize,
    total_num_vir_mem_accesses: usize,
  
    block_vars_matrix: Vec<Vec<VarsAssignment>>,
    block_inputs_matrix: Vec<Vec<InputsAssignment>>,
    exec_inputs: Vec<InputsAssignment>,
    addr_phy_mems_list: Vec<MemsAssignment>,
    addr_vir_mems_list: Vec<MemsAssignment>,
    addr_ts_bits_list: Vec<MemsAssignment>,
  
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
        writeln!(&mut f, "{}", self.total_num_phy_mem_accesses)?;
        writeln!(&mut f, "{}", self.total_num_vir_mem_accesses)?;

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
        writeln!(&mut f, "ADDR_PHY_MEMS")?;
        let mut addr_counter = 0;
        for addr in &self.addr_phy_mems_list {
            writeln!(&mut f, "ACCESS {}", addr_counter)?;
            addr.write(&mut f)?;
            addr_counter += 1;
        }
        writeln!(&mut f, "ADDR_VIR_MEMS")?;
        let mut addr_counter = 0;
        for addr in &self.addr_vir_mems_list {
            writeln!(&mut f, "ACCESS {}", addr_counter)?;
            addr.write(&mut f)?;
            addr_counter += 1;
        }
        writeln!(&mut f, "ADDR_VM_BITS")?;
        let mut addr_counter = 0;
        for addr in &self.addr_ts_bits_list {
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

// Sort block_num_proofs and record where each entry is
struct InstanceSortHelper {
    num_exec: usize,
    index: usize,
  }
impl InstanceSortHelper {
fn new(num_exec: usize, index: usize) -> InstanceSortHelper {
        InstanceSortHelper {
            num_exec,
            index
        }
    }
}
// Ordering of InstanceSortHelper solely by num_exec
impl Ord for InstanceSortHelper {
    fn cmp(&self, other: &Self) -> Ordering {
        self.num_exec.cmp(&other.num_exec)
    }
  }
  impl PartialOrd for InstanceSortHelper {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
  }
  impl PartialEq for InstanceSortHelper {
    fn eq(&self, other: &Self) -> bool {
        self.num_exec == other.num_exec
    }
  }
  impl Eq for InstanceSortHelper {}
  

// --
// Generate constraints and others
// --
fn get_compile_time_knowledge<const VERBOSE: bool>(
    path: PathBuf
) -> (CompileTimeKnowledge, Vec<usize>, Vec<usize>, Vec<ProverData>) {
    println!("Generating Compiler Time Data...");

    let (cs, func_input_width, io_size, live_io_list, block_num_mem_accesses, live_vm_list) = {
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
    // Obtain the actual number of witnesse per block, round to the next power of 2
    let mut num_vars_per_block = Vec::new();
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
        let num_witnesses = 
            r1cs.num_vars() + 1 // add W to witness
            + VARS_PER_VM_ACCESS * block_num_mem_accesses[block_num].1 - live_vm_list[block_num].len() // remove live vm vars, add all vm vars
            - live_io_list[block_num].0.len() - live_io_list[block_num].1.len(); // remove all inputs / outputs
        num_vars_per_block.push(num_witnesses.next_power_of_two());
        // Include V * V = V and 0 = W - V
        let num_cons = r1cs.constraints().len() + 2;
        if num_witnesses > max_num_witnesses { max_num_witnesses = num_witnesses };
        if num_cons > max_num_cons { max_num_cons = num_cons };
        r1cs_list.push(r1cs);
        block_num += 1;
        block_name = format!("Block_{}", block_num);
    }
    
    max_num_witnesses = max_num_witnesses.next_power_of_two();
    let num_inputs_unpadded = io_size;
    let max_num_cons = max_num_cons.next_power_of_two();

    // Convert R1CS into Spartan sparse format
    // The final version will be of form: (v, _, i, o, wv, ma, mv, w), where
    //   v is the valid bit
    //   _ is a dummy
    //   i are the inputs
    //   o are the outputs
    //  wv is the valid bit, but in witnesses
    //  ma are addresses of all memory accesses
    //  mv are values of all memory accesses
    //   w are witnesses
    // According to the final io width, re-label all inputs and witnesses to the form (witness, input, output)
    let io_relabel = |b: usize, i: usize| -> usize {
        if i < live_io_list[b].0.len() {
            // inputs, label starts at 1, index starts at 2
            live_io_list[b].0[i] + 1
        } else {
            // outputs, label starts at 1, index starts at num_inputs_unpadded + 1
            live_io_list[b].1[i - live_io_list[b].0.len()] + num_inputs_unpadded
        }
    };
    // Add all IOs and WV in front
    let witness_relabel = |b: usize, i: usize|  -> usize {
        let num_pm_vars = VARS_PER_ST_ACCESS * block_num_mem_accesses[b].0;
        let num_live_vm_vars = live_vm_list[b].len();
        let num_vm_vars = VARS_PER_VM_ACCESS * block_num_mem_accesses[b].1;
        // physical memory accesses
        if i < num_pm_vars {
            max_num_witnesses + 1 + i
        }
        // virtual memory accesses
        else if i < num_pm_vars + num_live_vm_vars {
            max_num_witnesses + 1 + num_pm_vars + live_vm_list[b][i - num_pm_vars]
        }
        // other witneses
        else {
            max_num_witnesses + 1 + num_vm_vars + (i - num_live_vm_vars)
        }
    };
    // 0th entry is constant
    let v_cnst = 0;
    let mut sparse_mat_entry: Vec<Vec<SparseMatEntry>> = Vec::new();
    for b in 0..r1cs_list.len() {
        let r1cs = &r1cs_list[b];
        sparse_mat_entry.push(Vec::new());
        // First constraint is V * V = V
        let (args_a, args_b, args_c) =
            (vec![(v_cnst, Integer::from(1))], vec![(v_cnst, Integer::from(1))], vec![(v_cnst, Integer::from(1))]);
        sparse_mat_entry[b].push(SparseMatEntry { args_a, args_b, args_c });
        // Second constraint is 0 = W - V
        let (args_a, args_b, args_c) =
            (vec![], vec![], vec![(max_num_witnesses, Integer::from(1)), (v_cnst, Integer::from(-1))]);
        sparse_mat_entry[b].push(SparseMatEntry { args_a, args_b, args_c });
        // Iterate
        for c in r1cs.constraints() {
            sparse_mat_entry[b].push(get_sparse_cons_with_v_check(c, v_cnst, |i| io_relabel(b, i), |i| witness_relabel(b, i)));
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
    let num_vars = max_num_witnesses;
    let args: Vec<Vec<(Vec<(usize, Integer)>, Vec<(usize, Integer)>, Vec<(usize, Integer)>)>> = 
        sparse_mat_entry.iter().map(|v| v.iter().map(|i| (i.args_a.clone(), i.args_b.clone(), i.args_c.clone())).collect()).collect();
    let input_block_num = 0;
    let output_block_num = block_num_instances;

    let live_io_size = live_io_list.iter().map(|i| i.0.len() + i.1.len()).collect();
    let live_mem_size = (0..live_vm_list.len()).map(|i| VARS_PER_ST_ACCESS * block_num_mem_accesses[i].0 + live_vm_list[i].len()).collect();
    
    (CompileTimeKnowledge {
        block_num_instances,
        num_vars,
        num_inputs_unpadded,
        num_vars_per_block,
        block_num_phy_mem_accesses: block_num_mem_accesses.iter().map(|i| i.0).collect(),
        block_num_vir_mem_accesses: block_num_mem_accesses.iter().map(|i| i.1).collect(),
        max_ts_width: MAX_TS_WIDTH,
        args,
        func_input_width,
        input_offset: NUM_RESERVED_VARS,
        input_block_num,
        output_offset: OUTPUT_OFFSET,
        output_block_num
      },
      live_io_size,
      live_mem_size,
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
    live_io_size: Vec<usize>,
    live_mem_size: Vec<usize>,
    prover_data_list: Vec<ProverData>
) -> RunTimeKnowledge {
    let num_blocks = ctk.block_num_instances;
    let num_input_unpadded = ctk.num_inputs_unpadded;
    let num_ios = (2 * num_input_unpadded).next_power_of_two();
    // bl_outputs records ios of blocks as lists
    // bl_io_map maps name of io variables to their values
    // bl_outputs are used to fill in io part of vars
    // bl_io_map is used to compute witness part of vars
    let (_, block_id_list, bl_outputs_list, bl_mems_list, bl_io_map_list, phy_mem_list, vir_mem_list) = {
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
    let total_num_phy_mem_accesses = phy_mem_list.len();
    let total_num_vir_mem_accesses = vir_mem_list.len();
    let output_exec_num = block_id_list.len() - 1;

    // num_blocks_live is # of non-zero entries in block_num_proofs
    let num_blocks_live = block_num_proofs.iter().fold(0, |i, j| if *j > 0 { i + 1 } else { i });
    // Sort blocks by number of execution
    let mut inst_sorter = Vec::new();
    for i in 0..num_blocks {
      inst_sorter.push(InstanceSortHelper::new(block_num_proofs[i], i))
    }
    // Sort from high -> low
    inst_sorter.sort_by(|a, b| b.cmp(a));
    // index_rev[i] = j => the original ith entry should now be at the jth position
    let mut index_rev = vec![0; num_blocks];
    for i in 0..num_blocks {
        index_rev[inst_sorter[i].index] = i;
    }

    // Block-specific info
    let zero = Integer::from(0);
    let one = Integer::from(1);
    // Start from entry block, compute value of witnesses
    // Note: block_vars_matrix & block_inputs_matrix are sorted by block_num_proofs, tie-breaked by block id
    // Thus, block_vars_matrix[0] might NOT store the executions of block 0!
    let mut block_vars_matrix = vec![Vec::new(); num_blocks_live];
    let mut block_inputs_matrix = vec![Vec::new(); num_blocks_live];
    let mut exec_inputs = Vec::new();

    let mut func_outputs = Integer::from(0);
    for i in 0..block_id_list.len() {
        let id = block_id_list[i];
        let input = bl_io_map_list[i].clone();
        if VERBOSE { println!("ID: {}", id); }
        let mut evaluator = StagedWitCompEvaluator::new(&prover_data_list[id].precompute);
        let mut eval = Vec::new();
        eval.extend(evaluator.eval_stage(input).into_iter().cloned());
        // Drop the last entry of io, which is the dummy return 0
        eval.pop();
        eval.extend(evaluator.eval_stage(Default::default()).into_iter().cloned());

        // Inputs are described in a length-(num_vars) array, consisted of input + output
        // Vars are described in a length-(num_vars) array, consisted of witnesses
        let mut inputs: Vec<Integer> = vec![zero.clone(); num_ios];
        let mut vars: Vec<Integer> = vec![zero.clone(); ctk.num_vars_per_block[id]];
        // Valid bit should be 1
        inputs[0] = one.clone();
        vars[0] = one.clone();
        // Use bl_outputs_list to assign input
        // Note that we do not use eval because eval automatically deletes dead registers
        // (that need to stay for consistency check)
        let reg_in = &bl_outputs_list[i];
        let reg_out = &bl_outputs_list[i + 1];
        for j in 0..reg_in.len() {
            if let Some(ri) = &reg_in[j] {
                inputs[j + 1] = ri.as_integer().unwrap();
            }
            if let Some(ro) = &reg_out[j] {
                inputs[num_input_unpadded + j] = ro.as_integer().unwrap();
            }
        }
        // Use bl_mems_list to assign all memory operations
        let reg_mem = &bl_mems_list[i];
        for j in 0..reg_mem.len() {
            if let Some(rm) = &reg_mem[j] {
                vars[j + 1] = rm.as_integer().unwrap();
            }
        }

        // Use eval to assign witnesses
        let wit_offset = live_io_size[id] + live_mem_size[id];
        for j in wit_offset..eval.len() {
            // witnesses, skip the 0th entry for the valid bit
            let k = 1 + j - wit_offset + reg_mem.len();
            vars[k] = eval[j].as_integer().unwrap();
        }
        if i == block_id_list.len() - 1 {
            func_outputs = inputs[num_input_unpadded + OUTPUT_OFFSET].clone();
        }
        if VERBOSE {
            let print_width = min(num_input_unpadded - 1, 32);
            print!("{:3} ", " ");
            for i in 0..2 + print_width {
                print!("{:3} ", i);
            }
            println!();
            print!("{:3} ", "I");
            for i in 0..2 + print_width {
                print!("{:3} ", inputs[i]);
            }
            if num_input_unpadded - 1 > print_width {
                println!("...");
            } else {
                println!();
            }
            print!("{:3} {:3} {:3} ", "O", " ", " ");
            for i in num_input_unpadded + 1..num_input_unpadded + 1 + print_width {
                print!("{:3} ", inputs[i]);
            }
            if num_input_unpadded - 1 > print_width {
                println!("...");
            } else {
                println!();
            }
            print!("{:3} ", "W");
            let print_width = min(vars.len(), print_width);
            for i in 0..print_width {
                print!("{:3} ", vars[i]);
            }
            if vars.len() > print_width {
                println!("...");
            } else {
                println!();
            }
        }

        let inputs_assignment = Assignment::new(inputs.iter().map(|i| integer_to_bytes(i.clone())).collect());
        let vars_assignment = Assignment::new(vars.iter().map(|i| integer_to_bytes(i.clone())).collect());

        let slot = index_rev[id];
        exec_inputs.push(inputs_assignment.clone());
        block_vars_matrix[slot].push(vars_assignment);
        block_inputs_matrix[slot].push(inputs_assignment);
    }

    // Physical Memory: valid, D, addr, data
    let mut addr_phy_mems_list = Vec::new();
    let mut phy_mem_last = vec![one.clone(); 4];
    for i in 0..phy_mem_list.len() {
        let m = &phy_mem_list[i];
        let mut mem: Vec<Integer> = vec![zero.clone(); 4];
        mem[0] = one.clone();
        mem[2] = m.0.as_integer().unwrap();
        mem[3] = m.1.as_integer().unwrap();
        // backend requires the 1st entry to be v[k + 1] * (1 - addr[k + 1] + addr[k])
        if i != 0 {
            phy_mem_last[1] = mem[0].clone() * (one.clone() - mem[2].clone() + phy_mem_last[2].clone());
            addr_phy_mems_list.push(Assignment::new(phy_mem_last.iter().map(|i| integer_to_bytes(i.clone())).collect()));
        }
        if i == phy_mem_list.len() - 1 {
            addr_phy_mems_list.push(Assignment::new(mem.iter().map(|i| integer_to_bytes(i.clone())).collect()));
        } else {
            phy_mem_last = mem;
        }
    }

    // Virtual Memory: valid, D1, addr, data, ls, ts, _, _
    let mut addr_vir_mems_list = Vec::new();
    let mut vir_mem_last: Vec<Integer> = Vec::new();
    // TS Bits: D2, EQ, B0, B1, B2 ...
    let mut addr_ts_bits_list = Vec::new();
    let mut ts_bits_last: Vec<Integer> = Vec::new();
    for i in 0..vir_mem_list.len() {
        let m = &vir_mem_list[i];
        
        let mut mem: Vec<Integer> = vec![zero.clone(); 8];
        mem[0] = one.clone();
        mem[2] = m[0].as_integer().unwrap();
        mem[3] = m[1].as_integer().unwrap();
        mem[4] = m[2].as_integer().unwrap();
        mem[5] = m[3].as_integer().unwrap();
        
        let ts_bits: Vec<Integer> = vec![zero.clone(); (MAX_TS_WIDTH + 2).next_power_of_two()];
        // D1, D2, D3, D4
        if i != 0 {
            // D1[k] = v[k + 1] * (1 - addr[k + 1] + addr[k])
            vir_mem_last[1] = mem[0].clone() * (one.clone() - mem[2].clone() + vir_mem_last[2].clone());
            // D2[k] = D1[k] * (ls[k + 1] - STORE), where STORE = 0
            ts_bits_last[0] = vir_mem_last[1].clone() * mem[4].clone();
            // Bits of D1[k] * (ts[k + 1] - ts[k]) in ts_bits_last[2..]
            let mut d4 = vir_mem_last[1].clone() * (mem[5].clone() - vir_mem_last[5].clone());
            if d4 != 0 {
                // EQ = 1
                ts_bits_last[1] = Integer::from(1);
                // Use bits to assemble D4 - 1
                d4 -= 1;
                for i in 0..MAX_TS_WIDTH {
                    ts_bits_last[2 + i] = d4.clone() % 2;
                    d4 /= 2;
                }
            }
            addr_vir_mems_list.push(Assignment::new(vir_mem_last.iter().map(|i| integer_to_bytes(i.clone())).collect()));
            addr_ts_bits_list.push(Assignment::new(ts_bits_last.iter().map(|i| integer_to_bytes(i.clone())).collect()));
        }
        if i == vir_mem_list.len() - 1 {
            addr_vir_mems_list.push(Assignment::new(mem.iter().map(|i| integer_to_bytes(i.clone())).collect()));
            addr_ts_bits_list.push(Assignment::new(ts_bits.iter().map(|i| integer_to_bytes(i.clone())).collect()));
        } else {
            vir_mem_last = mem;
            ts_bits_last = ts_bits;
        }
    }

    if VERBOSE {
        println!("\n--\nFUNC");
        print!("{:3} ", " ");
        for i in 0..if entry_regs.len() == 0 {1} else {0} {
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
        total_num_phy_mem_accesses,
        total_num_vir_mem_accesses,
      
        block_vars_matrix,
        block_inputs_matrix,
        exec_inputs,
        addr_phy_mems_list,
        addr_vir_mems_list,
        addr_ts_bits_list,
      
        input: func_inputs,
        output: func_outputs,
        output_exec_num
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

    // --
    // Generate Constraints
    // --
    let compiler_start = Instant::now();
    let benchmark_name = options.path.as_os_str().to_str().unwrap();
    let path = PathBuf::from(format!("../zok_tests/benchmarks/{}.zok", benchmark_name));
    let (ctk, live_io_size, live_mem_size, prover_data_list) = 
        get_compile_time_knowledge::<false>(path.clone());
    let compiler_time = compiler_start.elapsed();

    // --
    // Obtain Inputs
    // --
    let witness_start = Instant::now();
    let input_file_name = format!("../zok_tests/benchmarks/{}.input", benchmark_name);
    // Assume inputs are listed in the order of the parameters
    let mut entry_regs: Vec<Integer> = Vec::new();
    let f = File::open(input_file_name).unwrap();
    let mut reader = BufReader::new(f);
    let mut buffer = String::new();
    reader.read_line(&mut buffer).unwrap();
    let _ = buffer.trim();
    while buffer != "END".to_string() {
        let split: Vec<String> = buffer.split(' ').map(|i| i.to_string().trim().to_string()).collect();
        entry_regs.push(Integer::from(split[1].parse::<usize>().unwrap()));

        buffer.clear();
        reader.read_line(&mut buffer).unwrap();
    }
    println!("INPUT: {:?}", entry_regs);

    // --
    // Generate Witnesses
    // --
    let rtk = get_run_time_knowledge::<false>(path.clone(), entry_regs, &ctk, live_io_size, live_mem_size, prover_data_list);
    let witness_time = witness_start.elapsed();

    // --
    // Write CTK, RTK to file
    // --
    let _ = ctk.write_to_file(benchmark_name.to_string());
    let _ = rtk.write_to_file(benchmark_name.to_string());

    println!("Compiler time: {}ms", compiler_time.as_millis());
    println!("\n--\nWitness time: {}ms", witness_time.as_millis());
}
