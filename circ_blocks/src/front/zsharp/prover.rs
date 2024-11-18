use std::iter::zip;
use pretty::pretty_expr;
use zokrates_pest_ast::*;
use crate::front::zsharp::ZGen;
use crate::front::zsharp::T;
use crate::front::zsharp::Ty;
use crate::front::zsharp::Value;
use crate::front::zsharp::const_bool;
use crate::front::zsharp::const_val;
use crate::front::zsharp::span_to_string;
use crate::front::zsharp::Op;
use std::collections::BTreeMap;
use crate::front::zsharp::blocks::*;
use crate::front::zsharp::*;
use crate::front::zsharp::pretty::pretty_name;
use log::warn;
use log::debug;
use std::cmp::Ordering;
use crate::ir::term::*;

use rug::Integer;

const STORE: usize = 0;
const LOAD: usize = 1;

const O_RET: &str = "%o000002";
const W_TS: &str = "%w1";
const W_AS: &str = "%w2";
const W_SP: &str = "%w3";
const W_BP: &str = "%w4";

#[derive(Debug, Clone)]
pub struct MemOp {
    // Address in usize for sorting
    pub addr: usize,
    // Address in T for witness generation
    pub addr_t: T,
    pub data_t: T,

    pub ls_t: Option<T>,
    // Timestamp in usize for sorting
    pub ts: Option<usize>,
    // Timestamp in T for witness generation
    pub ts_t: Option<T>,
}

impl MemOp {
    fn new_phy(addr: usize, addr_t: T, data_t: T) -> Self {
        let input = Self {
            addr,
            addr_t,
            data_t,
            ls_t: None,
            ts: None,
            ts_t: None,
        };
        input
    }

    fn new_vir(addr: usize, addr_t: T, data_t: T, ls_t: T, ts: usize, ts_t: T) -> Self {
        let input = Self {
            addr,
            addr_t,
            data_t,
            ls_t: Some(ls_t),
            ts: Some(ts),
            ts_t: Some(ts_t),
        };
        input
    }
}
// Ordering of MemOp solely by address
impl Ord for MemOp {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.addr, self.ts).cmp(&(other.addr, other.ts))
    }
}
impl PartialOrd for MemOp {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl PartialEq for MemOp {
    fn eq(&self, other: &Self) -> bool {
        self.addr == other.addr && self.ts == other.ts
    }
}
impl Eq for MemOp {}

// We reserve indices for reg_in and reg_out to:
// reg  0   1   2   3   4   5   6   7   8
//      V  BN  RET TS  AS  SP  BP  i7  i8
#[derive(Debug, Clone)]
pub struct ExecState {
    pub blk_id: usize,      // ID of the block
    pub reg_out: Vec<Option<T>>,    // Output register State
    pub succ_id: usize,     // ID of the successor block
    pub phy_mem_op: Vec<MemOp>,  // List of physical memory operations within the block
    pub vir_mem_op: Vec<MemOp>,  // List of virtual memory operations within the block
    pub wit_op: Vec<T>, // List of witnesses in the block
}

impl ExecState {
    pub fn new(blk_id: usize, io_size: usize) -> Self {
        let input = Self {
            blk_id,
            reg_out: vec![None; io_size],
            succ_id: 0,
            phy_mem_op: Vec::new(),
            vir_mem_op: Vec::new(),
            wit_op: Vec::new(),
        };
        input
    }
}

impl<'ast> ZGen<'ast> {
    fn print_all_vars_in_scope(&self) {
        println!("\n\nVariables in scope:");

        let mut all_vars = BTreeMap::new();
        let binding = self.cvars_stack.borrow_mut();
        let maps = binding.last().unwrap();
        for map in maps {
            for (key, value) in map.iter() {
                all_vars.insert(key, value);
            }
        }
        
        for (key, value) in all_vars {
            print!("{} = ", pretty_name(key));
            value.pretty(&mut std::io::stdout().lock()).unwrap_or({
                print!("_");
            });
            println!();
        }
    }

    fn t_to_usize(&self, a: T) -> Result<usize, String> {
        let t = const_val(a)?;
        match &t.term.op() {
            Op::Const(val) => {
                match val {
                    Value::Field(f) => {
                        let intg = f.i().to_usize().ok_or("Stack Overflow: array index exceeds usize limit.")?;
                        return Ok(intg);
                    }
                    Value::BitVector(bv) => {
                        let intg = bv.uint().to_usize().ok_or("Stack Overflow: array index exceeds usize limit.")?;
                        return Ok(intg);
                    }
                    Value::Int(i) => {
                        let intg = i.to_usize().ok_or("Stack Overflow: array index exceeds usize limit.")?;
                        return Ok(intg);
                    }
                    _ => {
                        return Err(format!("Fail to evaluate array index: index is not a number."));
                    }
                }
            }
            _ => { return Err(format!("This line should not be triggered unless const_val has been modified. Const_val needs to return Op::Const for Term.")) }
        }
    }

    fn int_to_t(&self, int: &Integer, ty: &Ty) -> Result<T, String> {
        let e = &(LiteralExpression::DecimalLiteral(
            DecimalLiteralExpression {
                value: DecimalNumber {
                    value: int.to_string(),
                    span: Span::new("", 0, 0).unwrap()
                },
                suffix: Some(match ty {
                    Ty::Field => DecimalSuffix::Field(FieldSuffix {
                        span: Span::new("", 0, 0).unwrap()
                    }),
                    Ty::Uint(64) => DecimalSuffix::U64(U64Suffix {
                        span: Span::new("", 0, 0).unwrap()
                    }),
                    Ty::Uint(32) => DecimalSuffix::U32(U32Suffix {
                        span: Span::new("", 0, 0).unwrap()
                    }),
                    Ty::Uint(16) => DecimalSuffix::U16(U16Suffix {
                        span: Span::new("", 0, 0).unwrap()
                    }),
                    Ty::Uint(8) => DecimalSuffix::U8(U8Suffix {
                        span: Span::new("", 0, 0).unwrap()
                    }),
                    _ => panic!("Unsupported input type: {:?}!", ty)
                }),
                span: Span::new("", 0, 0).unwrap()
            }
        ));

        let val = self.literal_(e)?;
        Ok(val)
    }

    fn reg_name_to_index(&self, name: &str) -> Result<usize, String> {
        let name_bytes = name.as_bytes();
        match name_bytes[1] {
            b'i' | b'o' | b'w' => {
                let reg_index: usize = name.split_at(2).1.parse().or(Err(format!("Unknown register: {}", name)))?;
                Ok(reg_index)
            },
            _ => {
                Err(format!("Unknown register: {}", name))
            }
        }
    }

    // Convert a usize into a Field value
    fn usize_to_field(&self, val: usize) -> Result<T, String> {
        let e = &(LiteralExpression::DecimalLiteral(
            DecimalLiteralExpression {
                value: DecimalNumber {
                    value: val.to_string(),
                    span: Span::new("", 0, 0).unwrap()
                },
                suffix: Some(DecimalSuffix::Field(FieldSuffix {
                        span: Span::new("", 0, 0).unwrap()
                    })),
                span: Span::new("", 0, 0).unwrap()
            }
        ));

        self.literal_(&e)
    }


    // I am hacking cvars_stack to do the interpretation. Ideally we want a separate var_table to do so.
    // We only need BTreeMap<String, T> to finish evaluation, so the 2 Vecs of cvars_stack should always have
    // size 1, i.e. we use only one function and one scope.
    pub fn bl_eval_entry_fn<const VERBOSE: bool>(
        &self,
        entry_bl: usize,
        prog_inputs: &Vec<(String, Ty)>,
        input_liveness: &Vec<bool>,
        entry_regs: &Vec<Integer>, // Entry regs should match the input of the entry block
        entry_stacks: &Vec<Vec<Integer>>,
        entry_arrays: &Vec<Vec<Integer>>,
        entry_witnesses: &Vec<Integer>,
        bls: &Vec<Block<'ast>>,
        io_size: usize
    ) -> Result<(
        T, // Return value
        Vec<usize>, // Block ID
        Vec<Option<T>>, // Program input state
        Vec<ExecState>, // Block output states
        Vec<MemOp>, // Input Physical Memory operations
        Vec<MemOp>, // Input Virtual Memory operations
        Vec<MemOp>, // Physical Memory operations
        Vec<MemOp> // Virtual Memory operations
    ), String> {
        if bls.len() < entry_bl {
            return Err(format!("Invalid entry_bl: entry_bl exceeds block size."));
        }

        // We assume that all errors has been handled in bl_gen functions        
        debug!("Block Eval Const entry: {}", entry_bl);

        // How many total blocks have we executed?
        let mut tr_size = 0;
        // bl_exec_count[i]: how many times have block i been executed?
        let mut bl_exec_count: Vec<usize> = vec![0; bls.len()];
        // bl_exec_state[i]: execution state of each block-execution
        let mut bl_exec_state: Vec<ExecState> = Vec::new();

        let mut nb = entry_bl;
        let mut io_regs: Vec<Option<T>> = Vec::new();
        let mut wit_regs: Vec<Option<T>> = Vec::new();
        let mut phy_mem: Vec<Option<T>> = Vec::new();
        let mut vir_mem: Vec<Option<T>> = Vec::new();
        let mut terminated = false;
        let mut init_phy_mem_list: Vec<MemOp> = Vec::new();
        let mut init_vir_mem_list: Vec<MemOp> = Vec::new();
        
        // Process input variables & arrays
        // Add %BN, %SP, and %AS to the front of inputs
        // Note: %SP and %AS are handled by the input parser and is already present in entry_regs
        let entry_regs = &[vec![Integer::from(0)], entry_regs.clone()].concat();
        let prog_inputs = &[vec![("%BN".to_string(), Ty::Field), ("%SP".to_string(), Ty::Field), ("%AS".to_string(), Ty::Field)], prog_inputs.clone()].concat();
        let entry_stacks = &[vec![vec![]], vec![vec![]], vec![vec![]], entry_stacks.clone()].concat();
        let entry_arrays = &[vec![vec![]], vec![vec![]], vec![vec![]], entry_arrays.clone()].concat();
        let input_liveness = &[vec![true], input_liveness.clone()].concat();

        let mut prog_reg_in = vec![None; io_size];
        // The next stack / address to allocate
        let mut stack_addr_count = 0;
        let mut mem_addr_count = 0;
        // The index in prog_inputs
        let mut i = 0;
        // The corresponding index in bls[entry_bl].input
        let mut input_count = 0;
        assert_eq!(prog_inputs.len(), entry_regs.len());
        assert_eq!(prog_inputs.len(), entry_stacks.len());
        assert_eq!(prog_inputs.len(), entry_arrays.len());
        assert_eq!(prog_inputs.len(), input_liveness.len());
        for ((_, x), alive) in zip(prog_inputs, input_liveness) {
            assert!(i < entry_regs.len());

            // Determine if ty is basic or complex
            match x {
                Ty::Uint(_) | Ty::Field | Ty::Bool => {
                    if *alive {
                        let (name, _) = &bls[entry_bl].inputs[input_count];
                        let val = self.int_to_t(&entry_regs[i], &x)?;
                        self.bl_eval_assign_impl_(&mut io_regs, &mut wit_regs, name, val)?;
                        input_count += 1;
                    }
                },
                Ty::Array(read_only, _, entry_ty) => {
                    let entry_ty = match **entry_ty {
                        Ty::Uint(_) | Ty::Field | Ty::Bool => { &*entry_ty },
                        Ty::Array(..) | Ty::Struct(..) => { &Ty::Field }
                        _ => { panic!("Mut Array input type not supported!") }
                    };
                    if *alive {
                        let (name, _) = &bls[entry_bl].inputs[input_count];
                        // Declare the array as a pointer
                        let val = self.int_to_t(&entry_regs[i], &Ty::Field)?;
                        self.bl_eval_assign_impl_(&mut io_regs, &mut wit_regs, name, val)?;
                        input_count += 1;
                    }
                    // Add all entries as STOREs
                    if *read_only {
                        assert_eq!(entry_arrays[i].len(), 0);
                        for entry in &entry_stacks[i] {
                            let addr = stack_addr_count;
                            let addr_t = self.int_to_t(&Integer::from(stack_addr_count), &Ty::Field)?;
                            let data_t = self.int_to_t(&entry, &*entry_ty)?;
                            phy_mem.push(Some(data_t.clone()));
                            init_phy_mem_list.push(MemOp::new_phy(addr, addr_t, data_t));
                            stack_addr_count += 1;
                        }
                    } else {
                        assert_eq!(entry_stacks[i].len(), 0);
                        for entry in &entry_arrays[i] {
                            let addr = mem_addr_count;
                            let addr_t = self.int_to_t(&Integer::from(mem_addr_count), &Ty::Field)?;
                            let data_t = self.int_to_t(&entry, &*entry_ty)?;
                            let ls_t = self.int_to_t(&Integer::from(STORE), &Ty::Field)?;
                            let ts = 0;
                            let ts_t = self.int_to_t(&Integer::from(0), &Ty::Field)?;
                            vir_mem.push(Some(data_t.clone()));
                            init_vir_mem_list.push(MemOp::new_vir(addr, addr_t, data_t, ls_t, ts, ts_t));
                            mem_addr_count += 1;
                        }
                    }
                },
                _ => { panic!("Struct input type not supported!") }
            }
            i += 1;
        }
        
        // The next witness to use
        let mut witness_count = 0;
        // Execute program
        while !terminated {
            bl_exec_count[nb] += 1;

            // Push-in new block state
            bl_exec_state.push(ExecState::new(nb, io_size));
            // If it is the first block, add input to prog_reg_in
            if tr_size == 0 {
                for i in 1..io_size {
                    prog_reg_in[i] = self.bl_eval_identifier_impl_(&io_regs, &wit_regs, &format!("%i{:06}", i)).ok();
                }
            }
            // Block transition is largely free, unless an input is not defined in the previous output, 
            // then set it to 0 / false
            // Record the transition state
            else {
                for (name, ty) in &bls[nb].inputs {
                    if let Some(x) = ty {
                        if self.bl_eval_identifier_impl_(&io_regs, &wit_regs, name).is_err() {
                            let lit = match x {
                                Ty::Bool => {
                                    LiteralExpression::BooleanLiteral(BooleanLiteralExpression {
                                        value: "false".to_string(),
                                        span: Span::new("", 0, 0).unwrap()
                                    })
                                },
                                _ => {
                                    LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                                        value: DecimalNumber {
                                            value: "0".to_string(),
                                            span: Span::new("", 0, 0).unwrap()
                                        },
                                        suffix: Some(match x {
                                            Ty::Field => DecimalSuffix::Field(FieldSuffix {
                                                span: Span::new("", 0, 0).unwrap()
                                            }),
                                            Ty::Uint(64) => DecimalSuffix::U64(U64Suffix {
                                                span: Span::new("", 0, 0).unwrap()
                                            }),
                                            Ty::Uint(32) => DecimalSuffix::U32(U32Suffix {
                                                span: Span::new("", 0, 0).unwrap()
                                            }),
                                            Ty::Uint(16) => DecimalSuffix::U16(U16Suffix {
                                                span: Span::new("", 0, 0).unwrap()
                                            }),
                                            Ty::Uint(8) => DecimalSuffix::U8(U8Suffix {
                                                span: Span::new("", 0, 0).unwrap()
                                            }),
                                            _ => panic!("Unsupported input type: {:?}!", x)
                                        }),
                                        span: Span::new("", 0, 0).unwrap()
                                    })
                                }
                            };
                            let val = self.literal_(&lit).unwrap();
                            self.bl_eval_assign_impl_(&mut io_regs, &mut wit_regs, name, val)?;
                        }
                    }
                }
                // Record the last transition state as the union of reg_in and reg_out
                for i in 1..io_size {
                    bl_exec_state[tr_size - 1].reg_out[i] = self.bl_eval_identifier_impl_(&io_regs, &wit_regs, &format!("%o{:06}", i)).ok();
                }
            }

            if VERBOSE {
                self.print_all_vars_in_scope();
                print!("%PHY: [");
                for c in &phy_mem {
                    if let Some(c) = c { 
                        c.pretty(&mut std::io::stdout().lock())
                        .expect("error pretty-printing value");
                    } else {
                        print!("_");
                    }
                    print!(", ");
                }
                println!("]");
                print!("%VIR: [");
                for c in &vir_mem {
                    if let Some(c) = c { 
                        c.pretty(&mut std::io::stdout().lock())
                        .expect("error pretty-printing value");
                    } else {
                        print!("_");
                    }
                    print!(", ");
                }
                println!("]");
                let _ = &bls[nb].pretty();
                println!();
            }

            let phy_mem_op: Vec<MemOp>;
            let vir_mem_op: Vec<MemOp>;
            let wit_op: Vec<T>;
            (nb, terminated, phy_mem_op, vir_mem_op, wit_op, witness_count) = 
                self.bl_eval_impl_(&bls[nb], &mut io_regs, &mut wit_regs, &mut phy_mem, &mut vir_mem, entry_witnesses, witness_count)?;
            // Remove undeclared %o registers
            let mut live_o_regs = vec![false; io_regs.len()];
            if bl_exec_state.len() > 1 {
                for (name, _) in &bls[bl_exec_state[tr_size].blk_id].outputs {
                    let reg_index = self.reg_name_to_index(name)?;
                    live_o_regs[reg_index] = true;
                }
                for i in 0..io_regs.len() {
                    if !live_o_regs[i] {
                        io_regs[i] = None;
                    }
                }
            }
            // Update successor block ID
            bl_exec_state[tr_size].succ_id = nb;
            // Update Memory Op
            bl_exec_state[tr_size].phy_mem_op = phy_mem_op;
            bl_exec_state[tr_size].vir_mem_op = vir_mem_op;
            bl_exec_state[tr_size].wit_op = wit_op;
            tr_size += 1;
        }
        
        // Record the final transition state
        for i in 1..io_size {
            bl_exec_state[tr_size - 1].reg_out[i] = self.bl_eval_identifier_impl_(&io_regs, &wit_regs, &format!("%o{:06}", i)).ok();
        }
        // Return value is just the value of the variable called "%RET"
        // Type of return value is checked during assignment
        let ret = self.bl_eval_identifier_impl_(&io_regs, &wit_regs, O_RET).or(
            Err(format!("Missing return value for one or more functions."))
        );

        let (phy_mem_list, vir_mem_list) = sort_by_mem(&init_phy_mem_list, &init_vir_mem_list, &bl_exec_state);
        Ok((ret?, bl_exec_count, prog_reg_in, bl_exec_state, init_phy_mem_list, init_vir_mem_list, phy_mem_list, vir_mem_list))
    }

    // Return type:
    // ret[0]: Index of next block,
    // ret[1]: Physical memory arrangement,
    // ret[2]: Virtual memory map,
    // ret[3]: Has the program terminated?
    // ret[4]: Pairs of [addr, data] for all physical (scoping) memory operations in the block
    // ret[5]: Quadruples of [addr, data, ls, ts] for all virtual memory operations in the block
    fn bl_eval_impl_(
        &self, 
        bl: &Block<'ast>,
        io_regs: &mut Vec<Option<T>>,
        wit_regs: &mut Vec<Option<T>>,
        phy_mem: &mut Vec<Option<T>>,
        vir_mem: &mut Vec<Option<T>>,
        entry_witnesses: &Vec<Integer>,
        mut witness_count: usize,
    ) -> Result<(usize, bool, Vec<MemOp>, Vec<MemOp>, Vec<T>, usize), String> {
        debug!("Block eval impl: {}", bl.name);

        // Record all RO mem ops before any PHY mem ops
        let mut phy_mem_op: Vec<MemOp> = Vec::new();
        let mut ro_mem_op: Vec<MemOp> = Vec::new();
        let mut vir_mem_op: Vec<MemOp> = Vec::new();
        let mut wit_op: Vec<T> = Vec::new();

        witness_count = self.bl_eval_inst_impl_(io_regs, wit_regs, &bl.instructions, phy_mem, vir_mem, &mut phy_mem_op, &mut ro_mem_op, &mut vir_mem_op, &mut wit_op, entry_witnesses, witness_count)?;
        ro_mem_op.extend(phy_mem_op);
        let phy_mem_op = ro_mem_op;

        match &bl.terminator {
            BlockTerminator::Transition(e) => {
                match self.t_to_usize(self.bl_eval_expr_impl_(io_regs, wit_regs, &e)?) {
                    Ok(nb) => { return Ok((nb, false, phy_mem_op, vir_mem_op, wit_op, witness_count)); }, 
                    _ => { return Err("Evaluation failed: block transition evaluated to an invalid block label".to_string()); }
                }
            }
            BlockTerminator::FuncCall(fc) => Err(format!("Evaluation failed: function call to {} needs to be converted to block label.", fc)),
            BlockTerminator::ProgTerm => Ok((0, true, phy_mem_op, vir_mem_op, wit_op, witness_count))
        }
    }

    fn bl_eval_inst_impl_(
        &self,
        io_regs: &mut Vec<Option<T>>,
        wit_regs: &mut Vec<Option<T>>,
        inst: &Vec<BlockContent>,
        phy_mem: &mut Vec<Option<T>>,
        vir_mem: &mut Vec<Option<T>>,
        phy_mem_op: &mut Vec<MemOp>,
        ro_mem_op: &mut Vec<MemOp>,
        vir_mem_op: &mut Vec<MemOp>,
        wit_op: &mut Vec<T>, 
        entry_witnesses: &Vec<Integer>,
        mut witness_count: usize,
    ) -> Result<usize, String> {
        for s in inst {
            debug!("Block eval inst impl: {:?}", s);
            match s {
                BlockContent::Witness((var, ty, alive)) => {
                    if *alive {
                        let ty = if let Ty::Array(..) = ty { &Ty::Field } else { ty };
                        let val = self.int_to_t(&entry_witnesses[witness_count], &ty)?;
                        self.bl_eval_assign_impl_(io_regs, wit_regs, var, val.clone())?;
                        wit_op.push(val);
                    }
                    witness_count += 1;
                }
                BlockContent::MemPush((var, _, offset)) => {
                    let sp_t = self.bl_eval_identifier_impl_(io_regs, wit_regs, W_SP)?;
                    let sp = self.t_to_usize(sp_t)?;
                    if sp + offset != phy_mem.len() {
                        return Err(format!("Error processing %PHY push: index {sp} + {offset} does not match with stack size {}.", phy_mem.len()));
                    } else {
                        let mut val_t = self.bl_eval_identifier_impl_(io_regs, wit_regs, var)?;
                        phy_mem.push(Some(val_t.clone()));
                        // Convert val_t to field for MemOp
                        if val_t.type_() != &Ty::Field {
                            val_t = uint_to_field(val_t).unwrap();
                        }
                        phy_mem_op.push(MemOp::new_phy(sp + offset, self.usize_to_field(sp + offset)?, val_t));
                    }
                }
                BlockContent::MemPop((var, _, offset)) => {
                    let bp_t = self.bl_eval_identifier_impl_(io_regs, wit_regs, W_BP)?;
                    let bp = self.t_to_usize(bp_t)?;
                    if bp + offset >= phy_mem.len() {
                        return Err(format!("Error processing %PHY pop: index out of bound."));
                    } else {
                        let t = phy_mem[bp + offset].clone();
                        self.bl_eval_assign_impl_(io_regs, wit_regs, &var, t.unwrap())?;
                    }
                    // Convert val_t to field for MemOp
                    let mut val_t = self.bl_eval_identifier_impl_(io_regs, wit_regs, var)?;
                    if val_t.type_() != &Ty::Field {
                        val_t = uint_to_field(val_t).unwrap();
                    }
                    phy_mem_op.push(MemOp::new_phy(bp + offset, self.usize_to_field(bp + offset)?, val_t));         
                }
                BlockContent::ArrayInit((arr, _, len_expr, read_only)) => {
                    // Declare the array as a pointer (field), set to %SP or %AS
                    let pointer_t = if *read_only {
                        self.bl_eval_identifier_impl_(io_regs, wit_regs, W_SP)?
                    } else {
                        self.bl_eval_identifier_impl_(io_regs, wit_regs, W_AS)?
                    };
                    self.bl_eval_assign_impl_(io_regs, wit_regs, &arr, pointer_t.clone())?;
                    // Increment %AS by size of array
                    let mut len_t = self.bl_eval_expr_impl_(io_regs, wit_regs, &len_expr).unwrap();
                    if len_t.type_() != &Ty::Field {
                        len_t = uint_to_field(len_t).unwrap();
                    }
                    let new_pointer_t = add(pointer_t, len_t).unwrap();
                    self.bl_eval_assign_impl_(io_regs, wit_regs, if *read_only { W_SP } else { W_AS }, new_pointer_t)?;
                }
                BlockContent::Store((val_expr, ty, arr, id_expr, init, read_only)) => {
                    let mut val_t = self.bl_eval_expr_impl_(io_regs, wit_regs, &val_expr)?;
                    let entry_ty = val_t.type_();
                    if ty != entry_ty {
                        return Err(format!(
                            "STORE type mismatch: {} annotated vs {} actual",
                            ty, entry_ty,
                        ));
                    }

                    let mut id_t = self.bl_eval_expr_impl_(io_regs, wit_regs, &id_expr)?;

                    // Add array offset to obtain address
                    let offset_t = self.bl_eval_identifier_impl_(io_regs, wit_regs, arr)?;
                    if id_t.type_() != &Ty::Field {
                        id_t = uint_to_field(id_t).unwrap();
                    }
                    let addr_t = add(id_t, offset_t).unwrap();
                    let addr = self.t_to_usize(addr_t.clone())?;
                    // update vir_mem, pad if necessary
                    if *read_only {
                        if addr >= phy_mem.len() { 
                            phy_mem.extend(vec![None; addr + 1 - phy_mem.len()]); 
                        }
                        phy_mem[addr] = Some(val_t.clone());

                        // Update phy_mem_op
                        // Convert val_t to field for MemOp
                        if val_t.type_() != &Ty::Field {
                            val_t = uint_to_field(val_t).unwrap();
                        }
                        ro_mem_op.push(MemOp::new_phy(
                            addr,
                            addr_t,
                            val_t,
                        ));
                    } else {
                        if addr >= vir_mem.len() { 
                            vir_mem.extend(vec![None; addr + 1 - vir_mem.len()]); 
                        }
                        vir_mem[addr] = Some(val_t.clone());

                        // Update vir_mem_op
                        let ls_t = self.bl_eval_expr_impl_(io_regs, wit_regs, &Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                            value: DecimalNumber {
                                value: STORE.to_string(),
                                span: Span::new("", 0, 0).unwrap()
                            },
                            suffix: Some(DecimalSuffix::Field(FieldSuffix {
                                span: Span::new("", 0, 0).unwrap()
                            })),
                            span: Span::new("", 0, 0).unwrap()
                        }))).unwrap();

                        // %TS = %TS + 1
                        if !init {
                            self.bl_eval_stmt_impl_(io_regs, wit_regs, &bl_gen_increment_stmt(W_TS, 1, &Ty::Field)).unwrap();
                        }
                        let ts_t = self.bl_eval_identifier_impl_(io_regs, wit_regs, W_TS)?;
                        let ts = self.t_to_usize(ts_t.clone())?;

                        // Convert val_t to field for MemOp
                        if val_t.type_() != &Ty::Field {
                            val_t = uint_to_field(val_t).unwrap();
                        }
                        vir_mem_op.push(MemOp::new_vir(
                            addr,
                            addr_t,
                            val_t,
                            ls_t,
                            ts,
                            ts_t
                        ));
                    }
                }
                BlockContent::Load((var, ty, arr, id_expr, read_only)) => {
                    let mut id_t = self.bl_eval_expr_impl_(io_regs, wit_regs, &id_expr)?;

                    // Add array offset to obtain address
                    let offset_t = self.bl_eval_identifier_impl_(io_regs, wit_regs, arr)?;
                    if id_t.type_() != &Ty::Field {
                        id_t = uint_to_field(id_t).unwrap();
                    }
                    let addr_t = add(id_t, offset_t).unwrap();
                    let addr = self.t_to_usize(addr_t.clone())?;

                    // Declare the variable
                    let mut val_t = if *read_only {
                        phy_mem[addr].clone().ok_or(format!("Read-only LOAD failed: entry {} is uninitialized.", addr))?
                    } else {
                        vir_mem[addr].clone().ok_or(format!("LOAD failed: entry {} is uninitialized.", addr))?
                    };
                    let entry_ty = val_t.type_();
                    if ty != entry_ty {
                        return Err(format!(
                            "LOAD type mismatch: {} annotated vs {} actual",
                            ty, entry_ty,
                        ));
                    }
                    self.bl_eval_assign_impl_(io_regs, wit_regs, var, val_t.clone())?;
                    // Convert val_t to field for MemOp
                    if val_t.type_() != &Ty::Field {
                        val_t = uint_to_field(val_t).unwrap();
                    }

                    // Update vir_mem_op
                    if *read_only {
                        ro_mem_op.push(MemOp::new_phy(
                            addr,
                            addr_t,
                            val_t,
                        ));
                    } else {
                        let ls_t = self.bl_eval_expr_impl_(io_regs, wit_regs, &Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                            value: DecimalNumber {
                                value: LOAD.to_string(),
                                span: Span::new("", 0, 0).unwrap()
                            },
                            suffix: Some(DecimalSuffix::Field(FieldSuffix {
                                span: Span::new("", 0, 0).unwrap()
                            })),
                            span: Span::new("", 0, 0).unwrap()
                        })))?;
                        let ts_t = self.bl_eval_identifier_impl_(io_regs, wit_regs, W_TS)?;
                        let ts = self.t_to_usize(ts_t.clone())?;
    
                        vir_mem_op.push(MemOp::new_vir(
                            addr,
                            addr_t,
                            val_t,
                            ls_t,
                            ts,
                            ts_t
                        ));
                    }
                }
                BlockContent::DummyLoad(read_only) => {
                    // Addr is 0
                    let addr_t = self.bl_eval_expr_impl_(io_regs, wit_regs, &Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                        value: DecimalNumber {
                            value: 0.to_string(),
                            span: Span::new("", 0, 0).unwrap()
                        },
                        suffix: Some(DecimalSuffix::Field(FieldSuffix {
                            span: Span::new("", 0, 0).unwrap()
                        })),
                        span: Span::new("", 0, 0).unwrap()
                    })))?;
                    let addr = self.t_to_usize(addr_t.clone())?;

                    // Val is phy_mem[0] or vir_mem[0]
                    let mut val_t = if *read_only {
                        phy_mem[addr].clone().ok_or(format!("LOAD failed: entry {} is uninitialized.", addr))?
                    } else {
                        vir_mem[addr].clone().ok_or(format!("LOAD failed: entry {} is uninitialized.", addr))?
                    };
                    // Convert val_t to field for MemOp
                    if val_t.type_() != &Ty::Field {
                        val_t = uint_to_field(val_t).unwrap();
                    }

                    // Update mem_op
                    if *read_only {
                        ro_mem_op.push(MemOp::new_phy(
                            addr,
                            addr_t,
                            val_t,
                        ));
                    } else {
                        let ls_t = self.bl_eval_expr_impl_(io_regs, wit_regs, &Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                            value: DecimalNumber {
                                value: LOAD.to_string(),
                                span: Span::new("", 0, 0).unwrap()
                            },
                            suffix: Some(DecimalSuffix::Field(FieldSuffix {
                                span: Span::new("", 0, 0).unwrap()
                            })),
                            span: Span::new("", 0, 0).unwrap()
                        }))).unwrap();
                        let ts_t = self.bl_eval_identifier_impl_(io_regs, wit_regs, W_TS)?;
                        let ts = self.t_to_usize(ts_t.clone())?;
    
                        vir_mem_op.push(MemOp::new_vir(
                            addr,
                            addr_t,
                            val_t,
                            ls_t,
                            ts,
                            ts_t
                        ));
                    }
                }
                BlockContent::Branch((cond, if_inst, else_inst)) => {
                    match self.bl_eval_expr_impl_(io_regs, wit_regs, &cond).and_then(|v| {
                        const_bool(v)
                            .ok_or_else(|| "interpreting expr as const bool failed".to_string())
                    }) {
                        Ok(true) => {
                            witness_count = self.bl_eval_inst_impl_(io_regs, wit_regs, if_inst, phy_mem, vir_mem, phy_mem_op, ro_mem_op, vir_mem_op, wit_op, entry_witnesses, witness_count)?;
                        },
                        Ok(false) => {
                            witness_count = self.bl_eval_inst_impl_(io_regs, wit_regs, else_inst, phy_mem, vir_mem, phy_mem_op, ro_mem_op, vir_mem_op, wit_op, entry_witnesses, witness_count)?;
                        },
                        Err(err) => return Err(format!(
                            "Const conditional expression eval failed: {} at\n{}",
                            err,
                            span_to_string(cond.span()),
                        ))
                    }
                }
                BlockContent::Stmt(s) => {
                    self.bl_eval_stmt_impl_(io_regs, wit_regs, s)?;
                }
            }
        };
        Ok(witness_count)
    }

    fn bl_eval_stmt_impl_(
        &self,
        io_regs: &mut Vec<Option<T>>,
        wit_regs: &mut Vec<Option<T>>,
        s: &Statement,
    ) -> Result<(), String> {
        match s {
            Statement::Return(_) => {
                return Err(format!("Blocks should not contain return statements."));
            }
            // %PHY should never appear in an assertion statement
            Statement::Assertion(a) => {
                match self.bl_eval_expr_impl_(io_regs, wit_regs, &a.expression).and_then(|v| {
                    const_bool(v)
                        .ok_or_else(|| "interpreting expr as const bool failed".to_string())
                }) {
                    Ok(true) => {},
                    Ok(false) => return Err(format!(
                        "Const assert failed: {} at\n{}",
                        a.message
                            .as_ref()
                            .map(|m| m.value.as_ref())
                            .unwrap_or("(no error message given)"),
                        span_to_string(a.expression.span()),
                    )),
                    Err(err) => return Err(format!(
                        "Const assert expression eval failed: {} at\n{}",
                        err,
                        span_to_string(a.expression.span()),
                    ))
                }
            }
            Statement::Iteration(_) => {
                return Err(format!("Blocks should not contain iteration statements."));
            }
            Statement::WhileLoop(_) => {
                return Err(format!("Blocks should not contain while loop statements."));
            }
            Statement::Conditional(_c) => {
                panic!("Blocks should not contain conditional statements.")
            }
            Statement::Definition(d) => {
                // XXX(unimpl) multi-assignment unimplemented
                assert!(d.lhs.len() <= 1);
                let e = self.bl_eval_expr_impl_(io_regs, wit_regs, &d.expression)?;

                if let Some(l) = d.lhs.first() {
                    match l {
                        TypedIdentifierOrAssignee::Assignee(l) => {
                            assert_eq!(l.accesses.len(), 0);
                            self.bl_eval_assign_impl_(io_regs, wit_regs, &l.id.value, e)?;
                        }
                        TypedIdentifierOrAssignee::TypedIdentifier(l) => {
                            let decl_ty = self.type_impl_::<true>(&l.ty)?;
                            let ty = e.type_();
                            if &decl_ty != ty {
                                return Err(format!(
                                    "Assignment type mismatch: {} annotated vs {} actual",
                                    decl_ty, ty,
                                ));
                            }
                            self.bl_eval_assign_impl_(io_regs, wit_regs, &l.identifier.value, e)?;
                        }
                    }
                } else {
                    warn!("Statement with no LHS!");
                }
            }
            Statement::CondStore(_) => { panic!("Blocks should not contain conditional store statements.") }
            Statement::Witness(_) => { panic!("Witness statements unsupported.") }
            Statement::ArrayDecl(_) => { panic!("Blocks should not contain array declaration statements.") }
        };
        Ok(())
    }

    fn bl_eval_expr_impl_(
        &self,
        io_regs: &Vec<Option<T>>,
        wit_regs: &Vec<Option<T>>,
        e: &Expression
    ) -> Result<T, String> {
        match e {
            ast::Expression::Ternary(u) => {
                match self.bl_eval_expr_impl_(io_regs, wit_regs, &u.first).ok().and_then(const_bool) {
                    Some(true) => self.bl_eval_expr_impl_(io_regs, wit_regs, &u.second),
                    Some(false) => self.bl_eval_expr_impl_(io_regs, wit_regs, &u.third),
                    None => Err("ternary condition not const bool".to_string()),
                }
            }
            ast::Expression::Binary(b) => {
                let left = self.bl_eval_expr_impl_(io_regs, wit_regs, &b.left)?;
                let right = self.bl_eval_expr_impl_(io_regs, wit_regs, &b.right)?;
                let op = self.bin_op(&b.op);
                op(left, right)
            }
            ast::Expression::Unary(u) => {
                let arg = self.bl_eval_expr_impl_(io_regs, wit_regs, &u.expression)?;
                let op = self.unary_op(&u.op);
                op(arg)
            }
            ast::Expression::Identifier(i) => {
                self.bl_eval_identifier_impl_(io_regs, wit_regs, &i.value)
            },
            ast::Expression::Literal(l) => self.literal_(l),
            ast::Expression::InlineArray(_) => {
                Err(format!("Blocks should not contain inline arrays!"))
            }
            ast::Expression::ArrayInitializer(_) => {
                Err(format!("Blocks should not contain array initializers!"))
            }
            ast::Expression::Postfix(_) => {
                Err(format!("Blocks should not contain postfixes!"))
            }
            ast::Expression::InlineStruct(_) => {
                Err(format!("Blocks should not contain inline structs!"))
            }
        }
        .and_then(|res| const_val(res))
        .map_err(|err| format!("{}; context:\n{}", err, span_to_string(e.span())))
    }

    fn bl_eval_assign_impl_(
        &self,
        io_regs: &mut Vec<Option<T>>,
        wit_regs: &mut Vec<Option<T>>,
        reg_name: &str,
        val: T
     ) -> Result<(), String> {
        let name_bytes = reg_name.as_bytes();
        match name_bytes[1] {
            b'i' | b'o' => {
                let reg_index = self.reg_name_to_index(&reg_name)?;
                if io_regs.len() <= reg_index {
                    io_regs.extend(vec![None; reg_index - io_regs.len() + 1])
                }
                io_regs[reg_index] = Some(val);
                Ok(())
            },
            b'w' => {
                let reg_index = self.reg_name_to_index(&reg_name)?;
                if wit_regs.len() <= reg_index {
                    wit_regs.extend(vec![None; reg_index - wit_regs.len() + 1])
                }
                wit_regs[reg_index] = Some(val);
                Ok(())
            },
            _ => {
                Err(format!("Unknown register: {}", reg_name))
            }
        }
    }

    fn bl_eval_identifier_impl_(
        &self,
        io_regs: &Vec<Option<T>>,
        wit_regs: &Vec<Option<T>>,
        reg_name: &str,
    ) -> Result<T, String> {
        let name_bytes = reg_name.as_bytes();
        match name_bytes[1] {
            b'i' | b'o' => {
                let reg_index = self.reg_name_to_index(&reg_name)?;
                if io_regs.len() <= reg_index {
                    Err(format!("Input register {} is uninitialized", reg_name))
                } else {
                    io_regs[self.reg_name_to_index(&reg_name)?].clone().ok_or(
                        format!("Input register {} is uninitialized", reg_name)
                    )
                }
            },
            b'w' => {
                let reg_index = self.reg_name_to_index(&reg_name)?;
                if wit_regs.len() <= reg_index {
                    Err(format!("Witness register {} is uninitialized", reg_name))
                } else {
                    wit_regs[self.reg_name_to_index(&reg_name)?].clone().ok_or(
                        format!("Witness register {} is uninitialized", reg_name)
                    )
                }
            },
            _ => {
                Err(format!("Unknown register: {}", reg_name))
            }
        }
    }
}

pub fn sort_by_mem(
    init_phy_mem_list: &Vec<MemOp>,
    init_vir_mem_list: &Vec<MemOp>,
    bl_exec_state: &Vec<ExecState>,
) -> (Vec<MemOp>, Vec<MemOp>) {
    let mut sorted_phy_mem_op_list = init_phy_mem_list.clone();
    let mut sorted_vir_mem_op_list = init_vir_mem_list.clone();
    for b in bl_exec_state {
        sorted_phy_mem_op_list.append(&mut b.phy_mem_op.clone());
        sorted_vir_mem_op_list.append(&mut b.vir_mem_op.clone());
    }
    sorted_phy_mem_op_list.sort();
    sorted_vir_mem_op_list.sort();
    (sorted_phy_mem_op_list, sorted_vir_mem_op_list)
}