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
use log::warn;
use log::debug;
use std::cmp::Ordering;
use crate::ir::term::*;

#[derive(Debug, Clone)]
pub struct MemOp {
    pub addr: usize,
    pub data: T
}

impl MemOp {
    fn new(addr: usize, data: T) -> Self {
        let input = Self {
            addr,
            data
        };
        input
    }

    fn pretty(&self) {
        print!("Addr: {:02}\tData: ", self.addr);
        self.data.pretty(&mut std::io::stdout().lock())
            .expect("error pretty-printing value");
        println!();
    }
}
// Ordering of MemOp solely by address
impl Ord for MemOp {
    fn cmp(&self, other: &Self) -> Ordering {
        self.addr.cmp(&other.addr)
    }
}
impl PartialOrd for MemOp {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl PartialEq for MemOp {
    fn eq(&self, other: &Self) -> bool {
        self.addr == other.addr
    }
}
impl Eq for MemOp {}

// We reserve index 0 - 3 for reg_in and reg_out to:
// reg_in[0]: %RP
// reg_in[1]: %SP
// reg_in[2]: %BP
// reg_in[3]: %RET
#[derive(Debug, Clone)]
pub struct ExecState {
    pub blk_id: usize,      // ID of the block
    pub active: bool,       // Is this block active (not a dummy)?
    pub reg_in: Vec<Option<T>>,     // Input register State
    pub reg_out: Vec<Option<T>>,    // Output register State
    pub succ_id: usize,     // ID of the successor block
    pub mem_op: Vec<MemOp>  // List of memory operations within the block
}

impl ExecState {
    pub fn new(blk_id: usize, reg_size: usize) -> Self {
        let input = Self {
            blk_id,
            active: true,
            reg_in: vec![None; reg_size],
            reg_out: vec![None; reg_size],
            succ_id: 0,
            mem_op: Vec::new()
        };
        input
    }

    pub fn new_dummy(blk_id: usize, reg_size: usize) -> Self {
        let input = Self {
            blk_id,
            active: false,
            reg_in: vec![None; reg_size],
            reg_out: vec![None; reg_size],
            succ_id: 0,
            mem_op: Vec::new()
        };
        input
    }

    fn pretty(&self) {
        println!("Block ID: {}", self.blk_id);
        println!("Active: {}", self.active);
        if self.active {
            print!("Reg\t%RP\t%SP\t%BP\t%RET");
            for i in 4..self.reg_in.len() {
                print!("\t%{}", i);
            }
            print!("\nIn:");
            for i in &self.reg_in {
                print!("\t");
                if let Some(t) = i {
                    t.pretty(&mut std::io::stdout().lock())
                        .expect("error pretty-printing value");
                }
            }
            print!("\nOut:");
            for i in &self.reg_out {
                print!("\t");
                if let Some(t) = i {
                    t.pretty(&mut std::io::stdout().lock())
                        .expect("error pretty-printing value");
                }
            }
            println!("\nSuccessor ID: {}", self.succ_id);
            println!("Memory Operations:");
            for m in &self.mem_op {
                m.pretty();
            }
        }
    }
}
// Ordering of ExecState solely by block ID and then active (true > false)
impl Ord for ExecState {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.blk_id, !self.active).cmp(&(other.blk_id, !other.active))
    }
}
impl PartialOrd for ExecState {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl PartialEq for ExecState {
    fn eq(&self, other: &Self) -> bool {
        self.blk_id == other.blk_id && self.active == other.active
    }
}
impl Eq for ExecState {}

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
            print!("{key} = ");
            value.pretty(&mut std::io::stdout().lock())
            .expect("error pretty-printing value");
            println!();
        }
    }

    fn t_to_usize(&self, a: T) -> Result<usize, String> {
        let t = const_val(a)?;
        match t.ty {
            Ty::Field => {
                match &t.term.op() {
                    Op::Const(val) => {
                        match val {
                            Value::Field(f) => {
                                let intg = f.i().to_usize().ok_or("Stack Overflow: %SP or %BP exceeds usize limit.")?;
                                return Ok(intg);
                            }
                            _ => {
                                return Err(format!("This line should not be triggered unless const_val has been modified. Const_val needs to return Op::Const for Term."));
                            }
                        }
                    }
                    _ => { return Err(format!("This line should not be triggered unless const_val has been modified. Const_val needs to return Op::Const for Term.")) }
                }
            }
            _ => { return Err(format!("Fail to evaluate %BP or %SP: %BP and %SP should be stored as Field type.")) }
        }
    }

    // I am hacking cvars_stack to do the interpretation. Ideally we want a separate var_table to do so.
    // We only need BTreeMap<String, T> to finish evaluation, so the 2 Vecs of cvars_stack should always have
    // size 1.
    // Return values:
    // ret[0]: the return value of the function
    // ret[1][i]: how many times have block i been executed?
    // ret[2][i]: execution state of each block-execution
    pub fn bl_eval_entry_fn<const VERBOSE: bool>(
        &self,
        entry_bl: usize,
        entry_regs: &Vec<LiteralExpression<'ast>>, // Entry regs should match the input of the entry block
        bls: &Vec<Block<'ast>>,
        reg_size: &usize
    ) -> Result<(T, Vec<usize>, Vec<ExecState>), String> {
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

        self.cvar_enter_function();
        let mut nb = entry_bl;
        let mut phy_mem: Vec<T> = Vec::new();
        let mut terminated = false;
        let mut mem_op: Vec<MemOp>;
        
        // Process input variables
        let mut i = 0;
        for (name, ty, _) in &bls[entry_bl].inputs {
            if let Some(x) = ty {
                assert!(i < entry_regs.len());
                let e = &entry_regs[i];
                let val = self.literal_(e)?;
                self.declare_init_impl_::<true>(
                    name.to_string(),
                    x.clone(),
                    val,
                )?;
                i += 1;
            }
        }
        // Execute program
        while !terminated {
            bl_exec_count[nb] += 1;

            // Push-in new block state
            bl_exec_state.push(ExecState::new(nb, *reg_size));
            // Match reg_in with reg_out of last block
            if tr_size > 0 {
                bl_exec_state[tr_size].reg_in = bl_exec_state[tr_size - 1].reg_out.clone();
            }

            if VERBOSE {
                self.print_all_vars_in_scope();
                print!("%PHY: [");
                for c in &phy_mem {
                    c.pretty(&mut std::io::stdout().lock())
                    .expect("error pretty-printing value");
                    print!(", ");
                }
                println!("]");
                let _ = &bls[nb].pretty();
            }
            (nb, phy_mem, terminated, mem_op) = self.bl_eval_impl_(&bls[nb], phy_mem)?;
            
            // Update reg_out
            bl_exec_state[tr_size].reg_out[0] = self.cvar_lookup("%RP");
            bl_exec_state[tr_size].reg_out[1] = self.cvar_lookup("%SP");
            bl_exec_state[tr_size].reg_out[2] = self.cvar_lookup("%BP");
            bl_exec_state[tr_size].reg_out[3] = self.cvar_lookup("%RET");
            for i in 4..*reg_size {
                bl_exec_state[tr_size].reg_out[i] = self.cvar_lookup(&format!("%{}", i));
            }
            // Update successor block ID
            bl_exec_state[tr_size].succ_id = nb;
            // Update Memory Op
            bl_exec_state[tr_size].mem_op = mem_op;
            tr_size += 1;
        }

        // Return value is just the value of the variable called "%RET"
        // Type of return value is checked during assignment
        let ret = self.cvar_lookup("%RET").ok_or(format!(
            "Missing return value for one or more functions."
        ));

        Ok((ret?, bl_exec_count, bl_exec_state))
    }

    // Return type:
    // ret[0]: Index of next block,
    // ret[1]: Physical memory arrangement,
    // ret[2]: Has the program terminated?
    // ret[3]: Pair of [addr, data] for all memory operations in the block
    fn bl_eval_impl_(
        &self, 
        bl: &Block<'ast>,
        mut phy_mem: Vec<T>,
    ) -> Result<(usize, Vec<T>, bool, Vec<MemOp>), String> {
        let mut mem_op: Vec<MemOp> = Vec::new();

        for s in &bl.instructions {
            match s {
                BlockContent::MemPush((var, _, offset)) => {
                    let sp_t = self.cvar_lookup("%SP").ok_or(format!("Push to %PHY failed: %SP is uninitialized."))?;
                    let sp = self.t_to_usize(sp_t)?;
                    if sp + offset != phy_mem.len() {
                        return Err(format!("Error processing %PHY push: index {sp} + {offset} does not match with stack size."));
                    } else {
                        let e = self.cvar_lookup(&var).ok_or(format!("Push to %PHY failed: pushing an out-of-scope variable: {}.", var))?;
                        phy_mem.push(e);
                    }
                    mem_op.push(MemOp::new(sp + offset, self.cvar_lookup(&var).unwrap()));
                }
                BlockContent::MemPop((var, _, offset)) => {
                    let bp_t = self.cvar_lookup("%BP").ok_or(format!("Pop from %PHY failed: %BP is uninitialized."))?;
                    let bp = self.t_to_usize(bp_t)?;
                    if bp + offset >= phy_mem.len() {
                        return Err(format!("Error processing %PHY pop: index out of bound."));
                    } else {
                        let t = phy_mem[bp + offset].clone();
                        self.cvar_assign(&var, t)?;
                    }
                    mem_op.push(MemOp::new(bp + offset, self.cvar_lookup(&var).unwrap()));         
                }
                BlockContent::Stmt(Statement::Return(_)) => {
                    return Err(format!("Blocks should not contain return statements."));
                }
                // %PHY should never appear in an assertion statement
                BlockContent::Stmt(Statement::Assertion(a)) => {
                    match self.expr_impl_::<true>(&a.expression).and_then(|v| {
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
                BlockContent::Stmt(Statement::Iteration(_)) => {
                    return Err(format!("Blocks should not contain iteration statements."));
                }
                BlockContent::Stmt(Statement::Conditional(_)) => {
                    return Err(format!("Blocks should not contain if / else statements."));
                }
                BlockContent::Stmt(Statement::Definition(d)) => {
                    // XXX(unimpl) multi-assignment unimplemented
                    assert!(d.lhs.len() <= 1);

                    self.set_lhs_ty_defn::<true>(&d)?;
                    let e = self.expr_impl_::<true>(&d.expression)?;
    
                    if let Some(l) = d.lhs.first() {
                        match l {
                            TypedIdentifierOrAssignee::Assignee(l) => {
                                let strict = match &d.expression {
                                    Expression::Unary(u) => {
                                        matches!(&u.op, UnaryOperator::Strict(_))
                                    }
                                    _ => false,
                                };
                                self.assign_impl_::<true>(&l.id.value, &l.accesses[..], e, strict)?;
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
                                self.declare_init_impl_::<true>(
                                    l.identifier.value.clone(),
                                    decl_ty,
                                    e,
                                )?;
                            }
                        }
                    } else {
                        warn!("Statement with no LHS!");
                    }
                }
                BlockContent::Stmt(Statement::CondStore(_)) => { panic!("Blocks should not contain conditional store statements.") }
            }
        };

        match &bl.terminator {
            BlockTerminator::Transition(e) => {
                match self.t_to_usize(self.expr_impl_::<true>(&e)?) {
                    Ok(nb) => { return Ok((nb, phy_mem, false, mem_op)); }, 
                    _ => { return Err("Evaluation failed: block transition evaluated to an invalid block label".to_string()); }
                }
            }
            BlockTerminator::FuncCall(fc) => Err(format!("Evaluation failed: function call to {} needs to be converted to block label.", fc)),
            BlockTerminator::ProgTerm => Ok((0, phy_mem, true, mem_op))
        }
    }
}

pub fn print_state_list(bl_exec_state: &Vec<ExecState>) {
    println!("\nExecution Trace:");
    for i in 0..bl_exec_state.len() {
        println!("--\nSTATE {}", i);
        bl_exec_state[i].pretty();
    }
}

pub fn sort_by_block(bl_exec_state: &Vec<ExecState>) -> Vec<ExecState> {
    let mut bl_sorted_state = bl_exec_state.clone();
    bl_sorted_state.sort();
    println!("\n==========\nSorting by Block:");
    for i in 0..bl_exec_state.len() {
        println!("--\nSORTED STATE {}", i);
        bl_sorted_state[i].pretty();
    }
    bl_sorted_state
}

pub fn sort_by_mem(bl_exec_state: &Vec<ExecState>) -> Vec<MemOp> {
    let mut sorted_memop_list = Vec::new();
    for b in bl_exec_state {
        sorted_memop_list.append(&mut b.mem_op.clone());
    }
    sorted_memop_list.sort();
    println!("\n==========\nSorting by Memory Address:");
    for i in 0..sorted_memop_list.len() {
        sorted_memop_list[i].pretty();
    }
    sorted_memop_list   
}