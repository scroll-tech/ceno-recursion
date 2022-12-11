// TODO: Recursion is not supported.

use log::{debug, warn};

use zokrates_pest_ast::*;
use crate::front::zsharp::ZGen;
use crate::front::zsharp::PathBuf;
use crate::front::zsharp::pretty;
use crate::front::zsharp::T;
use crate::front::zsharp::Ty;
use crate::front::zsharp::Value;
use crate::front::zsharp::Loc;
use crate::front::zsharp::const_bool;
use crate::front::zsharp::const_val;
use crate::front::zsharp::span_to_string;
use crate::front::zsharp::bool;
use crate::front::zsharp::Op;
use std::collections::BTreeMap;
use pest::Span;

fn cond_expr<'ast>(ident: IdentifierExpression<'ast>, condition: Expression<'ast>) -> Expression<'ast> {
    let ce = Expression::Binary(BinaryExpression {
        op: BinaryOperator::Lt,
        left: Box::new(Expression::Identifier(ident.clone())),
        right: Box::new(condition.clone()),
        span: Span::new("", 0, 0).unwrap()
    });
    ce
}

fn ty_to_dec_suffix<'ast>(ty: Type<'ast>) -> DecimalSuffix<'ast> {
    let span = Span::new("", 0, 0).unwrap();
    match ty {
        Type::Basic(BasicType::Field(_)) => { DecimalSuffix::Field(FieldSuffix { span }) }
        Type::Basic(BasicType::U8(_)) => { DecimalSuffix::U8(U8Suffix { span }) }
        Type::Basic(BasicType::U16(_)) => { DecimalSuffix::U16(U16Suffix { span }) }
        Type::Basic(BasicType::U32(_)) => { DecimalSuffix::U32(U32Suffix { span }) }
        Type::Basic(BasicType::U64(_)) => { DecimalSuffix::U64(U64Suffix { span }) }
        _ => { panic!("Type not supported for loop iterator.") }
    }
}

#[derive(Clone)]
pub struct Block<'ast> {
    name: usize,
    instructions: Vec<BlockContent<'ast>>,
    terminator: BlockTerminator<'ast>,
}

#[derive(Clone)]
pub enum BlockContent<'ast> {
    MemPush((String, usize)), // %PHY[%SP + offset] = id
    MemPop((String, usize)),  // id = %PHY[%BP + offset]
    Stmt(Statement<'ast>) // other statements
}

#[derive(Clone)]
// Coda is the number of total types of blocks
pub enum BlockTerminator<'ast> {
    Transition(BlockTransition<'ast>),
    Coda(usize),
}

#[derive(Clone)]
// BlockTransition is of the format:
// if cond then goto tblock else goto fblock
pub struct BlockTransition<'ast> {
    cond: Expression<'ast>,
    tblock: usize,
    fblock: usize,
}

impl<'ast> Block<'ast> {
    fn new(name: usize) -> Self {
        let input = Self {
            name,
            instructions: Vec::new(),
            terminator: BlockTerminator::Coda(name + 1)
        };
        input
    }

    pub fn pretty(&self) {
        println!("\nBlock {}:", self.name);
        for c in &self.instructions {
            match c {
                BlockContent::MemPush((id, offset)) => { println!("    %PHY[%SP + {offset}] = {id}") }
                BlockContent::MemPop((id, offset)) => { println!("    {id} = %PHY[%BP + {offset}]") }
                BlockContent::Stmt(s) => { pretty::pretty_stmt(1, &s); }
            }
        }
        match &self.terminator {
            BlockTerminator::Transition(t) => {
                print!("Block Transition: ");
                pretty::pretty_expr(&t.cond);
                print!(" ? block {} : block {}", t.tblock.to_string(), t.fblock.to_string())
            }
            BlockTerminator::Coda(c) => {
                print!("Block terminates with coda {}.", c.to_string());
            }
        }
    }
}

impl<'ast> BlockTransition<'ast> {
    fn new(cond: Expression<'ast>, tblock: usize, fblock: usize) -> Self {
        let input = Self {
            cond,
            tblock,
            fblock
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
            println!("{key} = {value}");
        }
    }

    fn t_to_usize(&self, a: T) -> Result<usize, String> {
        let t = const_val(a)?;
        match t.ty {
            Ty::Field => {
                match &t.term.get().op {
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

    pub fn bl_gen_const_entry_fn(&'ast self, n: &str) -> (Vec<Block<'ast>>, usize, usize) {
        debug!("Block Gen Const entry: {}", n);
        let (f_file, f_name) = self.deref_import(n);
        if let Some(f) = self.functions.get(&f_file).and_then(|m| m.get(&f_name)) {
            if !f.generics.is_empty() {
                panic!("const_entry_fn cannot be called on a generic function")
            } else if !f.parameters.is_empty() {
                panic!("const_entry_fn must be called on a function with zero arguments")
            }
        } else {
            panic!(
                "No function '{:?}//{}' attempting const_entry_fn",
                &f_file, &f_name
            );
        }

        let mut blks = Vec::new();
        let mut blks_len = 0;
        // Create the initial block
        blks.push(Block::new(0));
        blks_len += 1;
        // Initialize %SP
        let sp_init_stmt = Statement::Definition(DefinitionStatement {
            lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                ty: Type::Basic(BasicType::Field(FieldType {
                    span: Span::new("", 0, 0).unwrap()
                })),
                identifier: IdentifierExpression {
                    value: "%SP".to_string(),
                    span: Span::new("", 0, 0).unwrap()
                },
                span: Span::new("", 0, 0).unwrap()
            })],
            expression: Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                value: DecimalNumber {
                    value: "0".to_string(),
                    span: Span::new("", 0, 0).unwrap()
                },
                suffix: Some(DecimalSuffix::Field(FieldSuffix {
                    span: Span::new("", 0, 0).unwrap()
                })),
                span: Span::new("", 0, 0).unwrap()
            })),
            span: Span::new("", 0, 0).unwrap()
        });
        blks[blks_len - 1].instructions.push(BlockContent::Stmt(sp_init_stmt));
        // Initialize %BP
        let bp_init_stmt = Statement::Definition(DefinitionStatement {
            lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                ty: Type::Basic(BasicType::Field(FieldType {
                    span: Span::new("", 0, 0).unwrap()
                })),
                identifier: IdentifierExpression {
                    value: "%BP".to_string(),
                    span: Span::new("", 0, 0).unwrap()
                },
                span: Span::new("", 0, 0).unwrap()
            })],
            expression: Expression::Identifier(IdentifierExpression {
                value: "%SP".to_string(),
                span: Span::new("", 0, 0).unwrap()
            }),
            span: Span::new("", 0, 0).unwrap()
        });
        blks[blks_len - 1].instructions.push(BlockContent::Stmt(bp_init_stmt));

        self.bl_gen_function_call_::<true>(f_file, f_name, blks, blks_len)
            .unwrap_or_else(|e| panic!("const_entry_fn failed: {}", e))
    }

    // TODO: Error handling in function call
    // The head block of the function is already created to facilitate any required initialization
    fn bl_gen_function_call_<const IS_CNST: bool>(
        &'ast self,
        f_path: PathBuf,
        f_name: String,
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
    ) -> Result<(Vec<Block>, usize, usize), String> {
        if IS_CNST {
            debug!("Block Gen Const function call: {} {:?}", f_name, f_path);
        } else {
            debug!("Block Gen Function call: {} {:?}", f_name, f_path);
        }
        let f = self
            .functions
            .get(&f_path)
            .ok_or_else(|| format!("No file '{:?}' attempting fn call", &f_path))?
            .get(&f_name)
            .ok_or_else(|| format!("No function '{}' attempting fn call", &f_name))?;

        // XXX(unimpl) multi-return unimplemented
        assert!(f.returns.len() <= 1);
        // Get the return type because we need to convert it into a variable
        let ret_ty = f
            .returns
            .first().ok_or("No return type provided for one or more function")?;
        // Use cvar to identify variable scoping for push and pull
        self.cvar_enter_function();

        // Iterate through Stmts
        for s in &f.statements {
            (blks, blks_len, _, _) = self.bl_gen_stmt_::<IS_CNST>(blks, blks_len, s, ret_ty, 0)?;
        }
        Ok((blks, 0, blks_len))
    }

    // Generate blocks from statements
    // Return value:
    // result[0]: list of blocks generated so far
    // result[1]: length of the generated blocks
    // result[2]: variables that need to be POPed after current scope, with their offset to %BP
    //            used by loop statements and potentially if / else statements
    // result[3]: variables that need to be POPed after current function, with their offset to %BP
    //            used by bl_gen_function_call
    // result[4]: offset between value of %SP and the actual size of the physical memory
    fn bl_gen_stmt_<const IS_CNST: bool>(
        &'ast self, 
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        s: &'ast Statement<'ast>,
        ret_ty: &'ast Type<'ast>,
        mut sp_offset: usize
    ) -> Result<(Vec<Block>, usize, BTreeMap<usize, String>, usize), String> {
        if IS_CNST {
            debug!("Block Gen Const stmt: {}", s.span().as_str());
        } else {
            debug!("Block Gen Stmt: {}", s.span().as_str());
        }

        let mut stmt_phy_assign = BTreeMap::new();

        match s {
            Statement::Return(r) => {
                let ret_stmt = Statement::Definition(DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                        ty: ret_ty.clone(),
                        identifier: IdentifierExpression {
                            value: "%RET".to_string(),
                            span: Span::new("", 0, 0).unwrap()
                        },
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    // Assume that we only have ONE return variable
                    expression: r.expressions[0].clone(),
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(ret_stmt));
            }
            Statement::Assertion(_) => {
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(s.clone()));
            }
            Statement::Iteration(it) => {
                let mut vars_to_pop = BTreeMap::new();
                let old_state = blks_len - 1;
                // Create and push FROM statement
                let from_stmt = Statement::Definition(DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                        ty: it.ty.clone(),
                        identifier: it.index.clone(),
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    expression: it.from.clone(),
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(from_stmt));

                // STORE iterator in Physical Mem if has appeared before
                (blks, stmt_phy_assign, sp_offset) = self.bl_gen_scoping_(blks, blks_len, &it.index.value, stmt_phy_assign, sp_offset);
                
                // New Scope
                (blks, blks_len, sp_offset) = self.bl_gen_enter_scope_::<IS_CNST>(blks, blks_len, sp_offset)?;
                let v_name = it.index.value.clone();
                let ty = self.type_impl_::<IS_CNST>(&it.ty)?;
                self.decl_impl_::<IS_CNST>(v_name, &ty)?;

                // Create new Block
                blks.push(Block::new(blks_len));
                blks_len += 1;

                let mut var_to_pop;
                // Iterate through Stmts
                for body in &it.statements {
                    (blks, blks_len, var_to_pop, sp_offset) = self.bl_gen_stmt_::<IS_CNST>(blks, blks_len, body, ret_ty, sp_offset)?;
                    vars_to_pop.extend(var_to_pop);
                }
                // Create and push STEP statement
                let step_stmt = Statement::Definition(DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::Assignee(Assignee {
                        id: it.index.clone(),
                        accesses: Vec::new(),
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    expression: Expression::Binary(BinaryExpression {
                        op: BinaryOperator::Add,
                        left: Box::new(Expression::Identifier(it.index.clone())),
                        right: Box::new(Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                            value: DecimalNumber {
                                value: "1".to_string(),
                                span: Span::new("", 0, 0).unwrap()
                            },
                            suffix: Some(ty_to_dec_suffix(it.ty.clone())),
                            span: Span::new("", 0, 0).unwrap()
                        }))),
                        span: Span::new("", 0, 0).unwrap()
                    }),
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(step_stmt));

                // POP local variables out
                for (addr, var) in vars_to_pop.iter().rev() {
                    blks[blks_len - 1].instructions.push(BlockContent::MemPop((var.to_string(), *addr)));
                }

                // Create and push TRANSITION statement
                let new_state = blks_len - 1;
                let term = BlockTerminator::Transition(
                    BlockTransition::new(
                        cond_expr(it.index.clone(), it.to.clone()), 
                        old_state + 1, 
                        new_state + 1
                    )
                );
                blks[new_state].terminator = term.clone();
                blks[old_state].terminator = term;

                // Exit Scoping
                (blks, blks_len, sp_offset) = self.bl_gen_exit_scope_::<IS_CNST>(blks, blks_len, sp_offset)?;

                // Create new Block
                blks.push(Block::new(blks_len));
                blks_len += 1;
            }
            Statement::Definition(d) => {
                // XXX(unimpl) multi-assignment unimplemented
                assert!(d.lhs.len() <= 1);

                // Handle Scoping change
                self.set_lhs_ty_defn::<IS_CNST>(d)?;
                let e = self.expr_impl_::<IS_CNST>(&d.expression)?;
                if let Some(l) = d.lhs.first() {
                    match l {
                        TypedIdentifierOrAssignee::Assignee(l) => {
                            // No scoping if lhs is an assignee, only need to make sure it has appeared before
                            let name = &l.id.value;
                            let _ = if IS_CNST {
                                self.cvar_lookup(name)
                                    .ok_or_else(|| format!("Assignment failed: no const variable {}", name))?
                            } else {
                                self.circ_get_value(Loc::local(name.to_string()))
                                    .map_err(|e| format!("{}", e))?
                                    .unwrap_term()
                            };
                        }
                        TypedIdentifierOrAssignee::TypedIdentifier(l) => {
                            let decl_ty = self.type_impl_::<IS_CNST>(&l.ty)?;
                            let ty = e.type_();
                            if &decl_ty != ty {
                                return Err(format!(
                                    "Assignment type mismatch: {} annotated vs {} actual",
                                    decl_ty, ty,
                                ));
                            }

                            // Scoping change
                            let id = &l.identifier.value;
                            (blks, stmt_phy_assign, sp_offset) = self.bl_gen_scoping_(blks, blks_len, id, stmt_phy_assign, sp_offset);

                            // Add the identifier to current scope
                            self.declare_init_impl_::<IS_CNST>(
                                id.clone(),
                                decl_ty,
                                e,
                            )?;
                        }
                    }
                } else {
                    warn!("Statement with no LHS!");
                }

                blks[blks_len - 1].instructions.push(BlockContent::Stmt(s.clone()));
            }
        }
        Ok((blks, blks_len, stmt_phy_assign, sp_offset))
    }

    // Handle scoping change by pushing old values onto the stack
    fn bl_gen_scoping_(
        &'ast self, 
        mut blks: Vec<Block<'ast>>,
        blks_len: usize,
        id: &String,
        mut stmt_phy_assign: BTreeMap<usize, String>,
        mut sp_offset: usize
    ) -> (Vec<Block>, BTreeMap<usize, String>, usize) {
        // We don't care about shadowing
        if !self.cvar_cur_scope_find(id) {
            // If the identifier is used in the previous scopes of the current function,
            // push the previous value and pop it after current scope ends
            if self.cvar_lookup(id).is_some() {
                // Push %BP onto the stack before anything else
                if sp_offset == 0 {
                    blks[blks_len - 1].instructions.push(BlockContent::MemPush(("%BP".to_string(), sp_offset)));
                    stmt_phy_assign.insert(sp_offset, "%BP".to_string());
                    sp_offset += 1;
                }
                blks[blks_len - 1].instructions.push(BlockContent::MemPush((id.to_string(), sp_offset)));
                stmt_phy_assign.insert(sp_offset, id.clone());
                sp_offset += 1;
            }
        }
        (blks, stmt_phy_assign, sp_offset)
    }

    fn bl_gen_enter_scope_<const IS_CNST: bool>(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        blks_len: usize,
        mut sp_offset: usize
    ) -> Result<(Vec<Block>, usize, usize), String> {
        // New Scoping
        self.enter_scope_impl_::<IS_CNST>();

        // Update %SP and %BP if any changes has been made
        if sp_offset > 0 {
            // %BP = %SP
            let bp_update_stmt = Statement::Definition(DefinitionStatement {
                lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                    ty: Type::Basic(BasicType::Field(FieldType {
                        span: Span::new("", 0, 0).unwrap()
                    })),
                    identifier: IdentifierExpression {
                        value: "%BP".to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    },
                    span: Span::new("", 0, 0).unwrap()
                })],
                expression: Expression::Identifier(IdentifierExpression {
                    value: "%SP".to_string(),
                    span: Span::new("", 0, 0).unwrap()
                }),
                span: Span::new("", 0, 0).unwrap()
            });
            blks[blks_len - 1].instructions.push(BlockContent::Stmt(bp_update_stmt));
            // %SP = %SP + sp_offset
            let sp_update_stmt = Statement::Definition(DefinitionStatement {
                lhs: vec![TypedIdentifierOrAssignee::Assignee(Assignee {
                    id: IdentifierExpression {
                        value: "%SP".to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    },
                    accesses: Vec::new(),
                    span: Span::new("", 0, 0).unwrap()
                })],
                expression: Expression::Binary(BinaryExpression {
                    op: BinaryOperator::Add,
                    left: Box::new(Expression::Identifier(IdentifierExpression {
                        value: "%SP".to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    })),
                    right: Box::new(Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                        value: DecimalNumber {
                            value: sp_offset.to_string(),
                            span: Span::new("", 0, 0).unwrap()
                        },
                        suffix: Some(DecimalSuffix::Field(FieldSuffix {
                            span: Span::new("", 0, 0).unwrap()
                        })),
                        span: Span::new("", 0, 0).unwrap()
                    }))),
                    span: Span::new("", 0, 0).unwrap()
                }),
                span: Span::new("", 0, 0).unwrap()
            });
            blks[blks_len - 1].instructions.push(BlockContent::Stmt(sp_update_stmt));
            sp_offset = 0;
        }
        Ok((blks, blks_len, sp_offset))
    }

    fn bl_gen_exit_scope_<const IS_CNST: bool>(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        blks_len: usize,
        mut sp_offset: usize
    ) -> Result<(Vec<Block>, usize, usize), String> {
        // Exit Scoping
        self.exit_scope_impl_::<IS_CNST>();

        // Update %SP if any changes has been made
        if sp_offset > 0 {
            // %SP = %SP + sp_offset
            let sp_update_stmt = Statement::Definition(DefinitionStatement {
                lhs: vec![TypedIdentifierOrAssignee::Assignee(Assignee {
                    id: IdentifierExpression {
                        value: "%SP".to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    },
                    accesses: Vec::new(),
                    span: Span::new("", 0, 0).unwrap()
                })],
                expression: Expression::Binary(BinaryExpression {
                    op: BinaryOperator::Add,
                    left: Box::new(Expression::Identifier(IdentifierExpression {
                        value: "%SP".to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    })),
                    right: Box::new(Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                        value: DecimalNumber {
                            value: sp_offset.to_string(),
                            span: Span::new("", 0, 0).unwrap()
                        },
                        suffix: Some(DecimalSuffix::Field(FieldSuffix {
                            span: Span::new("", 0, 0).unwrap()
                        })),
                        span: Span::new("", 0, 0).unwrap()
                    }))),
                    span: Span::new("", 0, 0).unwrap()
                }),
                span: Span::new("", 0, 0).unwrap()
            });
            blks[blks_len - 1].instructions.push(BlockContent::Stmt(sp_update_stmt));
            sp_offset = 0;
        }
        Ok((blks, blks_len, sp_offset))
    }

    // I am hacking cvars_stack to do the interpretation. Ideally we want a separate var_table to do so.
    // We only need BTreeMap<String, T> to finish evaluation, so the 2 Vecs of cvars_stack should always have
    // size 1.
    pub fn bl_eval_const_entry_fn(&self, entry_bl: usize, exit_bl: usize, bls: &Vec<Block<'ast>>) -> Result<T, String> {
        // We assume that all errors has been handled in bl_gen functions        
        debug!("Block Eval Const entry: {}", entry_bl);
        self.cvar_enter_function();
        let mut nb = entry_bl;
        let mut phy_mem = Vec::new();
        while nb != exit_bl {
            self.print_all_vars_in_scope();
            println!("%PHY:");
            for c in &phy_mem {
                println!("{c},");
            }
            println!();
            (nb, phy_mem) = self.bl_eval_impl_::<true>(&bls[nb], phy_mem)?;
        }

        // Return value is just the value of the variable called "%RET"
        // Type of return value is checked during assignment
        self.cvar_lookup("%RET").ok_or(format!(
            "Missing return value for one or more functions."
        ))
    }

    fn bl_eval_impl_<const IS_CNST: bool>(
        &self, 
        bl: &Block<'ast>,
        mut phy_mem: Vec<T>,
    ) -> Result<(usize, Vec<T>), String> {
        if IS_CNST {
            debug!("Const block: ");
            let _ = &bl.pretty();
        } else {
            debug!("Block: ");
            let _ = &bl.pretty();
        }

        for s in &bl.instructions {
            match s {
                BlockContent::MemPush((var, offset)) => {
                    let sp_t = self.cvar_lookup("%SP").ok_or(format!("Push to %PHY failed: %SP is uninitialized."))?;
                    let sp = self.t_to_usize(sp_t)?;
                    if sp + offset != phy_mem.len() {
                        return Err(format!("Error processing %PHY push: index {sp} + {offset} does not match with stack size."));
                    } else {
                        let e = self.cvar_lookup(&var).ok_or(format!("Push to %PHY failed: pushing an out-of-scope variable."))?;
                        phy_mem.push(e);
                    }
                }
                BlockContent::MemPop((var, offset)) => {
                    let bp_t = self.cvar_lookup("%BP").ok_or(format!("Pop from %PHY failed: %BP is uninitialized."))?;
                    let bp = self.t_to_usize(bp_t)?;
                    if bp + offset >= phy_mem.len() {
                        return Err(format!("Error processing %PHY pop: index out of bound."));
                    } else {
                        let t = phy_mem[bp + offset].clone();
                        self.cvar_assign(&var, t)?;
                    }              
                }
                BlockContent::Stmt(Statement::Return(_)) => {
                    return Err(format!("Blocks should not contain return statements."));
                }
                // %PHY should never appear in an assertion statement
                BlockContent::Stmt(Statement::Assertion(e)) => {
                    match self.expr_impl_::<true>(&e.expression).and_then(|v| {
                        const_bool(v)
                            .ok_or_else(|| "interpreting expr as const bool failed".to_string())
                    }) {
                        Ok(true) => {},
                        Ok(false) => return Err(format!(
                            "Const assert failed: {} at\n{}",
                            e.message
                                .as_ref()
                                .map(|m| m.value.as_ref())
                                .unwrap_or("(no error message given)"),
                            span_to_string(e.expression.span()),
                        )),
                        Err(err) if IS_CNST => return Err(format!(
                            "Const assert expression eval failed {} at\n{}",
                            err,
                            span_to_string(e.expression.span()),
                        )),
                        _ => {
                            let b = bool(self.expr_impl_::<IS_CNST>(&e.expression)?)?;
                            self.assert(b);
                        }
                    }
                }
                BlockContent::Stmt(Statement::Iteration(_)) => {
                    return Err(format!("Blocks should not contain iteration statements."));
                }
                BlockContent::Stmt(Statement::Definition(d)) => {
                    // XXX(unimpl) multi-assignment unimplemented
                    assert!(d.lhs.len() <= 1);

                    self.set_lhs_ty_defn::<IS_CNST>(d)?;
                    let e = self.expr_impl_::<IS_CNST>(&d.expression)?;
    
                    if let Some(l) = d.lhs.first() {
                        match l {
                            TypedIdentifierOrAssignee::Assignee(l) => {
                                let strict = match &d.expression {
                                    Expression::Unary(u) => {
                                        matches!(&u.op, UnaryOperator::Strict(_))
                                    }
                                    _ => false,
                                };
                                self.assign_impl_::<IS_CNST>(&l.id.value, &l.accesses[..], e, strict)?;
                            }
                            TypedIdentifierOrAssignee::TypedIdentifier(l) => {
                                let decl_ty = self.type_impl_::<IS_CNST>(&l.ty)?;
                                let ty = e.type_();
                                if &decl_ty != ty {
                                    return Err(format!(
                                        "Assignment type mismatch: {} annotated vs {} actual",
                                        decl_ty, ty,
                                    ));
                                }
                                self.declare_init_impl_::<IS_CNST>(
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
            }
        };

        match &bl.terminator {
            BlockTerminator::Transition(t) => {
                match self.expr_impl_::<true>(&t.cond).ok().and_then(const_bool) {
                    Some(true) => Ok((t.tblock, phy_mem)), 
                    Some(false) => Ok((t.fblock, phy_mem)),
                    _ => Err("block transition condition not const bool".to_string()),
                }
            }
            BlockTerminator::Coda(nb) => Ok((*nb, phy_mem))
        }
    }
}
