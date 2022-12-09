// TODO: Recursion is not supported.

use log::{debug, warn};

use zokrates_pest_ast::*;
use crate::front::zsharp::ZGen;
use crate::front::zsharp::PathBuf;
use crate::front::zsharp::pretty;
use crate::front::zsharp::T;
use crate::front::zsharp::Ty;
use crate::front::zsharp::Loc;
use crate::front::zsharp::const_bool;
use crate::front::zsharp::span_to_string;
use crate::front::zsharp::bool;
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
    instructions: Vec<Statement<'ast>>,
    terminator: BlockTerminator<'ast>,
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
        for s in &self.instructions {
            pretty::pretty_stmt(1, &s);
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

    // Generate the stmt: %PHY[%SP + sp_offset] = id
    fn phy_mem_push_stmt(&self, id: String, sp_offset: usize) -> Statement {
        let push_stmt = Statement::Definition(DefinitionStatement {
            lhs: vec![TypedIdentifierOrAssignee::Assignee(Assignee {
                id: IdentifierExpression {
                    value: "%PHY".to_string(),
                    span: Span::new("", 0, 0).unwrap()
                },
                accesses: vec![AssigneeAccess::Select(ArrayAccess {
                    expression: RangeOrExpression::Expression(
                        if sp_offset != 0 {
                            Expression::Binary(BinaryExpression {
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
                                    suffix: Some(ty_to_dec_suffix(Type::Basic(BasicType::U32(U32Type {
                                        span: Span::new("", 0, 0).unwrap()
                                    })))),
                                    span: Span::new("", 0, 0).unwrap()
                                }))),
                                span: Span::new("", 0, 0).unwrap()
                            })
                        } else {
                            Expression::Identifier(IdentifierExpression {
                                value: "%SP".to_string(),
                                span: Span::new("", 0, 0).unwrap()
                            })
                        }
                    ),
                    span: Span::new("", 0, 0).unwrap()
                })],
                span: Span::new("", 0, 0).unwrap()
            })],
            expression: Expression::Identifier(IdentifierExpression {
                value: id,
                span: Span::new("", 0, 0).unwrap()
            }),
            span: Span::new("", 0, 0).unwrap()
        });
        push_stmt
    }

    // Generate the stmt: id = %PHY[%BP + sp_offset]
    fn phy_mem_pop_stmt(&self, id: String, sp_offset: usize) -> Statement {
        let pop_stmt = Statement::Definition(DefinitionStatement {
            lhs: vec![TypedIdentifierOrAssignee::Assignee(Assignee {
                id: IdentifierExpression {
                    value: id,
                    span: Span::new("", 0, 0).unwrap()
                },
                accesses: Vec::new(),
                span: Span::new("", 0, 0).unwrap()
            })],
            expression: Expression::Postfix(PostfixExpression {
                id: IdentifierExpression {
                    value: "%PHY".to_string(),
                    span: Span::new("", 0, 0).unwrap()
                },
                accesses: vec![Access::Select(ArrayAccess {
                    expression: RangeOrExpression::Expression(
                        if sp_offset != 0 {
                            Expression::Binary(BinaryExpression {
                                op: BinaryOperator::Add,
                                left: Box::new(Expression::Identifier(IdentifierExpression {
                                    value: "%BP".to_string(),
                                    span: Span::new("", 0, 0).unwrap()
                                })),
                                right: Box::new(Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                                    value: DecimalNumber {
                                        value: sp_offset.to_string(),
                                        span: Span::new("", 0, 0).unwrap()
                                    },
                                    suffix: Some(ty_to_dec_suffix(Type::Basic(BasicType::U32(U32Type {
                                        span: Span::new("", 0, 0).unwrap()
                                    })))),
                                    span: Span::new("", 0, 0).unwrap()
                                }))),
                                span: Span::new("", 0, 0).unwrap()
                            })
                        } else {
                            Expression::Identifier(IdentifierExpression {
                                value: "%SP".to_string(),
                                span: Span::new("", 0, 0).unwrap()
                            })
                        }
                    ),
                    span: Span::new("", 0, 0).unwrap()
                })],
                span: Span::new("", 0, 0).unwrap()
            }),
            span: Span::new("", 0, 0).unwrap()
        });
        pop_stmt
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
        let init_stmt = Statement::Definition(DefinitionStatement {
            lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                ty: Type::Basic(BasicType::U32(U32Type {
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
                suffix: Some(ty_to_dec_suffix(Type::Basic(BasicType::U32(U32Type {
                    span: Span::new("", 0, 0).unwrap()
                })))),
                span: Span::new("", 0, 0).unwrap()
            })),
            span: Span::new("", 0, 0).unwrap()
        });
        blks[blks_len - 1].instructions.push(init_stmt);
        // Initialize %BP
        let init_stmt = Statement::Definition(DefinitionStatement {
            lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                ty: Type::Basic(BasicType::U32(U32Type {
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
        blks[blks_len - 1].instructions.push(init_stmt);

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
                blks[blks_len - 1].instructions.push(ret_stmt);
            }
            Statement::Assertion(_) => {
                blks[blks_len - 1].instructions.push(s.clone());
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
                blks[blks_len - 1].instructions.push(from_stmt);

                // STORE iterator in Physical Mem if has appeared before
                (blks, stmt_phy_assign, sp_offset) = self.bl_gen_scoping_(blks, blks_len, &it.index.value, stmt_phy_assign, sp_offset);
                // New Scoping
                let v_name = it.index.value.clone();
                let ty = self.type_impl_::<IS_CNST>(&it.ty)?;
                self.enter_scope_impl_::<IS_CNST>();
                self.decl_impl_::<IS_CNST>(v_name, &ty)?;

                // Update %SP and %BP if any changes has been made
                if sp_offset > 0 {
                    // %BP = %SP
                    let bp_stmt = Statement::Definition(DefinitionStatement {
                        lhs: vec![TypedIdentifierOrAssignee::Assignee(Assignee {
                            id: IdentifierExpression {
                                value: "%BP".to_string(),
                                span: Span::new("", 0, 0).unwrap()
                            },
                            accesses: Vec::new(),
                            span: Span::new("", 0, 0).unwrap()
                        })],
                        expression: Expression::Identifier(IdentifierExpression {
                            value: "%SP".to_string(),
                            span: Span::new("", 0, 0).unwrap()
                        }),
                        span: Span::new("", 0, 0).unwrap()
                    });
                    blks[blks_len - 1].instructions.push(bp_stmt);
                    // %SP = %SP + sp_offset
                    let sp_stmt = Statement::Definition(DefinitionStatement {
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
                                suffix: Some(ty_to_dec_suffix(it.ty.clone())),
                                span: Span::new("", 0, 0).unwrap()
                            }))),
                            span: Span::new("", 0, 0).unwrap()
                        }),
                        span: Span::new("", 0, 0).unwrap()
                    });
                    blks[blks_len - 1].instructions.push(sp_stmt);
                    sp_offset = 0
                }

                // Create new Block
                blks.push(Block::new(blks_len));
                blks_len += 1;

                let mut var_to_pop = BTreeMap::new();
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
                blks[blks_len - 1].instructions.push(step_stmt);

                // POP local variables out
                for (addr, var) in vars_to_pop.iter().rev() {
                    let pop_stmt = self.phy_mem_pop_stmt(var.to_string(), *addr);
                    blks[blks_len - 1].instructions.push(pop_stmt);
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
                self.exit_scope_impl_::<IS_CNST>();

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

                blks[blks_len - 1].instructions.push(s.clone());
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
                    let push_stmt = self.phy_mem_push_stmt("%BP".to_string(), sp_offset);
                    stmt_phy_assign.insert(sp_offset, "%BP".to_string());
                    sp_offset += 1;
                    blks[blks_len - 1].instructions.push(push_stmt);
                }
                let push_stmt = self.phy_mem_push_stmt(id.to_string(), sp_offset);
                stmt_phy_assign.insert(sp_offset, id.clone());
                sp_offset += 1;
                blks[blks_len - 1].instructions.push(push_stmt);
            }
        }
        (blks, stmt_phy_assign, sp_offset)
    }

    pub fn bl_eval_const_entry_fn(&self, entry_bl: usize, exit_bl: usize, bls: &Vec<Block<'ast>>) -> Result<T, String> {
        // We assume that all errors has been handled in bl_gen functions        
        debug!("Block Eval Const entry: {}", entry_bl);
        self.cvar_enter_function();
        let mut nb = entry_bl;
        while nb != exit_bl {
            self.print_all_vars_in_scope();
            nb = self.bl_eval_impl_::<true>(&bls[nb])?;
        }

        // Return value is just the value of the variable called "%RET"
        // Type of return value is checked during assignment
        self.cvar_lookup("%RET").ok_or(format!(
            "Missing return value for one or more functions."
        ))
    }

    fn bl_eval_impl_<const IS_CNST: bool>(&self, bl: &Block<'ast>) -> Result<usize, String> {
        if IS_CNST {
            debug!("Const block: ");
            let _ = &bl.pretty();
        } else {
            debug!("Block: ");
            let _ = &bl.pretty();
        }

        for s in &bl.instructions {
            match s {
                Statement::Return(r) => {
                    // XXX(unimpl) multi-return unimplemented
                    assert!(r.expressions.len() <= 1);
                    if let Some(e) = r.expressions.first() {
                        self.set_lhs_ty_ret(r);
                        let ret = self.expr_impl_::<IS_CNST>(e)?;
                        self.ret_impl_::<IS_CNST>(Some(ret)).map_err(|e| format!("{}", e))?;
                    } else {
                        self.ret_impl_::<IS_CNST>(None).map_err(|e| format!("{}", e))?;
                    }
                }
                Statement::Assertion(e) => {
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
                Statement::Iteration(i) => {
                    let ty = self.type_impl_::<IS_CNST>(&i.ty)?;
                    let ival_cons = match ty {
                        Ty::Field => T::new_field,
                        Ty::Uint(8) => T::new_u8,
                        Ty::Uint(16) => T::new_u16,
                        Ty::Uint(32) => T::new_u32,
                        Ty::Uint(64) => T::new_u64,
                        _ => {
                            return Err(format!(
                                "Iteration variable must be Field or Uint, got {:?}",
                                ty
                            ));
                        }
                    };
                    // XXX(rsw) CHECK does this work if the range includes negative numbers?
                    let s = self.const_isize_impl_::<IS_CNST>(&i.from)?;
                    let e = self.const_isize_impl_::<IS_CNST>(&i.to)?;
                    let v_name = i.index.value.clone();
                    self.enter_scope_impl_::<IS_CNST>();
                    self.decl_impl_::<IS_CNST>(v_name, &ty)?;
                    for j in s..e {
                        self.enter_scope_impl_::<IS_CNST>();
                        self.assign_impl_::<IS_CNST>(&i.index.value, &[][..], ival_cons(j), false)?;
                        for s in &i.statements {
                            self.stmt_impl_::<IS_CNST>(s)?;
                        }
                        self.exit_scope_impl_::<IS_CNST>();
                    }
                    self.exit_scope_impl_::<IS_CNST>();
                }
                Statement::Definition(d) => {
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
                    Some(true) => Ok(t.tblock), 
                    Some(false) => Ok(t.fblock),
                    _ => Err("block transition condition not const bool".to_string()),
                }
            }
            BlockTerminator::Coda(nb) => Ok(*nb)
        }
    }
}
