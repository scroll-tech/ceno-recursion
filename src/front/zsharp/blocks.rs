// TODO: Recursion is not supported.
//       Generics are not supported.
//       If / else statements are not supported.
//       Arrays & structs are not supported.
//       Function within array index?

// Other Cleanups:
//  Cross check edge-case detection with original ZSharp
//  Can we get rid of IS_CNST?
//  Replace `panic!()` with proper `return Err(format!());`

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

        let main_ret = self.bl_gen_function_call_(blks, blks_len, 0, Vec::new(), f_file, f_name)
            .unwrap_or_else(|e| panic!("const_entry_fn failed: {}", e));
        (main_ret.0, main_ret.2, main_ret.3)
    }

    // TODO: Error handling in function call
    // The head block of the function is already created to facilitate any required initialization
    // Return type:
    // Blks, blks_len, entry_blk, exit_blk, stmt_phy_assign, sp_offset
    fn bl_gen_function_call_(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        mut sp_offset: usize,
        args: Vec<Expression<'ast>>, // We do not use &args here because Expressions might be reconstructed
        f_path: PathBuf,
        f_name: String,
    ) -> Result<(Vec<Block>, usize, usize, usize, usize), String> {
        debug!("Block Gen Function call: {} {:?}", f_name, f_path);

        let mut exit_blk = 0;
        let mut stmt_phy_assign = BTreeMap::new();

        let f = self
            .functions
            .get(&f_path)
            .ok_or_else(|| format!("No file '{:?}' attempting fn call", &f_path))?
            .get(&f_name)
            .ok_or_else(|| format!("No function '{}' attempting fn call", &f_name))?;

        if self.stdlib.is_embed(&f_path) {
            // Leave embedded functions in the blocks
            // They will be handled at IR level
        } else {
            // XXX(unimpl) multi-return unimplemented
            assert!(f.returns.len() <= 1);
            if f.generics.len() != 0 {
                return Err(format!("Generics not implemented"));
            }
            if f.parameters.len() != args.len() {
                return Err(format!(
                    "Wrong number of arguments calling {} (got {}, expected {})",
                    &f.id.value,
                    args.len(),
                    f.parameters.len()
                ));
            }

            // XXX(unimpl) multi-return unimplemented
            assert!(f.returns.len() <= 1);
            // Get the return type because we need to convert it into a variable
            let ret_ty = f
                .returns
                .first().ok_or("No return type provided for one or more function")?;

            for (p, a) in f.parameters.clone().into_iter().zip(args) {
                let p_id = p.id.value.clone();
                // Push p to stack if necessary
                (blks, stmt_phy_assign, sp_offset) = self.bl_gen_scoping_(blks, blks_len, &p.id.value, stmt_phy_assign, sp_offset);
                // Assign p to a
                let param_stmt = Statement::Definition(DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                        ty: p.ty,
                        identifier: IdentifierExpression {
                            value: p_id.clone(),
                            span: Span::new("", 0, 0).unwrap()
                        },
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    expression: a.clone(),
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(param_stmt));
            }

            if stmt_phy_assign.len() > 0 {
                (blks, blks_len, sp_offset) = self.bl_gen_enter_scope_(blks, blks_len, sp_offset)?;
            }

            // Use cvar to identify variable scoping for push and pull
            self.cvar_enter_function();

            // Create new Block
            blks.push(Block::new(blks_len));
            blks_len += 1;

            // Add parameters to scope
            for p in f.parameters.clone().into_iter() {
                let p_id = p.id.value.clone();
                let p_ty = self.type_impl_::<true>(&p.ty)?;
                self.decl_impl_::<true>(p_id, &p_ty)?;                
            }

            // Iterate through Stmts
            for s in &f.statements {
                (blks, blks_len, exit_blk, _, sp_offset) = self.bl_gen_stmt_(blks, blks_len, exit_blk, s, ret_ty, sp_offset)?;
            }
            if exit_blk == 0 {
                exit_blk = blks_len;
            }

            self.cvar_exit_function();
            self.maybe_garbage_collect();

            // Create new Block
            blks.push(Block::new(blks_len));
            blks_len += 1;
            
            if stmt_phy_assign.len() > 0 {
                // Exit Scoping
                (blks, blks_len, sp_offset) = self.bl_gen_exit_scope_(blks, blks_len, stmt_phy_assign, sp_offset)?;
            }
        }

        Ok((blks, blks_len, 0, exit_blk, sp_offset))
    }

    // Generate blocks from statements
    // Return value:
    // result[0]: list of blocks generated so far
    // result[1]: length of the generated blocks
    // result[2]: Exit Block of the CURRENT function, will be decided after processing any return statement
    //            0 if undecided, coda block if we are processing 
    // result[3]: variables that need to be POPed after current scope, with their offset to %BP
    //            used by loop statements and potentially if / else statements
    // result[4]: variables that need to be POPed after current function, with their offset to %BP
    //            used by bl_gen_function_call
    // result[5]: offset between value of %SP and the actual size of the physical memory
    fn bl_gen_stmt_(
        &'ast self, 
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        mut exit_blk: usize,
        s: &'ast Statement<'ast>,
        ret_ty: &'ast Type<'ast>,
        mut sp_offset: usize
    ) -> Result<(Vec<Block>, usize, usize, BTreeMap<usize, String>, usize), String> {
        debug!("Block Gen Stmt: {}", s.span().as_str());

        let mut stmt_phy_assign = BTreeMap::new();

        match s {
            Statement::Return(r) => {
                let ret_expr: Expression;
                (blks, blks_len, exit_blk, stmt_phy_assign, sp_offset, ret_expr, _) = 
                    self.bl_gen_expr_(blks, blks_len, exit_blk, &r.expressions[0], stmt_phy_assign, sp_offset, 0)?;
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
                    expression: ret_expr,
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(ret_stmt));

                // Update CODA block
                if exit_blk == 0 {
                    exit_blk = blks_len;
                    // Create new Block
                    blks.push(Block::new(blks_len));
                    blks_len += 1;
                } else {
                    let term = BlockTerminator::Coda(exit_blk);
                    blks[blks_len - 1].terminator = term;
                }

            }
            Statement::Assertion(a) => {
                let asst_expr: Expression;
                (blks, blks_len, exit_blk, stmt_phy_assign, sp_offset, asst_expr, _) = 
                    self.bl_gen_expr_(blks, blks_len, exit_blk, &a.expression, stmt_phy_assign, sp_offset, 0)?;
                let asst_stmt = Statement::Assertion(AssertionStatement {
                    expression: asst_expr,
                    message: a.message.clone(),
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(asst_stmt));
            }
            Statement::Iteration(it) => {
                let mut vars_to_pop = BTreeMap::new();
                let old_state = blks_len - 1;
                // Create and push FROM statement
                let from_expr: Expression;
                (blks, blks_len, exit_blk, stmt_phy_assign, sp_offset, from_expr, _) = 
                    self.bl_gen_expr_(blks, blks_len, exit_blk, &it.from, stmt_phy_assign, sp_offset, 0)?;
                let from_stmt = Statement::Definition(DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                        ty: it.ty.clone(),
                        identifier: it.index.clone(),
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    expression: from_expr,
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(from_stmt));

                // STORE iterator in Physical Mem if has appeared before
                (blks, stmt_phy_assign, sp_offset) = self.bl_gen_scoping_(blks, blks_len, &it.index.value, stmt_phy_assign, sp_offset);
                
                // New Scope
                (blks, blks_len, sp_offset) = self.bl_gen_enter_scope_(blks, blks_len, sp_offset)?;
                let v_name = it.index.value.clone();
                let ty = self.type_impl_::<true>(&it.ty)?;
                self.decl_impl_::<true>(v_name, &ty)?;

                // Create new Block
                blks.push(Block::new(blks_len));
                blks_len += 1;

                let mut var_to_pop;
                // Iterate through Stmts
                for body in &it.statements {
                    (blks, blks_len, exit_blk, var_to_pop, sp_offset) = self.bl_gen_stmt_(blks, blks_len, exit_blk, body, ret_ty, sp_offset)?;
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

                // Create and push TRANSITION statement
                let to_expr: Expression;
                (blks, blks_len, exit_blk, stmt_phy_assign, sp_offset, to_expr, _) = 
                    self.bl_gen_expr_(blks, blks_len, exit_blk, &it.to, stmt_phy_assign, sp_offset, 0)?;
                let new_state = blks_len - 1;
                let term = BlockTerminator::Transition(
                    BlockTransition::new(
                        cond_expr(it.index.clone(), to_expr), 
                        old_state + 1, 
                        new_state + 1
                    )
                );
                blks[new_state].terminator = term.clone();
                blks[old_state].terminator = term;

                // Exit Scoping
                (blks, blks_len, sp_offset) = self.bl_gen_exit_scope_(blks, blks_len, vars_to_pop, sp_offset)?;

                // Create new Block
                blks.push(Block::new(blks_len));
                blks_len += 1;
            }
            Statement::Definition(d) => {
                // XXX(unimpl) multi-assignment unimplemented
                assert!(d.lhs.len() <= 1);

                // Evaluate function calls in expression
                let rhs_expr: Expression;
                (blks, blks_len, exit_blk, stmt_phy_assign, sp_offset, rhs_expr, _) = 
                    self.bl_gen_expr_(blks, blks_len, exit_blk, &d.expression, stmt_phy_assign, sp_offset, 0)?;

                // Handle Scoping change
                self.set_lhs_ty_defn::<true>(d)?;
                let e = self.expr_impl_::<true>(&d.expression)?;
                if let Some(l) = d.lhs.first() {
                    match l {
                        TypedIdentifierOrAssignee::Assignee(l) => {
                            // No scoping if lhs is an assignee, only need to make sure it has appeared before
                            let name = &l.id.value;
                            let _ = self.cvar_lookup(name)
                                    .ok_or_else(|| format!("Assignment failed: no const variable {}", name))?;
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

                            // Scoping change
                            let id = &l.identifier.value;
                            (blks, stmt_phy_assign, sp_offset) = self.bl_gen_scoping_(blks, blks_len, id, stmt_phy_assign, sp_offset);

                            // Add the identifier to current scope
                            self.declare_init_impl_::<true>(
                                id.clone(),
                                decl_ty,
                                e,
                            )?;
                        }
                    }
                } else {
                    warn!("Statement with no LHS!");
                }
                let new_stmt = Statement::Definition(DefinitionStatement {
                    lhs: d.lhs.clone(),
                    expression: rhs_expr,
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(new_stmt));
            }
        }
        Ok((blks, blks_len, exit_blk, stmt_phy_assign, sp_offset))
    }

    // Generate blocks from statements
    // Return value:
    // result[0 ~ 5] follows bl_gen_stmt_
    // result[6]: new_expr reconstructs the expression and converts all function calls to %RET
    // result[7]: func_count, how many function calls has occured in this statement?
    // Since the return value of all function calls are stored in %RET, we need to differentiate them if
    // multiple function calls occur in the same statement
    fn bl_gen_expr_(
        &'ast self, 
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        mut exit_blk: usize,
        e: &'ast Expression<'ast>,
        mut stmt_phy_assign: BTreeMap<usize, String>,
        mut sp_offset: usize,
        mut func_count: usize
    ) -> Result<(Vec<Block>, usize, usize, BTreeMap<usize, String>, usize, Expression, usize), String> {
        debug!("Block Gen Expr: {}", e.span().as_str());

        let mut ret_e = e.clone();

        match e {
            Expression::Ternary(t) => {
                let new_e_first: Expression;
                let new_e_second: Expression;
                let new_e_third: Expression;
                (blks, blks_len, exit_blk, stmt_phy_assign, sp_offset, new_e_first, func_count) = 
                    self.bl_gen_expr_(blks, blks_len, exit_blk, &t.first, stmt_phy_assign, sp_offset, func_count)?;
                (blks, blks_len, exit_blk, stmt_phy_assign, sp_offset, new_e_second, func_count) = 
                    self.bl_gen_expr_(blks, blks_len, exit_blk, &t.second, stmt_phy_assign, sp_offset, func_count)?;
                (blks, blks_len, exit_blk, stmt_phy_assign, sp_offset, new_e_third, func_count) = 
                    self.bl_gen_expr_(blks, blks_len, exit_blk, &t.third, stmt_phy_assign, sp_offset, func_count)?;
                ret_e = Expression::Ternary(TernaryExpression {
                    first: Box::new(new_e_first),
                    second: Box::new(new_e_second),
                    third: Box::new(new_e_third),
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::Binary(b) => {
                let new_e_left: Expression;
                let new_e_right: Expression;
                (blks, blks_len, exit_blk, stmt_phy_assign, sp_offset, new_e_left, func_count) = 
                    self.bl_gen_expr_(blks, blks_len, exit_blk, &b.left, stmt_phy_assign.clone(), sp_offset, func_count)?;
                (blks, blks_len, exit_blk, stmt_phy_assign, sp_offset, new_e_right, func_count) = 
                    self.bl_gen_expr_(blks, blks_len, exit_blk, &b.right, stmt_phy_assign.clone(), sp_offset, func_count)?;
                ret_e = Expression::Binary(BinaryExpression {
                    op: b.op.clone(),
                    left: Box::new(new_e_left),
                    right: Box::new(new_e_right),
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::Unary(u) => {
                let new_e_expr: Expression;
                (blks, blks_len, exit_blk, stmt_phy_assign, sp_offset, new_e_expr, func_count) = 
                    self.bl_gen_expr_(blks, blks_len, exit_blk, &u.expression, stmt_phy_assign.clone(), sp_offset, func_count)?;
                ret_e = Expression::Unary(UnaryExpression {
                    op: u.op.clone(),
                    expression: Box::new(new_e_expr),
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::Postfix(p) => {
                // assume no functions in arrays, etc.
                assert!(!p.accesses.is_empty());
                if let Some(Access::Call(c)) = p.accesses.first() {
                    let (f_path, f_name) = self.deref_import(&p.id.value);
                    // TODO: evalute all arguments to see if they contain additional function calls
                    let mut args: Vec<Expression> = Vec::new();
                    let mut new_expr: Expression;
                    for old_expr in &c.arguments.expressions {
                        (blks, blks_len, exit_blk, stmt_phy_assign, sp_offset, new_expr, func_count) = 
                            self.bl_gen_expr_(blks, blks_len, exit_blk, old_expr, stmt_phy_assign.clone(), sp_offset, func_count)?;
                        args.push(new_expr);                       
                    }
                    // Update %SP and %BP before function call started since we won't know what happens to them
                    (blks, blks_len, sp_offset) = self.bl_gen_enter_scope_(blks, blks_len, sp_offset)?;
                    (blks, blks_len, _, _, sp_offset) =
                        self.bl_gen_function_call_(blks, blks_len, sp_offset, args, f_path.clone(), f_name.clone())?;
                    let ret_ty = self
                    .functions
                    .get(&f_path)
                    .ok_or_else(|| format!("No file '{:?}' attempting fn call", &f_path))?
                    .get(&f_name)
                    .ok_or_else(|| format!("No function '{}' attempting fn call", &f_name))?
                    .returns
                    .first().ok_or("No return type provided for one or more function")?;

                    let update_ret_stmt = Statement::Definition(DefinitionStatement {
                        lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                            ty: ret_ty.clone(),
                            identifier: IdentifierExpression {
                                value: format!("%RET{}", func_count),
                                span: Span::new("", 0, 0).unwrap()
                            },
                            span: Span::new("", 0, 0).unwrap()
                        })],
                        // Assume that we only have ONE return variable
                        expression: Expression::Identifier(IdentifierExpression {
                            value: "%RET".to_string(),
                            span: Span::new("", 0, 0).unwrap()
                        }),
                        span: Span::new("", 0, 0).unwrap()
                    });
                    blks[blks_len - 1].instructions.push(BlockContent::Stmt(update_ret_stmt));
                    
                    // Exit Scoping
                    // We need to do it AFTER %RET has been stored somewhere else to prevent it being overrided
                    // We also need to do it BEFORE some assinging some variable to %RET because otherwise its
                    // value might be overrided again after being assigned to %RET
                    (blks, blks_len, sp_offset) = self.bl_gen_exit_scope_(blks, blks_len, stmt_phy_assign.clone(), sp_offset)?;
                    
                    ret_e = Expression::Identifier(IdentifierExpression {
                        value: format!("%RET{}", func_count),
                        span: Span::new("", 0, 0).unwrap()
                    });
                    func_count += 1;
                } else {
                    panic!("Array and Struct not implemented!")
                };
            }
            Expression::ArrayInitializer(_) => { panic!("Array not supported!"); }
            Expression::InlineStruct(_) => { panic!("Struct not supported!"); }
            Expression::InlineArray(_) => { panic!("Array not supported!"); }
            _ => {}
        }
        Ok((blks, blks_len, exit_blk, stmt_phy_assign, sp_offset, ret_e, func_count))
    }   
    
    // Handle scoping change by pushing old values onto the stack
    // When IS_FUNC_CALL is activated, we don't care about shadowing
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
                // Push %BP onto the stack, pop back as %BP
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

    fn bl_gen_enter_scope_(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        blks_len: usize,
        mut sp_offset: usize
    ) -> Result<(Vec<Block>, usize, usize), String> {
        // New Scoping
        self.enter_scope_impl_::<true>();

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

    fn bl_gen_exit_scope_(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        blks_len: usize,
        stmt_phy_assign: BTreeMap<usize, String>,
        mut sp_offset: usize
    ) -> Result<(Vec<Block>, usize, usize), String> {
        // Exit Scoping
        self.exit_scope_impl_::<true>();

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

        // POP local variables out
        for (addr, var) in stmt_phy_assign.iter().rev() {
            blks[blks_len - 1].instructions.push(BlockContent::MemPop((var.to_string(), *addr)));
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
        let mut phy_mem: Vec<T> = Vec::new();
        while nb != exit_bl {
            self.print_all_vars_in_scope();
            print!("%PHY: [");
            for c in &phy_mem {
                c.pretty(&mut std::io::stdout().lock())
                .expect("error pretty-printing value");
                print!(", ");
            }
            println!("]");
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
                            let b = bool(self.expr_impl_::<true>(&e.expression)?)?;
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

                    self.set_lhs_ty_defn::<true>(d)?;
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
