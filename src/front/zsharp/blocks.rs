// TODO: Add type to all the + 1s.

use log::{debug, warn};

use zokrates_pest_ast as ast;
use crate::front::zsharp::ZGen;
use crate::front::zsharp::PathBuf;
use crate::front::zsharp::pretty;
use crate::front::zsharp::T;
use crate::front::zsharp::Ty;
use crate::front::zsharp::const_bool;
use crate::front::zsharp::span_to_string;
use crate::front::zsharp::bool;
use pest::Span;

fn cond_expr<'ast>(ident: ast::IdentifierExpression<'ast>, condition: ast::Expression<'ast>) -> ast::Expression<'ast> {
    let ce = ast::Expression::Binary(ast::BinaryExpression {
        op: ast::BinaryOperator::Lt,
        left: Box::new(ast::Expression::Identifier(ident.clone())),
        right: Box::new(condition.clone()),
        span: Span::new("", 0, 0).unwrap()
    });
    ce
}

fn ty_to_dec_suffix<'ast>(ty: ast::Type<'ast>) -> ast::DecimalSuffix<'ast> {
    let span = Span::new("", 0, 0).unwrap();
    match ty {
        ast::Type::Basic(ast::BasicType::Field(_)) => { ast::DecimalSuffix::Field(ast::FieldSuffix { span }) }
        ast::Type::Basic(ast::BasicType::U8(_)) => { ast::DecimalSuffix::U8(ast::U8Suffix { span }) }
        ast::Type::Basic(ast::BasicType::U16(_)) => { ast::DecimalSuffix::U16(ast::U16Suffix { span }) }
        ast::Type::Basic(ast::BasicType::U32(_)) => { ast::DecimalSuffix::U32(ast::U32Suffix { span }) }
        ast::Type::Basic(ast::BasicType::U64(_)) => { ast::DecimalSuffix::U64(ast::U64Suffix { span }) }
        _ => { panic!("Type not supported for loop iterator.") }
    }
}

#[derive(Clone)]
pub struct Block<'ast> {
    name: usize,
    instructions: Vec<ast::Statement<'ast>>,
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
    cond: ast::Expression<'ast>,
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
    fn new(cond: ast::Expression<'ast>, tblock: usize, fblock: usize) -> Self {
        let input = Self {
            cond,
            tblock,
            fblock
        };
        input
    }
}

impl<'ast> ZGen<'ast> {
    pub fn bl_gen_const_entry_fn(&'ast self, n: &str) -> Vec<Block<'ast>> {
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

        self.bl_gen_function_call_::<true>(f_file, f_name)
            .unwrap_or_else(|e| panic!("const_entry_fn failed: {}", e))
    }

    // TODO: Error handling in function call
    fn bl_gen_function_call_<const IS_CNST: bool>(
        &self,
        f_path: PathBuf,
        f_name: String,
    ) -> Result<Vec<Block>, String> {
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

        let mut blks = Vec::new();
        let mut blks_len = 0;
        // Create the initial block
        blks.push(Block::new(0));
        blks_len += 1;
        // Iterate through Stmts
        for s in &f.statements {
            (blks, blks_len) = self.bl_gen_stmt_::<IS_CNST>(blks, blks_len, s, ret_ty)?;
        }
        Ok(blks)
    }

    fn bl_gen_stmt_<const IS_CNST: bool>(
        &'ast self, 
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        s: &'ast ast::Statement<'ast>,
        ret_ty: &'ast ast::Type<'ast>
    ) -> Result<(Vec<Block>, usize), String> {
        if IS_CNST {
            debug!("Block Gen Const stmt: {}", s.span().as_str());
        } else {
            debug!("Block Gen Stmt: {}", s.span().as_str());
        }

        match s {
            ast::Statement::Return(r) => {
                let ret_stmt = ast::Statement::Definition(ast::DefinitionStatement {
                    lhs: vec![ast::TypedIdentifierOrAssignee::TypedIdentifier(ast::TypedIdentifier {
                        ty: ret_ty.clone(),
                        identifier: ast::IdentifierExpression {
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
                Ok((blks, blks_len))
            }
            ast::Statement::Assertion(_) => {
                blks[blks_len - 1].instructions.push(s.clone());
                Ok((blks, blks_len))
            }
            ast::Statement::Iteration(it) => {
                let old_state = blks_len - 1;
                // Create and push FROM statement
                let from_stmt = ast::Statement::Definition(ast::DefinitionStatement {
                    lhs: vec![ast::TypedIdentifierOrAssignee::TypedIdentifier(ast::TypedIdentifier {
                        ty: it.ty.clone(),
                        identifier: it.index.clone(),
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    expression: it.from.clone(),
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(from_stmt);
                // Create new Block
                blks.push(Block::new(blks_len));
                blks_len += 1;
                // Iterate through Stmts
                for body in &it.statements {
                    (blks, blks_len) = self.bl_gen_stmt_::<IS_CNST>(blks, blks_len, body, ret_ty)?;
                }
                // Create and push STEP statement
                let step_stmt = ast::Statement::Definition(ast::DefinitionStatement {
                    lhs: vec![ast::TypedIdentifierOrAssignee::Assignee(ast::Assignee {
                        id: it.index.clone(),
                        accesses: Vec::new(),
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    expression: ast::Expression::Binary(ast::BinaryExpression {
                        op: ast::BinaryOperator::Add,
                        left: Box::new(ast::Expression::Identifier(it.index.clone())),
                        right: Box::new(ast::Expression::Literal(ast::LiteralExpression::DecimalLiteral(ast::DecimalLiteralExpression {
                            value: ast::DecimalNumber {
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
                // Create new Block
                blks.push(Block::new(blks_len));
                blks_len += 1;
                Ok((blks, blks_len))
            }
            ast::Statement::Definition(_) => {
                blks[blks_len - 1].instructions.push(s.clone());
                Ok((blks, blks_len))
            }
        }
    }

    pub fn bl_eval_const_entry_fn(&self, entry_bl: usize, bls: &Vec<Block<'ast>>) -> Result<T, String> {
        // We assume that all errors has been handled in bl_gen functions        
        debug!("Block Eval Const entry: {}", entry_bl);
        self.cvar_enter_function();
        self.bl_eval_impl_::<true>(&bls[entry_bl])?;

        // Return value is just the value of the variable called "%RET"
        // Type of return value is checked during assignment
        self.cvar_lookup("RET").ok_or(format!(
            "Missing return value for one or more functions."
        ))
    }

    // TODO: Return the index of the next block
    fn bl_eval_impl_<const IS_CNST: bool>(&self, bl: &Block<'ast>) -> Result<(), String> {
        if IS_CNST {
            debug!("Const block: ");
            let _ = &bl.pretty();
        } else {
            debug!("Block: ");
            let _ = &bl.pretty();
        }

        for s in &bl.instructions {
            match s {
                ast::Statement::Return(r) => {
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
                ast::Statement::Assertion(e) => {
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
                            let b = bool(self.expr_impl_::<false>(&e.expression)?)?;
                            self.assert(b);
                        }
                    }
                }
                ast::Statement::Iteration(i) => {
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
                ast::Statement::Definition(d) => {
                    // XXX(unimpl) multi-assignment unimplemented
                    assert!(d.lhs.len() <= 1);
    
                    self.set_lhs_ty_defn::<IS_CNST>(d)?;
                    let e = self.expr_impl_::<IS_CNST>(&d.expression)?;
    
                    if let Some(l) = d.lhs.first() {
                        match l {
                            ast::TypedIdentifierOrAssignee::Assignee(l) => {
                                let strict = match &d.expression {
                                    ast::Expression::Unary(u) => {
                                        matches!(&u.op, ast::UnaryOperator::Strict(_))
                                    }
                                    _ => false,
                                };
                                self.assign_impl_::<IS_CNST>(&l.id.value, &l.accesses[..], e, strict)?;
                            }
                            ast::TypedIdentifierOrAssignee::TypedIdentifier(l) => {
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

        Ok(())
    }
}
