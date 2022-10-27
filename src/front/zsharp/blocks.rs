// TODO: Add type to all the + 1s.

use zokrates_pest_ast as ast;
use crate::front::zsharp::ZGen;
use crate::front::zsharp::debug;
use crate::front::zsharp::PathBuf;
use crate::front::zsharp::pretty;
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
    pub fn bl_const_entry_fn(&'ast self, n: &str) -> Vec<Block<'ast>> {
        debug!("Const entry: {}", n);
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

        self.bl_function_call_impl_::<true>(f_file, f_name)
            .unwrap_or_else(|e| panic!("const_entry_fn failed: {}", e))
    }

    fn bl_function_call_impl_<const IS_CNST: bool>(
        &self,
        f_path: PathBuf,
        f_name: String,
    ) -> Result<Vec<Block>, String> {
        if IS_CNST {
            debug!("Const function call: {} {:?}", f_name, f_path);
        } else {
            debug!("Function call: {} {:?}", f_name, f_path);
        }
        let f = self
            .functions
            .get(&f_path)
            .ok_or_else(|| format!("No file '{:?}' attempting fn call", &f_path))?
            .get(&f_name)
            .ok_or_else(|| format!("No function '{}' attempting fn call", &f_name))?;

        let mut blks = Vec::new();
        let mut blks_len = 0;
        // Create the initial block
        blks.push(Block::new(0));
        blks_len += 1;
        // Iterate through Stmts
        for s in &f.statements {
            (blks, blks_len) = self.bl_stmt_impl_::<IS_CNST>(blks, blks_len, s)?;
        }
        Ok(blks)
    }

    fn bl_stmt_impl_<const IS_CNST: bool>(
        &'ast self, 
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        s: &'ast ast::Statement<'ast>
    ) -> Result<(Vec<Block>, usize), String> {
        if IS_CNST {
            debug!("Const stmt: {}", s.span().as_str());
        } else {
            debug!("Stmt: {}", s.span().as_str());
        }

        match s {
            ast::Statement::Return(_) => {
                blks[blks_len - 1].instructions.push(s.clone());
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
                    (blks, blks_len) = self.bl_stmt_impl_::<IS_CNST>(blks, blks_len, body)?;
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
}
