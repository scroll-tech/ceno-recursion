use zokrates_pest_ast as ast;
use crate::front::zsharp::ZGen;
use crate::front::zsharp::debug;
use crate::front::zsharp::PathBuf;
use pest::Span;

fn get_type_span(ty: &ast::Type) -> String {
    match ty {
        ast::Type::Basic(ast::BasicType::Field(t)) => { format!("{}", t.span.as_str()) }
        ast::Type::Basic(ast::BasicType::Boolean(t)) => { format!("{}", t.span.as_str()) }
        ast::Type::Basic(ast::BasicType::U8(t)) => { format!("{}", t.span.as_str()) }
        ast::Type::Basic(ast::BasicType::U16(t)) => { format!("{}", t.span.as_str()) }
        ast::Type::Basic(ast::BasicType::U32(t)) => { format!("{}", t.span.as_str()) }
        ast::Type::Basic(ast::BasicType::U64(t)) => { format!("{}", t.span.as_str()) }
        ast::Type::Struct(t) => { format!("{}", t.span.as_str()) }
        ast::Type::Array(t) => { format!("{}", t.span.as_str()) }
    }
}

fn new_block(mut blks: B) -> B {
    // Create new Block
    blks.blocks.push(Vec::new());
    blks.spans.push(Vec::new());
    blks.bl_len += 1;
    // Assert B@
    let new_span = format!("assert(B@ = {})", (blks.bl_len - 1).to_string());
    let check_stmt = ast::Statement::Assertion(ast::AssertionStatement {
        expression: ast::Expression::Binary(ast::BinaryExpression {
            op: ast::BinaryOperator::Eq,
            left: Box::new(ast::Expression::Identifier(ast::IdentifierExpression {
                value: "B@".to_string(),
                span: Span::new("", 0, 0).unwrap()
            })),
            right: Box::new(ast::Expression::Literal(ast::LiteralExpression::HexLiteral(ast::HexLiteralExpression {
                // TODO: Where do I put the actual number???
                value: ast::HexNumberExpression::U32( ast::U32NumberExpression{
                    value: format!("{:X}", blks.bl_len - 1),
                    span: Span::new("", 0, 0).unwrap()
                }),
                span: Span::new("", 0, 0).unwrap()
            }))),
            span: Span::new("", 0, 0).unwrap()
        }),
        message: None,
        span: Span::new("", 0, 0).unwrap()
    });
    blks.blocks[blks.bl_len - 1].push(check_stmt);
    blks.spans[blks.bl_len - 1].push(new_span);
    blks
}

fn transition_block<'ast>(mut blks: B<'ast>, old_state: usize, new_state: usize, ident: ast::IdentifierExpression<'ast>, condition: ast::Expression<'ast>) -> B<'ast> {
    let new_span = format!("B@ = if {} < {} then {} else {} fi", ident.span.as_str().clone(), condition.span().as_str().clone(), (old_state + 1).to_string(), (new_state + 1).to_string());
    let trans_stmt = ast::Statement::Definition(ast::DefinitionStatement {
        lhs: vec![ast::TypedIdentifierOrAssignee::Assignee(ast::Assignee {
            id: ast::IdentifierExpression {
                value: "B@".to_string(),
                span: Span::new("", 0, 0).unwrap()
            },
            accesses: Vec::new(),
            span: Span::new("", 0, 0).unwrap()
        })],
        expression: ast::Expression::Ternary(ast::TernaryExpression {
            first: Box::new(ast::Expression::Binary(ast::BinaryExpression {
                op: ast::BinaryOperator::Lt,
                left: Box::new(ast::Expression::Identifier(ident.clone())),
                right: Box::new(condition.clone()),
                span: Span::new("", 0, 0).unwrap()
            })),
            second: Box::new(ast::Expression::Literal(ast::LiteralExpression::HexLiteral(ast::HexLiteralExpression {
                // TODO: Where do I put the actual number???
                value: ast::HexNumberExpression::U32( ast::U32NumberExpression{
                    value: format!("{:X}", old_state + 1),
                    span: Span::new("", 0, 0).unwrap()
                }),
                span: Span::new("", 0, 0).unwrap()
            }))),
            third: Box::new(ast::Expression::Literal(ast::LiteralExpression::HexLiteral(ast::HexLiteralExpression {
                // TODO: Where do I put the actual number???
                value: ast::HexNumberExpression::U32( ast::U32NumberExpression{
                    value: format!("{:X}", new_state + 1),
                    span: Span::new("", 0, 0).unwrap()
                }),
                span: Span::new("", 0, 0).unwrap()
            }))),
            span: Span::new("", 0, 0).unwrap()
        }),
        span: Span::new("", 0, 0).unwrap()
    });
    blks.blocks[old_state].push(trans_stmt.clone());
    blks.spans[old_state].push(new_span.clone());
    blks.blocks[new_state].push(trans_stmt);
    blks.spans[new_state].push(new_span);
    blks
}

fn terminal_block(mut blks: B) -> B {
    let new_span = format!("B@ = {}", blks.bl_len.to_string());
    let assign_stmt = ast::Statement::Definition(ast::DefinitionStatement {
        lhs: vec![ast::TypedIdentifierOrAssignee::Assignee(ast::Assignee {
            id: ast::IdentifierExpression {
                value: "B@".to_string(),
                span: Span::new("", 0, 0).unwrap()
            },
            accesses: Vec::new(),
            span: Span::new("", 0, 0).unwrap()
        })],
        expression: ast::Expression::Literal(ast::LiteralExpression::HexLiteral(ast::HexLiteralExpression {
                value: ast::HexNumberExpression::U32( ast::U32NumberExpression{
                    value: format!("{:X}", blks.bl_len),
                    span: Span::new("", 0, 0).unwrap()
                }),
                span: Span::new("", 0, 0).unwrap()
            })),
        span: Span::new("", 0, 0).unwrap()
    });
    blks.blocks[blks.bl_len - 1].push(assign_stmt);
    blks.spans[blks.bl_len - 1].push(new_span);
    blks
}

pub struct B<'ast> {
    blocks: Vec<Vec<ast::Statement<'ast>>>,
    // Store actual codes for pretty printing
    spans: Vec<Vec<String>>,
    bl_len: usize
}

impl<'ast> B<'ast> {
    fn new() -> Self {
        let input = Self {
            blocks: Vec::new(),
            spans: Vec::new(),
            bl_len: 0
        };
        input
    }

    pub fn pretty(&self) {
        for i in 0..self.bl_len {
            println!("\nBlock {}:", i);
            for j in &self.spans[i] {
                println!("{}", j);
            }
        }
    }
}

impl<'ast> ZGen<'ast> {
    pub fn bl_const_entry_fn(&'ast self, n: &str) -> B<'ast> {
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
    ) -> Result<B, String> {
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

        let mut blks = B::new();
        // Check B@ is at initial block
        blks = new_block(blks);
        // Iterate through Stmts
        for s in &f.statements {
            blks = self.bl_stmt_impl_::<IS_CNST>(blks, s)?;
        }
        // Assign B@ to termination block
        blks = terminal_block(blks);

        Ok(blks)
    }

    fn bl_stmt_impl_<const IS_CNST: bool>(&'ast self, mut blks: B<'ast>, s: &'ast ast::Statement<'ast>) -> Result<B, String> {
        if IS_CNST {
            debug!("Const stmt: {}", s.span().as_str());
        } else {
            debug!("Stmt: {}", s.span().as_str());
        }

        match s {
            ast::Statement::Return(_) => {
                blks.blocks[blks.bl_len - 1].push(s.clone());
                blks.spans[blks.bl_len - 1].push(s.span().as_str().to_owned().clone());
                Ok(blks)
            }
            ast::Statement::Assertion(_) => {
                blks.blocks[blks.bl_len - 1].push(s.clone());
                Ok(blks)
            }
            ast::Statement::Iteration(it) => {
                let old_state = blks.bl_len - 1;
                // Create and push FROM statement
                let new_span = format!("{} {} = {}", get_type_span(&it.ty), it.index.span.as_str(), it.from.span().as_str());
                let from_stmt = ast::Statement::Definition(ast::DefinitionStatement {
                    lhs: vec![ast::TypedIdentifierOrAssignee::TypedIdentifier(ast::TypedIdentifier {
                        ty: it.ty.clone(),
                        identifier: it.index.clone(),
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    expression: it.from.clone(),
                    span: Span::new("", 0, 0).unwrap()
                });
                blks.blocks[blks.bl_len - 1].push(from_stmt);
                blks.spans[blks.bl_len - 1].push(new_span);
                // Check B@
                blks = new_block(blks);
                // Iterate through Stmts
                for body in &it.statements {
                    blks = self.bl_stmt_impl_::<IS_CNST>(blks, body)?;
                }
                // Create and push STEP statement
                let new_span = format!("{} = {} + 1", it.index.span.as_str(), it.index.span.as_str());
                let step_stmt = ast::Statement::Definition(ast::DefinitionStatement {
                    lhs: vec![ast::TypedIdentifierOrAssignee::Assignee(ast::Assignee {
                        id: it.index.clone(),
                        accesses: Vec::new(),
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    expression: ast::Expression::Binary(ast::BinaryExpression {
                        op: ast::BinaryOperator::Add,
                        left: Box::new(ast::Expression::Identifier(it.index.clone())),
                        right: Box::new(ast::Expression::Literal(ast::LiteralExpression::HexLiteral(ast::HexLiteralExpression {
                            value: ast::HexNumberExpression::U32( ast::U32NumberExpression{
                                value: format!("{:X}", 1),
                                span: Span::new("", 0, 0).unwrap()
                            }),
                            span: Span::new("", 0, 0).unwrap()
                        }))),
                        span: Span::new("", 0, 0).unwrap()
                    }),
                    span: Span::new("", 0, 0).unwrap()
                });
                blks.blocks[blks.bl_len - 1].push(step_stmt);
                blks.spans[blks.bl_len - 1].push(new_span);
                // Create and push TRANSITION statement
                let new_state = blks.bl_len - 1;
                blks = transition_block(blks, old_state, new_state, it.index.clone(), it.to.clone());
                // Check B@
                blks = new_block(blks);
                Ok(blks)
            }
            ast::Statement::Definition(_) => {
                blks.blocks[blks.bl_len - 1].push(s.clone());
                blks.spans[blks.bl_len - 1].push(s.span().as_str().to_owned().clone());
                Ok(blks)
            }
        }
    }
}
