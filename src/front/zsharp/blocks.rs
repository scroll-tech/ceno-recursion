// TODO: Recursion is not supported.
//       Generics are not supported.
//       Loop breaks are not supported.
//       Arrays & structs are not supported.
//       Function within array index?
//       Multi-file program not supported
//       What would happen if we put function calls in loop to / from?
//       If b@1 is dead, can we avoid pushing-in b@0?
//       Might be a good idea to avoid using physical memory at all here.
//       Can try eliminate ternaries with a constant condition

// Next Step:
//  The logical thing seems to be, for each blocks produce
//      1. An input for every LOAD / STORE
//      2. A set of constraints where each LOAD / STORE is replaced with an assertion
//      3. A sequence of LOAD / STORE in the block
//  The verifier then asks the prover to provide an execution sequence, and produces
//      1. A unique identifier for each block in the execution (e.g. blk_X_occ_Y or exec_X)
//      2. Block transition sequence check (easy if using exec_X, hard if blk_X_occ_Y)
//      3. Memory consistency check (seems like we need to go through the list anyways)
//      4. Set up circuit for each block (???)
//  Q: Wouldn't this make the verifier's cost linear to the execution?

use log::{debug, warn};

use zokrates_pest_ast::*;
use crate::front::zsharp::ZGen;
use crate::front::zsharp::Ty;
use crate::front::zsharp::PathBuf;
use crate::front::zsharp::pretty;
use crate::front::zsharp::prover::ExecState;
use std::collections::HashMap;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use crate::front::zsharp::*;


fn cond_expr<'ast>(ident: IdentifierExpression<'ast>, condition: Expression<'ast>) -> Expression<'ast> {
    let ce = Expression::Binary(BinaryExpression {
        op: BinaryOperator::Lt,
        left: Box::new(Expression::Identifier(ident.clone())),
        right: Box::new(condition.clone()),
        span: Span::new("", 0, 0).unwrap()
    });
    ce
}

fn ty_to_dec_suffix<'ast>(ty: &Type<'ast>) -> DecimalSuffix<'ast> {
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

pub fn ty_to_type<'ast>(ty: &Ty) -> Result<Type<'ast>, String> {
    match ty {
        Ty::Uint(8) => Ok(Type::Basic(BasicType::U8(U8Type {
            span: Span::new("", 0, 0).unwrap()
        }))),
        Ty::Uint(16) => Ok(Type::Basic(BasicType::U16(U16Type {
            span: Span::new("", 0, 0).unwrap()
        }))),
        Ty::Uint(32) => Ok(Type::Basic(BasicType::U32(U32Type {
            span: Span::new("", 0, 0).unwrap()
        }))),
        Ty::Uint(64) => Ok(Type::Basic(BasicType::U64(U64Type {
            span: Span::new("", 0, 0).unwrap()
        }))),
        Ty::Bool => Ok(Type::Basic(BasicType::Boolean(BooleanType {
            span: Span::new("", 0, 0).unwrap()
        }))),
        Ty::Field => Ok(Type::Basic(BasicType::Field(FieldType {
            span: Span::new("", 0, 0).unwrap()
        }))),
        _ => Err(format!("Type not supported!"))
    }
}

pub fn bl_coda<'ast>(nb: NextBlock) -> Expression<'ast> {
    match nb {
        NextBlock::Label(val) => Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
            value: DecimalNumber {
                value: format!("{}", val),
                span: Span::new("", 0, 0).unwrap()
            },
            suffix: Some(ty_to_dec_suffix(&Type::Basic(BasicType::Field(FieldType {
                span: Span::new("", 0, 0).unwrap()
            })))),
            span: Span::new("", 0, 0).unwrap()
        })),
        NextBlock::Rp => Expression::Identifier(IdentifierExpression {
            value: "%RP".to_string(),
            span: Span::new("", 0, 0).unwrap()
        })
    }
}

pub fn bl_trans<'ast>(cond: Expression<'ast>, tval: NextBlock, fval: NextBlock) -> Expression<'ast> {
    Expression::Ternary(TernaryExpression {
        first: Box::new(cond),
        second: Box::new(bl_coda(tval)),
        third: Box::new(bl_coda(fval)),
        span: Span::new("", 0, 0).unwrap()
    })
}

// Generate the statement: %SP = %SP + sp_offset
fn bl_gen_update_sp<'ast>(sp_offset: usize) -> Statement<'ast> {
    let sp_update_stmt = Statement::Definition(DefinitionStatement {
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
    sp_update_stmt   
}

// #[derive(Clone)]
pub struct Block<'ast> {
    pub name: usize,
    pub inputs: Vec<(String, Option<Ty>)>,
    pub outputs: Vec<(String, Option<Ty>)>,
    pub instructions: Vec<BlockContent<'ast>>,
    pub terminator: BlockTerminator<'ast>
}

#[derive(Clone)]
pub enum BlockContent<'ast> {
    MemPush((String, Ty, usize)), // %PHY[%SP + offset] = id
    MemPop((String, Ty, usize)),  // id = %PHY[%BP + offset]
    Stmt(Statement<'ast>) // other statements
}

#[derive(Clone)]
// Coda is the number of total types of blocks
pub enum BlockTerminator<'ast> {
    Transition(Expression<'ast>), // Expression that should be evaluated to either a const int or "%RP"
    FuncCall(String), // Placeholders before blocks corresponding to each function has been determined
    ProgTerm // The program terminates
}

#[derive(Clone, PartialEq)]
// The next block either has a usize label or is pointed by %RP
// Used to construct Block Transition
pub enum NextBlock {
    Label(usize),
    Rp
}

impl<'ast> Block<'ast> {
    pub fn new(name: usize) -> Self {
        let input = Self {
            name,
            inputs: Vec::new(),
            outputs: Vec::new(),
            instructions: Vec::new(),
            terminator: BlockTerminator::Transition(bl_coda(NextBlock::Label(name + 1)))
        };
        input
    }

    pub fn clone(name: usize, old_bl: &Block<'ast>) -> Self {
        let input = Self {
            name,
            inputs: old_bl.inputs.clone(),
            outputs: old_bl.outputs.clone(),
            instructions: old_bl.instructions.clone(),
            terminator: old_bl.terminator.clone()
        };
        input
    }

    pub fn pretty(&self) {
        println!("\nBlock {}:", self.name);
        println!("Inputs:");
        for i in &self.inputs {
            let (name, ty) = i;
            if let Some(x) = ty {
                println!("    {}: {}", name, x);
            }
        }
        println!("Outputs:");
        for i in &self.outputs {
            let (name, ty) = i;
            if let Some(x) = ty {
                println!("    {}: {}", name, x);
            }
        }
        println!("Instructions:");
        for c in &self.instructions {
            match c {
                BlockContent::MemPush((id, ty, offset)) => { println!("    %PHY[%SP + {offset}] = {id} <{ty}>") }
                BlockContent::MemPop((id, ty, offset)) => { println!("    {ty} {id} = %PHY[%BP + {offset}]") }
                BlockContent::Stmt(s) => { pretty::pretty_stmt(1, &s); }
            }
        }
        match &self.terminator {
            BlockTerminator::Transition(e) => {
                print!("Transition: ");
                pretty::pretty_expr::<true>(e);
            }
            BlockTerminator::FuncCall(fc) => {
                print!("Transition: -> function call on {}.", fc);
            }
            BlockTerminator::ProgTerm => {
                print!("Program terminates.")
            }
        }
    }

    pub fn contains_input(&self, input: &str) -> bool {
        for i in &self.inputs {
            if i.0 == input.to_string() {
                return true;
            }
        }
        return false;
    }

    pub fn contains_output(&self, output: &str) -> bool {
        for i in &self.outputs {
            if i.0 == output.to_string() {
                return true;
            }
        }
        return false;
    }
}

// Given a variable, unroll its scoping according to var_scope_info
// Separate the cases into whether we are declaring the variable,
// assignment is NOT a declaration
fn bl_gen_unroll_scope<const IS_DECL: bool>(
    var: String, 
    mut var_scope_info: HashMap<String, (usize, bool)>
) -> Result<(String, HashMap<String, (usize, bool)>), String> {
    if var.chars().nth(0).unwrap() == '%' {
        return Ok((var, var_scope_info));
    }
    let new_var: String;
    if !var_scope_info.contains_key(&var) {
        if !IS_DECL {
            return Err(format!("Variable {} referenced before definition in bl_gen_unroll_scope!", var));
        } else {
            var_scope_info.insert(var.clone(), (0, false));
            new_var = format!("{}@0", var);
        }
    } else {
        let (mut scope, need_push) = var_scope_info.get(&var).unwrap();
        if *need_push && IS_DECL {
            scope += 1;
            var_scope_info.insert(var.clone(), (scope, false));
            new_var = format!("{}@{}", var.clone(), scope);                
        } else {
            new_var = format!("{}@{}", var, scope);
        }
    }
    return Ok((new_var, var_scope_info));
}

impl<'ast> ZGen<'ast> {

    fn cvar_lookup_type(&self, name: &str) -> Option<Ty> {
        match name {
            "%BP" => Some(Ty::Field),
            "%SP" => Some(Ty::Field),
            "%RP" => Some(Ty::Field),
            _ => Some(self.cvar_lookup(name)?.ty)
        }
    }

    // Returns blocks, block_size, and arguments and their types
    pub fn bl_gen_entry_fn(&'ast self, n: &str) -> (Vec<Block<'ast>>, usize, Vec<(String, Ty)>) {
        debug!("Block Gen entry: {}", n);

        let (f_file, f_name) = self.deref_import(n);
        if let Some(f) = self.functions.get(&f_file).and_then(|m| m.get(&f_name)) {
            if !f.generics.is_empty() {
                panic!("const_entry_fn cannot be called on a generic function")
            }
        } else {
            panic!(
                "No function '{:?}//{}' attempting const_entry_fn",
                &f_file, &f_name
            );
        }

        // Blocks for main function
        let mut blks = Vec::new();
        let mut blks_len = 0;
        // Create the initial block
        blks.push(Block::new(0));
        blks_len += 1;
        // Initialize %RP
        let rp_init_stmt = Statement::Definition(DefinitionStatement {
            lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                ty: Type::Basic(BasicType::Field(FieldType {
                    span: Span::new("", 0, 0).unwrap()
                })),
                identifier: IdentifierExpression {
                    value: "%RP".to_string(),
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
        blks[blks_len - 1].instructions.push(BlockContent::Stmt(rp_init_stmt));
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
        blks[blks_len - 1].instructions.push(BlockContent::Stmt(bp_init_stmt));

        let inputs: Vec<(String, Ty)>;
        (blks, blks_len, inputs) = self.bl_gen_function_init_::<true>(blks, blks_len, f_file.clone(), f_name)
            .unwrap_or_else(|e| panic!("const_entry_fn failed: {}", e));

        // Create a mapping from each function name to the beginning of their blocks
        let mut func_blk_map = BTreeMap::new();
        func_blk_map.insert("main".to_string(), 0);
        // Generate blocks for other functions
        for decls in &self.asts[&f_file].declarations {
            if let SymbolDeclaration::Function(func) = decls {
                let f_name = func.id.value.clone();
                if f_name != "main".to_string() {
                    if self.functions.get(&f_file).and_then(|m| m.get(&f_name)) == None {
                        panic!(
                            "No function '{:?}//{}' attempting entry_fn",
                            &f_file, &f_name
                        );
                    }
                    func_blk_map.insert(f_name.clone(), blks_len);
                    (blks, blks_len, _) = self.bl_gen_function_init_::<false>(blks, blks_len, f_file.clone(), f_name)
                        .unwrap_or_else(|e| panic!("const_entry_fn failed: {}", e));
                }
            }
        }

        let mut new_blks = Vec::new();
        // Convert all FuncCall to actual Block number
        for mut blk in blks {
            if let BlockTerminator::FuncCall(f_name) = blk.terminator {
                let f_label = func_blk_map.get(&f_name).unwrap();
                blk.terminator = BlockTerminator::Transition(bl_coda(NextBlock::Label(*f_label)));
            }
            new_blks.push(blk);
        }

        (new_blks, 0, inputs)
    }

    // Convert each function to blocks
    // Generic: IS_MAIN determines if we are in the main function, which has two properties:
    //   1. We don't need to push %RP when doing function calls in MAIN, since %RP is undefined
    //   2. We don't update the exit block of MAIN to %RP
    //   3. We don't need to handle scoping when hitting `return` in MAIN
    // Return type:
    // Blks, blks_len
    fn bl_gen_function_init_<const IS_MAIN: bool>(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        f_path: PathBuf,
        f_name: String,
    ) -> Result<(Vec<Block>, usize, Vec<(String, Ty)>), String> {
        debug!("Block Gen Function init: {} {:?}", f_name, f_path);

        let f = self
            .functions
            .get(&f_path)
            .ok_or_else(|| format!("No file '{:?}' attempting fn call", &f_path))?
            .get(&f_name)
            .ok_or_else(|| format!("No function '{}' attempting fn call", &f_name))?;

        let mut inputs: Vec<(String, Ty)> = Vec::new();

        if self.stdlib.is_embed(&f_path) {
            // Leave embedded functions in the blocks
            // They will be handled at IR level
        } else {
            // XXX(unimpl) multi-return unimplemented
            assert!(f.returns.len() <= 1);
            if f.generics.len() != 0 {
                return Err(format!("Generics not implemented"));
            }

            // Get the return type because we need to convert it into a variable
            let ret_ty = f
                .returns
                .first().ok_or("No return type provided for one or more function")?;

            // Use cvar to identify variable scoping for push and pull
            self.cvar_enter_function();

            // Create new Block
            blks.push(Block::new(blks_len));
            blks_len += 1;

            // Add scoping to parameters and process the scoped parameters
            let mut var_scope_info: HashMap<String, (usize, bool)> = HashMap::new();
            for p in f.parameters.clone().into_iter() {
                let p_id = p.id.value.clone();
                var_scope_info.insert(p_id.clone(), (0, false));
                let p_ty = self.type_impl_::<true>(&p.ty)?;
                self.decl_impl_::<true>(p_id.clone(), &p_ty)?;
                inputs.push((format!("{}@0", p_id), p_ty.clone()));     
            }

            // Since the out-most scope of a function does not have a stack frame,
            // we do not need to keep track of func_phy_assign between its statements
            let mut sp_offset = 0;
            // Iterate through Stmts
            for s in &f.statements {
                (blks, blks_len, _, sp_offset, var_scope_info) = self.bl_gen_stmt_::<IS_MAIN>(blks, blks_len, s, ret_ty, sp_offset, Vec::new(), var_scope_info)?;
            }

            // Set terminator to ProgTerm if in main, point to %RP otherwise
            if IS_MAIN {
                blks[blks_len - 1].terminator = BlockTerminator::ProgTerm;
            } else {
                blks[blks_len - 1].terminator = BlockTerminator::Transition(bl_coda(NextBlock::Rp));
            }

            self.cvar_exit_function();
            self.maybe_garbage_collect();
        }

        Ok((blks, blks_len, inputs))
    }

    // TODO: Error handling in function call
    // The head block of the function is already created to facilitate any required initialization
    // Arguments have already been pre-processed (func-call replacement, scope unrolling)
    // Return type:
    // Blks, blks_len, entry_blk, func_phy_assign, sp_offset, func_count, var_scope_info
    fn bl_gen_function_call_<const IS_MAIN: bool>(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        mut func_phy_assign: Vec<Vec<(usize, String)>>,
        mut sp_offset: usize,
        args: Vec<Expression<'ast>>, // We do not use &args here because Expressions might be reconstructed
        f_path: PathBuf,
        f_name: String,
        func_count: usize,
        mut var_scope_info: HashMap<String, (usize, bool)>
    ) -> Result<(Vec<Block>, usize, usize, Vec<Vec<(usize, String)>>, usize, usize, HashMap<String, (usize, bool)>), String> {
        debug!("Block Gen Function call: {} {:?}", f_name, f_path);

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

            // We can't assign parameters to their respective arguments directly,
            // consider `func foo(a, b)` and we call `foo(b, a)`
            // We would have to assign b to a and a to b, which would be impossible without intermediate variables
            // Better introduce a variable @ARGx for each parameter and optimize later
            let mut arg_count = 0;
            // Assign @ARGx to a
            for (p, a) in f.parameters.clone().into_iter().zip(args) {
                let param_stmt = Statement::Definition(DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                        ty: p.ty,
                        identifier: IdentifierExpression {
                            value: format!("%ARG{}", arg_count),
                            span: Span::new("", 0, 0).unwrap()
                        },
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    expression: a.clone(),
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(param_stmt));
                arg_count += 1;
            }

            // Push all local variables onto the stack
            let mut var_map: BTreeSet<String> = BTreeSet::new();
            if let Some(st) = self.cvars_stack.borrow().last() {
                for var_list in st.iter().rev() {
                    for var in var_list.clone().into_keys() {
                        var_map.insert(var);
                    }
                }
            }
            // Push all %RETx onto the stack
            for ret_count in 0..func_count {
                var_map.insert(format!("%RET{}", ret_count));
            }
            for var in var_map {
                (blks, func_phy_assign, sp_offset, var_scope_info) = self.bl_gen_scoping_::<true>(blks, blks_len, &var, func_phy_assign, sp_offset, var_scope_info)?;
            }

            // Push %RP onto the stack if not in main
            if !IS_MAIN {
                (blks, func_phy_assign, sp_offset, var_scope_info) = self.bl_gen_scoping_::<true>(blks, blks_len, &"%RP".to_string(), func_phy_assign, sp_offset, var_scope_info)?;
            }

            // Update %SP again to finalize the call stack
            // We technically shouldn't need it before %SP will be updated by the next enter_scope,
            // but there's no harm doing it here
            if sp_offset > 0 {
                // %SP = %SP + sp_offset
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_update_sp(sp_offset)));
                sp_offset = 0;
            }
        
            // Assign p@0 to @ARGx
            arg_count = 0;
            for p in f.parameters.clone().into_iter() {
                let p_id = p.id.value.clone();
                let param_stmt = Statement::Definition(DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                        ty: p.ty,
                        identifier: IdentifierExpression {
                            value: format!("{}@0", p_id.clone()),
                            span: Span::new("", 0, 0).unwrap()
                        },
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    expression: Expression::Identifier(IdentifierExpression {
                        value: format!("%ARG{}", arg_count),
                        span: Span::new("", 0, 0).unwrap()
                    }),
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(param_stmt));
                arg_count += 1;
            }

            // %RP has been pushed to stack before function call
            // Set up %RP and block terminator
            let rp_update_stmt = Statement::Definition(DefinitionStatement {
                lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                    ty: Type::Basic(BasicType::Field(FieldType {
                        span: Span::new("", 0, 0).unwrap()
                    })),
                    identifier: IdentifierExpression {
                        value: "%RP".to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    },
                    span: Span::new("", 0, 0).unwrap()
                })],
                expression: Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                    value: DecimalNumber {
                        value: blks_len.to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    },
                    suffix: Some(DecimalSuffix::Field(FieldSuffix {
                        span: Span::new("", 0, 0).unwrap()
                    })),
                    span: Span::new("", 0, 0).unwrap()
                })),
                span: Span::new("", 0, 0).unwrap()
            });
            blks[blks_len - 1].instructions.push(BlockContent::Stmt(rp_update_stmt));            
            let term = BlockTerminator::FuncCall(f_name.clone());
            blks[blks_len - 1].terminator = term;

            // Create new Block
            blks.push(Block::new(blks_len));
            blks_len += 1; 
            
            // Store Return value to a temporary %RETx
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
            // We need to do it AFTER %RET has been stored somewhere else to prevent it from being overrided
            // We also need to do it BEFORE some assigning some variable to %RET because otherwise its
            // value might be overrided again after being assigned to %RET
            (blks, func_phy_assign, sp_offset, var_scope_info) = self.bl_gen_exit_scope_(blks, blks_len, func_phy_assign, sp_offset, var_scope_info)?;
        }

        Ok((blks, blks_len, 0, func_phy_assign, sp_offset, func_count, var_scope_info))
    }

    // Generate blocks from statements
    // Convert all assignments to declaration, they should behave the same since we don't have scoping.
    // Return value:
    // result[0]: list of blocks generated so far
    // result[1]: length of the generated blocks
    // result[2]: Mapping between variables and their address in stack (in term of offset to %BP) for
    //            ALL stack frames of the current function. Each entry represents one scope.
    // result[3]: variables that need to be POPed after current function, with their offset to %BP
    //            used by bl_gen_function_call
    // result[4]: offset between value of %SP and the actual size of the physical memory
    fn bl_gen_stmt_<const IS_MAIN: bool>(
        &'ast self, 
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        s: &'ast Statement<'ast>,
        ret_ty: &'ast Type<'ast>,
        mut sp_offset: usize,
        mut func_phy_assign: Vec<Vec<(usize, String)>>,
        // We want to unroll scoping as we construct the blocks,
        // so we use a HashMap: String -> (usize, bool) to record scoping information for each variable
        // For each variable, usize indicates the number of times it has been defined in previous scopes
        //                    bool indicates whether it has yet to be defined in the current scope
        //                    true ==> for the next definition, we need to increment the usize
        mut var_scope_info: HashMap<String, (usize, bool)>
    ) -> Result<(Vec<Block>, usize, Vec<Vec<(usize, String)>>, usize, HashMap<String, (usize, bool)>), String> {
        debug!("Block Gen Stmt: {}", s.span().as_str());

        match s {
            Statement::Return(r) => {
                let ret_expr: Expression;
                (blks, blks_len, func_phy_assign, sp_offset, var_scope_info, ret_expr, _) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &r.expressions[0], func_phy_assign, sp_offset, 0, var_scope_info)?;
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

                // Handle scope change after return if we are not in MAIN
                if !IS_MAIN {
                    (blks, sp_offset) = self.bl_gen_return_scope_(blks, blks_len, func_phy_assign.clone(), sp_offset)?;
                }

                // Set terminator to ProgTerm if in main, point to %RP otherwise
                if IS_MAIN {
                    blks[blks_len - 1].terminator = BlockTerminator::ProgTerm;
                } else {
                    blks[blks_len - 1].terminator = BlockTerminator::Transition(bl_coda(NextBlock::Rp));
                }

                // Create a dummy block in case there are anything after return
                // Will be eliminated during DBE
                blks.push(Block::new(blks_len));
                blks_len += 1;

            }
            Statement::Assertion(a) => {
                let asst_expr: Expression;
                (blks, blks_len, func_phy_assign, sp_offset, var_scope_info, asst_expr, _) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &a.expression, func_phy_assign, sp_offset, 0, var_scope_info)?;
                let asst_stmt = Statement::Assertion(AssertionStatement {
                    expression: asst_expr,
                    message: a.message.clone(),
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(asst_stmt));
            }
            Statement::Iteration(it) => {
                // Standalone Scope for the Iterator
                (blks, func_phy_assign, sp_offset) = self.bl_gen_enter_scope_(blks, blks_len, func_phy_assign, sp_offset)?;

                // STORE iterator value in Physical Mem if has appeared before                
                (blks, func_phy_assign, sp_offset, var_scope_info) = self.bl_gen_scoping_::<false>(blks, blks_len, &it.index.value, func_phy_assign, sp_offset, var_scope_info)?;

                // Initialize the scoped iterator
                let v_name = it.index.value.clone();
                let ty = self.type_impl_::<true>(&it.ty)?;
                self.decl_impl_::<true>(v_name.clone(), &ty)?;
                let new_v_name: String;
                (new_v_name, var_scope_info) = bl_gen_unroll_scope::<true>(v_name.clone(), var_scope_info)?;

                // Create and push FROM statement
                let from_expr: Expression;
                (blks, blks_len, func_phy_assign, sp_offset, var_scope_info, from_expr, _) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &it.from, func_phy_assign, sp_offset, 0, var_scope_info)?;

                let new_id = IdentifierExpression {
                    value: new_v_name,
                    span: Span::new("", 0, 0).unwrap()
                };

                let from_stmt = Statement::Definition(DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                        ty: it.ty.clone(),
                        identifier: new_id.clone(),
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    expression: from_expr,
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(from_stmt));

                // New Scope AGAIN to deal with any overwrites to the iterator within the loop
                (blks, func_phy_assign, sp_offset) = self.bl_gen_enter_scope_(blks, blks_len, func_phy_assign, sp_offset)?;

                let old_state = blks_len - 1;

                // Create new Block
                blks.push(Block::new(blks_len));
                blks_len += 1;

                // Iterate through Stmts
                for body in &it.statements {
                    (blks, blks_len, func_phy_assign, sp_offset, var_scope_info) = self.bl_gen_stmt_::<IS_MAIN>(blks, blks_len, body, ret_ty, sp_offset, func_phy_assign, var_scope_info)?;
                }

                // Exit scoping to iterator scope
                (blks, func_phy_assign, sp_offset, var_scope_info) = self.bl_gen_exit_scope_(blks, blks_len, func_phy_assign, sp_offset, var_scope_info)?;

                // Create and push STEP statement
                let step_stmt = Statement::Definition(DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                        ty: it.ty.clone(),
                        identifier: new_id.clone(),
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    expression: Expression::Binary(BinaryExpression {
                        op: BinaryOperator::Add,
                        left: Box::new(Expression::Identifier(new_id.clone())),
                        right: Box::new(Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                            value: DecimalNumber {
                                value: "1".to_string(),
                                span: Span::new("", 0, 0).unwrap()
                            },
                            suffix: Some(ty_to_dec_suffix(&it.ty)),
                            span: Span::new("", 0, 0).unwrap()
                        }))),
                        span: Span::new("", 0, 0).unwrap()
                    }),
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(step_stmt));

                // Create and push TRANSITION statement
                let to_expr: Expression;
                (blks, blks_len, func_phy_assign, sp_offset, var_scope_info, to_expr, _) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &it.to, func_phy_assign, sp_offset, 0, var_scope_info)?;
                let new_state = blks_len - 1;
                let term = BlockTerminator::Transition(
                    bl_trans(
                        cond_expr(new_id.clone(), to_expr), 
                        NextBlock::Label(old_state + 1), 
                        NextBlock::Label(new_state + 1)
                    )
                );
                blks[new_state].terminator = term.clone();
                blks[old_state].terminator = term;

                // Create new block
                blks.push(Block::new(blks_len));
                blks_len += 1;

                // Exit scoping again to outside the loop
                (blks, func_phy_assign, sp_offset, var_scope_info) = self.bl_gen_exit_scope_(blks, blks_len, func_phy_assign, sp_offset, var_scope_info)?;
            }
            Statement::Conditional(c) => {
                // Process function calls in the condition
                let cond_expr: Expression;
                (blks, blks_len, func_phy_assign, sp_offset, var_scope_info, cond_expr, _) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &c.condition, func_phy_assign, sp_offset, 0, var_scope_info)?;

                let head_state = blks_len - 1;

                // If statements
                // Enter Scoping
                (blks, func_phy_assign, sp_offset) = self.bl_gen_enter_scope_(blks, blks_len, func_phy_assign, sp_offset)?;
                // Create new Block
                blks.push(Block::new(blks_len));
                blks_len += 1;
                // Iterate through Stmts
                for body in &c.ifbranch {
                    (blks, blks_len, func_phy_assign, sp_offset, var_scope_info) = self.bl_gen_stmt_::<IS_MAIN>(blks, blks_len, body, ret_ty, sp_offset, func_phy_assign, var_scope_info)?;
                }
                // Exit Scoping
                (blks, func_phy_assign, sp_offset, var_scope_info) = self.bl_gen_exit_scope_(blks, blks_len, func_phy_assign, sp_offset, var_scope_info)?;
                let if_tail_state = blks_len - 1;

                // Else statements
                // Enter Scoping
                (blks, func_phy_assign, sp_offset) = self.bl_gen_enter_scope_(blks, blks_len, func_phy_assign, sp_offset)?;
                // Create new Block
                blks.push(Block::new(blks_len));
                blks_len += 1;
                // Iterate through Stmts
                for body in &c.elsebranch {
                    (blks, blks_len, func_phy_assign, sp_offset, var_scope_info) = self.bl_gen_stmt_::<IS_MAIN>(blks, blks_len, body, ret_ty, sp_offset, func_phy_assign, var_scope_info)?;
                }
                // Exit Scoping
                (blks, func_phy_assign, sp_offset, var_scope_info) = self.bl_gen_exit_scope_(blks, blks_len, func_phy_assign, sp_offset, var_scope_info)?;
                let else_tail_state = blks_len - 1;

                // Block Transition
                // Transition of head block is a branch to if or else
                let head_term = BlockTerminator::Transition(
                    bl_trans(
                        cond_expr, 
                        NextBlock::Label(head_state + 1), 
                        NextBlock::Label(if_tail_state + 1)
                    )
                );
                blks[head_state].terminator = head_term;
                // Transition of if block is to the end of tail
                let if_tail_term = BlockTerminator::Transition(bl_coda(NextBlock::Label(else_tail_state + 1)));
                blks[if_tail_state].terminator = if_tail_term;
                // Transition of else block is already correct

                // Create new Block
                blks.push(Block::new(blks_len));
                blks_len += 1;
            }
            Statement::Definition(d) => {
                // XXX(unimpl) multi-assignment unimplemented
                assert!(d.lhs.len() <= 1);

                // Evaluate function calls in expression
                let mut lhs_expr = d.lhs.clone();
                let rhs_expr: Expression;
                (blks, blks_len, func_phy_assign, sp_offset, var_scope_info, rhs_expr, _) =
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &d.expression, func_phy_assign, sp_offset, 0, var_scope_info)?;

                // Handle Scoping change
                self.set_lhs_ty_defn::<true>(d)?;
                let e = self.expr_impl_::<true>(&d.expression)?;
                if let Some(l) = d.lhs.first() {
                    match l {
                        TypedIdentifierOrAssignee::Assignee(l) => {
                            // No scoping change if lhs is an assignee, only need to make sure it has appeared before
                            let new_l: String;
                            (new_l, var_scope_info) = bl_gen_unroll_scope::<false>(l.id.value.clone(), var_scope_info)?;

                            let new_id = IdentifierExpression {
                                value: new_l.clone(),
                                span: Span::new("", 0, 0).unwrap()
                            };

                            // Convert the assignee to a declaration
                            lhs_expr = vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                                ty: ty_to_type(&self.cvar_lookup_type(&l.id.value).ok_or_else(|| format!("Assignment failed: no variable {}", &new_l))?)?,
                                identifier: new_id.clone(),
                                span: Span::new("", 0, 0).unwrap()
                            })];
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
                            (blks, func_phy_assign, sp_offset, var_scope_info) = self.bl_gen_scoping_::<false>(blks, blks_len, id, func_phy_assign, sp_offset, var_scope_info)?;

                            // Unroll scoping on LHS
                            let new_l: String;
                            (new_l, var_scope_info) = bl_gen_unroll_scope::<true>(l.identifier.value.clone(), var_scope_info)?;

                            // Add the identifier to current scope
                            self.declare_init_impl_::<true>(
                                id.clone(),
                                decl_ty.clone(),
                                e,
                            )?;

                            let new_id = IdentifierExpression {
                                value: new_l,
                                span: Span::new("", 0, 0).unwrap()
                            };

                            // Convert the assignee to a declaration
                            lhs_expr = vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                                ty: l.ty.clone(),
                                identifier: new_id.clone(),
                                span: Span::new("", 0, 0).unwrap()
                            })];
                        }
                    }
                } else {
                    warn!("Statement with no LHS!");
                }
                let new_stmt = Statement::Definition(DefinitionStatement {
                    lhs: lhs_expr,
                    expression: rhs_expr,
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(new_stmt));
            }
            Statement::CondStore(_) => { panic!("Conditional store statements unsupported.") }
        }
        Ok((blks, blks_len, func_phy_assign, sp_offset, var_scope_info))
    }

    // Generate blocks from statements
    // Return value:
    // result[0 ~ 4] follows bl_gen_stmt
    // result[5]: new_expr reconstructs the expression, converts all function calls to %RET, and handles scoping
    // result[6]: func_count, how many function calls has occured in this statement?
    // Since the return value of all function calls are stored in %RET, we need to differentiate them if
    // multiple function calls occur in the same statement
    fn bl_gen_expr_<const IS_MAIN: bool>(
        &'ast self, 
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        e: &'ast Expression<'ast>,
        mut func_phy_assign: Vec<Vec<(usize, String)>>,
        mut sp_offset: usize,
        mut func_count: usize,
        mut var_scope_info: HashMap<String, (usize, bool)>
    ) -> Result<(Vec<Block>, usize, Vec<Vec<(usize, String)>>, usize, HashMap<String, (usize, bool)>, Expression, usize), String> {
        debug!("Block Gen Expr: {}", e.span().as_str());

        let mut ret_e = e.clone();

        match e {
            Expression::Ternary(t) => {
                let new_e_first: Expression;
                let new_e_second: Expression;
                let new_e_third: Expression;
                (blks, blks_len, func_phy_assign, sp_offset, var_scope_info, new_e_first, func_count) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &t.first, func_phy_assign, sp_offset, func_count, var_scope_info)?;
                (blks, blks_len, func_phy_assign, sp_offset, var_scope_info, new_e_second, func_count) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &t.second, func_phy_assign, sp_offset, func_count, var_scope_info)?;
                (blks, blks_len, func_phy_assign, sp_offset, var_scope_info, new_e_third, func_count) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &t.third, func_phy_assign, sp_offset, func_count, var_scope_info)?;
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
                (blks, blks_len, func_phy_assign, sp_offset, var_scope_info, new_e_left, func_count) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &b.left, func_phy_assign, sp_offset, func_count, var_scope_info)?;
                (blks, blks_len, func_phy_assign, sp_offset, var_scope_info, new_e_right, func_count) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &b.right, func_phy_assign, sp_offset, func_count, var_scope_info)?;
                ret_e = Expression::Binary(BinaryExpression {
                    op: b.op.clone(),
                    left: Box::new(new_e_left),
                    right: Box::new(new_e_right),
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::Unary(u) => {
                let new_e_expr: Expression;
                (blks, blks_len, func_phy_assign, sp_offset, var_scope_info, new_e_expr, func_count) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &u.expression, func_phy_assign, sp_offset, func_count, var_scope_info)?;
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
                    let mut args: Vec<Expression> = Vec::new();
                    let mut new_expr: Expression;
                    for old_expr in &c.arguments.expressions {
                        (blks, blks_len, func_phy_assign, sp_offset, var_scope_info, new_expr, func_count) = 
                            self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, old_expr, func_phy_assign, sp_offset, func_count, var_scope_info)?;
                        args.push(new_expr);                       
                    }

                    // Update %SP and %BP before function call started since we won't know what happens to them
                    (blks, func_phy_assign, sp_offset) = self.bl_gen_enter_scope_(blks, blks_len, func_phy_assign, sp_offset)?;
 
                    // Do the function call
                    (blks, blks_len, _, func_phy_assign, sp_offset, func_count, var_scope_info) =
                        self.bl_gen_function_call_::<IS_MAIN>(blks, blks_len, func_phy_assign, sp_offset, args, f_path.clone(), f_name.clone(), func_count, var_scope_info)?;

                    ret_e = Expression::Identifier(IdentifierExpression {
                        value: format!("%RET{}", func_count),
                        span: Span::new("", 0, 0).unwrap()
                    });
                    func_count += 1;
                } else {
                    return Err(format!("Array and Struct not implemented!"));
                };
            }
            Expression::Identifier(i) => {
                let new_var: String;
                (new_var, var_scope_info) = bl_gen_unroll_scope::<false>(i.value.clone(), var_scope_info)?;
                ret_e = Expression::Identifier(IdentifierExpression {
                    value: new_var,
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::Literal(_) => {}
            Expression::ArrayInitializer(_) => { return Err(format!("Array not supported!")); }
            Expression::InlineStruct(_) => { return Err(format!("Struct not supported!")); }
            Expression::InlineArray(_) => { return Err(format!("Array not supported!")); }
        }
        Ok((blks, blks_len, func_phy_assign, sp_offset, var_scope_info, ret_e, func_count))
    }

    // Handle scoping change by pushing old values onto the stack
    // When IS_FUNC_CALL is activated, we don't care about shadowing
    fn bl_gen_scoping_<const IS_FUNC_CALL: bool>(
        &'ast self, 
        mut blks: Vec<Block<'ast>>,
        blks_len: usize,
        id: &String,
        mut func_phy_assign: Vec<Vec<(usize, String)>>,
        mut sp_offset: usize,
        mut var_scope_info: HashMap<String, (usize, bool)>
    ) -> Result<(Vec<Block>, Vec<Vec<(usize, String)>>, usize, HashMap<String, (usize, bool)>), String> {
        // We don't care about shadowing
        if !self.cvar_cur_scope_find(id) || IS_FUNC_CALL {
            // If the identifier is used in the previous scopes of the current function,
            // or if it is a variable added by the compiler (always begins with '%'),
            // push the previous value and pop it after current scope ends
            if self.cvar_lookup(id).is_some() || id.chars().nth(0).unwrap() == '%' {
                // Initialize a new stack frame
                if sp_offset == 0 {
                    // push %BP onto STACK
                    blks[blks_len - 1].instructions.push(BlockContent::MemPush(("%BP".to_string(), Ty::Field, sp_offset)));
                    func_phy_assign.last_mut().unwrap_or_else(|| panic!("Pushing into a non-existing scope in func_phy_assign!")).push((sp_offset, "%BP".to_string()));
                    sp_offset += 1;
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
                }
                let mut new_id = id.to_string();
                if id.chars().nth(0).unwrap() != '%' {
                    // Unroll scoping on ID
                    if !var_scope_info.contains_key(&new_id) {
                        panic!("Variable {} referenced before definition in bl_gen_scoping!", new_id);
                    }
                    // ID is now undeclared in the new scope
                    var_scope_info.insert(new_id.clone(), (var_scope_info.get(&new_id).unwrap().0, true));
                    // Actual Unroll
                    new_id = format!("{}@{}", new_id.clone(), var_scope_info.get(&new_id).unwrap().0);
                }
                // Push ID onto stack
                blks[blks_len - 1].instructions.push(BlockContent::MemPush((new_id.clone(), self.cvar_lookup_type(&id).ok_or_else(|| format!("Variable {} referenced before assignment", &new_id))?, sp_offset)));
                // NOTE: we push ID onto func_phy_assign instead of NEW_ID!!!
                func_phy_assign.last_mut().unwrap_or_else(|| panic!("Pushing into a non-existing scope in func_phy_assign!")).push((sp_offset, id.clone()));
                sp_offset += 1;
            }
        }
        Ok((blks, func_phy_assign, sp_offset, var_scope_info))
    }

    fn bl_gen_enter_scope_(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        blks_len: usize,
        mut func_phy_assign: Vec<Vec<(usize, String)>>,
        mut sp_offset: usize
    ) -> Result<(Vec<Block>, Vec<Vec<(usize, String)>>, usize), String> {
        // New Scoping
        self.enter_scope_impl_::<true>();

        // Update %SP if any changes has been made
        if sp_offset > 0 {
            // %SP = %SP + sp_offset
            blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_update_sp(sp_offset)));
            sp_offset = 0;
        }

        // New Stack Frame
        func_phy_assign.push(Vec::new());

        Ok((blks, func_phy_assign, sp_offset))
    }

    fn bl_gen_exit_scope_(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        blks_len: usize,
        mut func_phy_assign: Vec<Vec<(usize, String)>>,
        mut sp_offset: usize,
        mut var_scope_info: HashMap<String, (usize, bool)>
    ) -> Result<(Vec<Block>, Vec<Vec<(usize, String)>>, usize, HashMap<String, (usize, bool)>), String> {
        // Exit Scoping
        self.exit_scope_impl_::<true>();

        // Update %SP and %BP if any changes has been made
        if sp_offset > 0 {
            // %SP = %SP + sp_offset
            blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_update_sp(sp_offset)));
            sp_offset = 0;
        }

        // POP local variables out
        for (addr, var) in func_phy_assign.pop().unwrap_or_else(|| panic!("Popping out a non-existing scope in func_phy_assign!")).iter().rev() {
            let mut new_var = var.to_string();
            if var.chars().nth(0).unwrap() != '%' {
                // Unroll scoping on ID
                if !var_scope_info.contains_key(&new_var) {
                    return Err(format!("Variable {} referenced before definition in bl_gen_exit_scope!", new_var));
                }
                // Set ID to the previous scope IF it has been defined in the current scope
                if !var_scope_info.get(&new_var).unwrap().1 && var_scope_info.get(&new_var).unwrap().0 == 0 {
                    return Err(format!("Variable {} referenced before definition in bl_gen_exit_scope!", new_var))
                } else if !var_scope_info.get(&new_var).unwrap().1 {
                    var_scope_info.insert(new_var.clone(), (var_scope_info.get(&new_var).unwrap().0 - 1, false));
                } else {
                    var_scope_info.insert(new_var.clone(), (var_scope_info.get(&new_var).unwrap().0, false));
                }
                // Actual Unroll
                new_var = format!("{}@{}", new_var, var_scope_info.get(&new_var).unwrap().0);
            }
            blks[blks_len - 1].instructions.push(BlockContent::MemPop((new_var.clone(), self.cvar_lookup_type(&var).ok_or_else(|| format!("Variable {} referenced before assignment", &new_var))?, *addr)));
        }
        Ok((blks, func_phy_assign, sp_offset, var_scope_info))
    }

    // Handle a return statement
    // We need to push out everything in the stack frame of the current function,
    // but we don't change actual scoping since there might be stuff after the `return`
    // Whether the things after return should be eliminated is not dealt with here
    // No need to worry about scoping since we are only popping out %BP
    fn bl_gen_return_scope_(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        blks_len: usize,
        func_phy_assign: Vec<Vec<(usize, String)>>,
        mut sp_offset: usize
    ) -> Result<(Vec<Block>, usize), String> {

        // Update %SP and %BP if any changes has been made
        if sp_offset > 0 {
            // %SP = %SP + sp_offset
            blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_update_sp(sp_offset)));
            sp_offset = 0;
        }

        // POP everything out
        for scope_phy_assign in func_phy_assign.iter().rev() {
            for (addr, var) in scope_phy_assign.iter().rev() {
                // We only need to pop out %BP
                if var.to_string() == "%BP".to_string() {
                    blks[blks_len - 1].instructions.push(BlockContent::MemPop((var.to_string(), self.cvar_lookup_type(&var).ok_or_else(|| format!("Variable {} referenced before assignment", &var))?, *addr)));
                }
            }
        }
        Ok((blks, sp_offset))
    }

    // Convert a list of blocks to circ_ir
    pub fn bls_to_circ(&'ast self, blks: &Vec<Block>) {
        // let phy_mem_id = self.circ_zero_allocate(MEM_SIZE, MEM_ADDR_WIDTH, MEM_VALUE_WIDTH);
        for b in blks {
            self.circ_init_block(&format!("Block_{}", b.name));
            self.bl_to_circ(&b);
        }
    }

    // Convert a block to circ_ir
    pub fn bl_to_circ(&self, b: &Block) {
        let f = format!("Block_{}", b.name);
        // setup stack frame for entry function
        // returns the next block, so return type is Field
        let ret_ty = Some(Ty::Field);
        self.circ_enter_fn(format!("Block_{}", b.name), ret_ty.clone());

        // Inputs of the block
        for (name, ty) in &b.inputs {
            if let Some(x) = ty {
                let r = self.circ_declare_input(
                    &f,
                    name.clone(),
                    x,
                    ZVis::Public,
                    None,
                    true,
                );
                r.unwrap();
            }
        }
        // Outputs of the block
        for (name, ty) in &b.outputs {
            if let Some(x) = ty {
                let r = self.circ_declare_input(
                    &f,
                    name.clone(),
                    x,
                    ZVis::Public,
                    None,
                    true,
                );
                r.unwrap();
            }
        }

        // How many memory operations have we encountered?
        let mut mem_op_count = 0;
        // Iterate over instructions, convert memory accesses into statements and then IR
        for i in &b.instructions {
            match i {
                BlockContent::MemPush((var, ty, offset)) => {
                    // Non-deterministically supply VAL in memory
                    self.circ_declare_input(
                        &f,
                        format!("%mv{}", mem_op_count),
                        ty,
                        ZVis::Public,
                        None,
                        true,
                    ).unwrap();
                    self.circ_declare_input(
                        &f,
                        format!("%ma{}", mem_op_count),
                        ty,
                        ZVis::Public,
                        None,
                        true,
                    ).unwrap();
                    // Assert correctness of value
                    let lhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                        value: var.to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    })).unwrap();
                    let rhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                        value: format!("%mv{}", mem_op_count),
                        span: Span::new("", 0, 0).unwrap()
                    })).unwrap();
                    let b = bool(eq(lhs_t, rhs_t).unwrap()).unwrap();
                    self.assert(b);
                    // Assert correctness of address
                    let lhs_t = self.expr_impl_::<false>(&Expression::Binary(BinaryExpression {
                        op: BinaryOperator::Add,
                        left: Box::new(Expression::Identifier(IdentifierExpression {
                            value: "%w1".to_string(),
                            span: Span::new("", 0, 0).unwrap()
                        })),
                        right: Box::new(Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                            value: DecimalNumber {
                                value: offset.to_string(),
                                span: Span::new("", 0, 0).unwrap()
                            },
                            suffix: Some(DecimalSuffix::Field(FieldSuffix {
                                span: Span::new("", 0, 0).unwrap()
                            })),
                            span: Span::new("", 0, 0).unwrap()
                        }))),
                        span: Span::new("", 0, 0).unwrap()
                    })).unwrap();
                    let rhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                        value: format!("%ma{}", mem_op_count),
                        span: Span::new("", 0, 0).unwrap()
                    })).unwrap();
                    let b = bool(eq(lhs_t, rhs_t).unwrap()).unwrap();
                    self.assert(b);
                    mem_op_count += 1;
                }
                BlockContent::MemPop((var, ty, offset)) => {
                    // Non-deterministically supply ADDR and VAL in memory
                    self.circ_declare_input(
                        &f,
                        format!("%mv{}", mem_op_count),
                        ty,
                        ZVis::Public,
                        None,
                        true,
                    ).unwrap();
                    self.circ_declare_input(
                        &f,
                        format!("%ma{}", mem_op_count),
                        ty,
                        ZVis::Public,
                        None,
                        true,
                    ).unwrap();
                    // Assign POP value to val
                    let e = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                        value: format!("%mv{}", mem_op_count),
                        span: Span::new("", 0, 0).unwrap()
                    })).unwrap();
                    self.declare_init_impl_::<false>(
                        var.clone(),
                        ty.clone(),
                        e,
                    ).unwrap();
                    // Assert correctness of address
                    let lhs_t = self.expr_impl_::<false>(&Expression::Binary(BinaryExpression {
                        op: BinaryOperator::Add,
                        left: Box::new(Expression::Identifier(IdentifierExpression {
                            value: "%w2".to_string(),
                            span: Span::new("", 0, 0).unwrap()
                        })),
                        right: Box::new(Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                            value: DecimalNumber {
                                value: offset.to_string(),
                                span: Span::new("", 0, 0).unwrap()
                            },
                            suffix: Some(DecimalSuffix::Field(FieldSuffix {
                                span: Span::new("", 0, 0).unwrap()
                            })),
                            span: Span::new("", 0, 0).unwrap()
                        }))),
                        span: Span::new("", 0, 0).unwrap()
                    })).unwrap();
                    let rhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                        value: format!("%ma{}", mem_op_count),
                        span: Span::new("", 0, 0).unwrap()
                    })).unwrap();
                    let b = bool(eq(lhs_t, rhs_t).unwrap()).unwrap();
                    self.assert(b);  
                    mem_op_count += 1;  
                }
                BlockContent::Stmt(stmt) => { self.stmt_impl_::<false>(&stmt).unwrap(); }
            }
        }
        
        // Returns block transition
        match &b.terminator {
            BlockTerminator::Transition(e) => {
                let ret = self.expr_impl_::<false>(e).unwrap();
                self.circ_return_(Some(ret)).unwrap();
            }
            BlockTerminator::FuncCall(_) => { panic!("Blocks pending evaluation should not have FuncCall as terminator.") }
            BlockTerminator::ProgTerm => {}
        }

        if let Some(r) = self.circ_exit_fn() {
            match self.mode {
                Mode::Mpc(_) => {
                    let ret_term = r.unwrap_term();
                    let ret_terms = ret_term.terms();
                    self.circ
                        .borrow()
                        .cir_ctx()
                        .cs
                        .borrow_mut()
                        .get_mut(&f)
                        .unwrap()
                        .outputs
                        .extend(ret_terms);
                }
                Mode::Proof => {
                    let ty = ret_ty.as_ref().unwrap();
                    let name = "return".to_owned();
                    let ret_val = r.unwrap_term();
                    let ret_var_val = self
                        .circ_declare_input(&f, name, ty, ZVis::Public, Some(ret_val.clone()), false)
                        .expect("circ_declare return");
                    let ret_eq = eq(ret_val, ret_var_val).unwrap().term;
                    let mut assertions = std::mem::take(&mut *self.assertions.borrow_mut());
                    let to_assert = if assertions.is_empty() {
                        ret_eq
                    } else {
                        assertions.push(ret_eq);
                        term(AND, assertions)
                    };
                    self.circ.borrow_mut().assert(&f, to_assert);
                }
                Mode::Opt => {
                    let ret_term = r.unwrap_term();
                    let ret_terms = ret_term.terms();
                    assert!(
                        ret_terms.len() == 1,
                        "When compiling to optimize, there can only be one output"
                    );
                    let t = ret_terms.into_iter().next().unwrap();
                    let t_sort = check(&t);
                    if !matches!(t_sort, Sort::BitVector(_)) {
                        panic!("Cannot maximize output of type {}", t_sort);
                    }
                    self.circ.borrow().cir_ctx().cs.borrow_mut().get_mut(&f).unwrap().outputs.push(t);
                }
                /*
                Mode::ProofOfHighValue(v) => {
                    let ret_term = r.unwrap_term();
                    let ret_terms = ret_term.terms();
                    assert!(
                        ret_terms.len() == 1,
                        "When compiling to optimize, there can only be one output"
                    );
                    let t = ret_terms.into_iter().next().unwrap();
                    let cmp = match check(&t) {
                        Sort::BitVector(w) => term![BV_UGE; t, bv_lit(v, w)],
                        s => panic!("Cannot maximize output of type {}", s),
                    };
                    self.circ
                        .borrow()
                        .cir_ctx()
                        .cs
                        .borrow_mut()
                        .outputs
                        .push(cmp);
                }
                */
                _ => { panic!("Supported Mode!") }
            }
        }
    }

    fn circ_init_block(&self, f: &str) {
        self.circ
            .borrow()
            .cir_ctx()
            .cs
            .borrow_mut()
            .insert(f.to_string(), Computation::new());
        self.circ
            .borrow()
            .cir_ctx()
            .cs
            .borrow_mut()
            .get_mut(f)
            .unwrap()
            .metadata
            .add_prover_and_verifier();
    }
}

// Compute waste as explained below
// Return values:
// ret[0]: the waste score of the given padding
// ret[1]: set to TRUE if no block is "splitted", i.e. there's no reason to increase padding further
fn compute_waste<const TRADEOFF: usize>(padding: usize, bl_exec_count: &Vec<usize>) -> (usize, bool) {
    let mut waste = 0;
    let mut split = false;
    for i in bl_exec_count {
        let mut count = *i;
        if count > padding {
            split = true;
            while count > padding {
                waste += TRADEOFF;
                count -= padding;
            }
        }
        if count != 0 {
            waste += padding - count;
        }
    }
    return (waste, split);
}

pub fn generate_padding(bl_exec_count: &Vec<usize>) -> usize {    

    // How many dummy inputs would cost the same as "splitting" a block into two?
    // A large tradeoff value corresponds to a high padding value.
    const TRADEOFF: usize = 64;

    // WASTE = # OF BLOCKS SPLITTED * TRADEOFF + # OF DUMMY IMPUTS
    // Start with PADDING = 1 and keep doubling until find the minimum WASTE
    let mut padding = 1;
    let mut waste: usize;
    let mut min_waste = 0;
    let mut best_pad = 0;
    let mut split = true;
    while split {
        (waste, split) = compute_waste::<TRADEOFF>(padding, bl_exec_count);
        if best_pad == 0 || waste < min_waste {
            min_waste = waste;
            best_pad = padding;
        }
        padding *= 2;
    }

    println!("Padding: {}", best_pad);

    best_pad
}

// Append dummy exec states to the list according to padding
pub fn append_dummy_exec_state(
    len: usize,
    bl_exec_count: &Vec<usize>,
    padding: &usize,
    mut bl_exec_state: Vec<ExecState>,
    reg_size: &usize
) -> Vec<ExecState> {
    for i in 0..len {
        let mut count = bl_exec_count[i];
        while count > *padding {
            count -= *padding;
        }
        if count != 0 {
            bl_exec_state.append(&mut vec![ExecState::new_dummy(i, *reg_size); *padding - count]);
        }
    }
    bl_exec_state
}