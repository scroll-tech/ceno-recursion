// TODO: Recursion is not supported.
//       Generics are not supported.
//       Loop breaks are not supported.
//       Arrays & structs are not supported.
//       Function within array index?
//       Multi-file program not supported
//       What would happen if we put function calls in loop to / from?
//       Can try eliminate ternaries with a constant condition
//       What would happen if block 0 is a loop to itself? Many analyses would break down!!!

use log::{debug, warn};

use zokrates_pest_ast::*;
use crate::front::zsharp::ZGen;
use crate::front::zsharp::Ty;
use crate::front::zsharp::PathBuf;
use crate::front::zsharp::pretty::*;
use std::collections::HashMap;
use std::collections::BTreeMap;
use std::convert::TryInto;
use crate::front::zsharp::*;

const LOAD: usize = 0;
const STORE: usize = 1;
const DUMMY_LOAD: usize = 2;

fn cond_expr<'ast>(ident: IdentifierExpression<'ast>, condition: Expression<'ast>) -> Expression<'ast> {
    let ce = Expression::Binary(BinaryExpression {
        // op: BinaryOperator::Lt,
        op: BinaryOperator::NotEq,
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
        _ => Err(format!("Type not supported: {:?}", ty))
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

// Generate the statement: var = var + offset
pub fn bl_gen_increment_stmt<'ast>(var: &str, offset: usize) -> Statement<'ast> {
    let sp_update_stmt = Statement::Definition(DefinitionStatement {
        lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
            ty: Type::Basic(BasicType::Field(FieldType {
                span: Span::new("", 0, 0).unwrap()
            })),
            identifier: IdentifierExpression {
                value: var.to_string(),
                span: Span::new("", 0, 0).unwrap()
            },
            span: Span::new("", 0, 0).unwrap()
        })],
        expression: Expression::Binary(BinaryExpression {
            op: BinaryOperator::Add,
            left: Box::new(Expression::Identifier(IdentifierExpression {
                value: var.to_string(),
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
    pub terminator: BlockTerminator<'ast>,
    // The upper bound on the number of times a block is executed within one execution of the function
    pub fn_num_exec_bound: usize,
    // Is this block the head of a while loop? If so, this block cannot be merged with any block before it
    pub is_head_of_while_loop: bool,
    // Number of non-scoping-related memory accesses per each variable type
    pub mem_op_by_ty: BTreeMap<Ty, usize>,
    // Name of the function the block is in
    pub fn_name: String,
    // Depth of the scope of the function
    pub scope: usize
}

#[derive(Clone, PartialEq, Debug)]
pub enum BlockContent<'ast> {
    //       val   type  offset  
    MemPush((String, Ty, usize)), // %PHY[%SP + offset] = val
    MemPop((String, Ty, usize)),  // val = %PHY[%BP + offset]
    //          arr   type  size, assume only one dimensional
    ArrayInit((String, Ty, usize)),   
    //     val_expr         type   arr   id_expr
    Store((Expression<'ast>, Ty, String, Expression<'ast>)), // arr[id] = val
    //    var    type   arr   id_expr
    Load((String, Ty, String, Expression<'ast>)),  // val = arr[id]
    // DummyLoad(Ty),
    // Branch((Expression<'ast>, Vec<BlockContent>, Vec<BlockContent>)),
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
    pub fn new(name: usize, num_exec_bound: usize, fn_name: String, scope: usize) -> Self {
        let input = Self {
            name,
            inputs: Vec::new(),
            outputs: Vec::new(),
            instructions: Vec::new(),
            terminator: BlockTerminator::Transition(bl_coda(NextBlock::Label(name + 1))),
            fn_num_exec_bound: num_exec_bound,
            is_head_of_while_loop: false,
            mem_op_by_ty: BTreeMap::new(),
            fn_name,
            scope
        };
        input
    }

    pub fn clone(name: usize, old_bl: &Block<'ast>) -> Self {
        let input = Self {
            name,
            inputs: old_bl.inputs.clone(),
            outputs: old_bl.outputs.clone(),
            instructions: old_bl.instructions.clone(),
            terminator: old_bl.terminator.clone(),
            fn_num_exec_bound: old_bl.fn_num_exec_bound,
            is_head_of_while_loop: old_bl.is_head_of_while_loop,
            mem_op_by_ty: old_bl.mem_op_by_ty.clone(),
            fn_name: old_bl.fn_name.clone(),
            scope: old_bl.scope
        };
        input
    }

    pub fn get_num_inputs(&self) -> usize {
        let mut count = 0;
        for i in &self.inputs {
            let (_, ty) = i;
            if let Some(_) = ty {
                count += 1;
            }
        }
        return count;
    }

    pub fn pretty(&self) {
        println!("\nBlock {}:", self.name);
        println!("Func: {}, Scope: {}", self.fn_name, self.scope);
        println!("Exec Bound: {}, While Loop: {}, TS Diff: {:?}", self.fn_num_exec_bound, self.is_head_of_while_loop, self.mem_op_by_ty);
        println!("Inputs:");

        for i in &self.inputs {
            let (name, ty) = i;
            if let Some(x) = ty {
                println!("    {}: {}", pretty_name(name), x);
            }
        }
        println!("Outputs:");
        for i in &self.outputs {
            let (name, ty) = i;
            if let Some(x) = ty {
                println!("    {}: {}", pretty_name(name), x);
            }
        }
        println!("Instructions:");
        for c in &self.instructions {
            match c {
                BlockContent::MemPush((val, ty, offset)) => { println!("    %PHY[%SP + {offset}] = {} <{ty}>", pretty_name(val)) }
                BlockContent::MemPop((val, ty, offset)) => { println!("    {ty} {} = %PHY[%BP + {offset}]", pretty_name(val)) }
                BlockContent::ArrayInit((arr, ty, size)) => { println!("    {ty}[{size}] {arr}") }
                BlockContent::Store((val, ty, arr, id)) => { print!("    {arr}["); pretty_expr::<false>(&id); print!("] = "); pretty_expr::<false>(&val); println!(" <{ty}>"); }
                BlockContent::Load((val, ty, arr, id)) => { print!("    {ty} {} = {arr}[", pretty_name(val)); pretty_expr::<false>(&id); println!("]"); }
                BlockContent::Stmt(s) => { pretty_stmt(1, &s); }
            }
        }
        match &self.terminator {
            BlockTerminator::Transition(e) => {
                print!("Transition: ");
                pretty_expr::<true>(e);
            }
            BlockTerminator::FuncCall(fc) => {
                print!("Transition: -> function call on {}.", fc);
            }
            BlockTerminator::ProgTerm => {
                print!("Program terminates.")
            }
        }
    }
}

// All information regarding scoping of every variable
pub struct VarScopeInfo {
    // Every time a variable is overwritten at a new scope, it receives a new version number at the specific depth
    // Use var_version to record the version number of each (var_name, fn_name) at each depth
    // Note: variable depth is how many times the variable has been overwritten, which might be different from the depth of the scope
    var_version: HashMap<(String, String), Vec<usize>>,
    // Use var_stack to track the depth of the variable
    // For each (var_name, fn_name), record its depth and all scopes that it has been defined
    // i.e., (2, (0, 2, 3)) means the current depth is 2 and the variables has been defined in scope 0, 2, 3
    var_stack: HashMap<(String, String), (usize, Vec<usize>)>,
    // Map of arrays to the type of their content
    arr_map: HashMap<String, Ty>,
}

impl VarScopeInfo {
    fn new() -> VarScopeInfo {
        VarScopeInfo {
            var_version: HashMap::new(),
            var_stack: HashMap::new(),
            arr_map: HashMap::new()
        }
    }

    // Declare a variable in a given scope of a given function, return the new variable name
    fn declare_var(&mut self, var_name: &str, fn_name: &str, cur_scope: usize) -> String {
        let name = &(var_name.to_string(), fn_name.to_string());
        match self.var_stack.get(name) {
            Some((depth, stack)) => {
                assert!(stack.len() == 0 || stack[stack.len() - 1] <= cur_scope);
                // If stack[stack.len() - 1] == cur_scope, this is shadowing and we don't need to do anything
                if stack.len() == 0 || stack[stack.len() - 1] < cur_scope {
                    let new_depth = depth + 1;
                    let new_stack = [stack.to_vec(), vec![cur_scope]].concat();
                    let mut version_list = self.var_version.get(name).unwrap().to_vec();
                    if version_list.len() > new_depth {
                        // If the variable has a version at cur_scope, increment it by 1
                        version_list[new_depth] += 1;
                        self.var_version.insert(name.clone(), version_list);
                    } else {
                        // Otherwise, assign version 0 to the new depth
                        // Assert that new_depth is only one-depth higher than the previous highest depth
                        assert_eq!(version_list.len(), new_depth);
                        version_list.push(0);
                        self.var_version.insert(name.clone(), version_list);
                    }
                    self.var_stack.insert(name.clone(), (new_depth, new_stack));
                }
            },
            None => {
                // If the variable is never defined, add variable to var_version and var_stack
                let depth_stack = (0, vec![cur_scope]);
                self.var_stack.insert(name.clone(), depth_stack);
                let version_list = vec![0];
                self.var_version.insert(name.clone(), version_list.to_vec());
            }
        }
        self.reference_var(var_name, fn_name).unwrap()
    }

    // Given a variable, return "<var_name>.<func_name>.<scope>.<version>"
    fn reference_var(&self, var_name: &str, fn_name: &str) -> Result<String, String> {
        let name = &(var_name.to_string(), fn_name.to_string());
        if let Some((depth, _)) = self.var_stack.get(&name) {
            let version = self.var_version.get(&name).unwrap()[*depth];
            Ok(format!("{}.{}.{}.{}", var_name, fn_name, depth, version))
        } else {
            Err(format!("get_var_extended_name failed: variable {} does not exist in function {}", var_name, fn_name))
        }
    }

    // exit the current scope
    fn exit_scope(&mut self, fn_name: &str, cur_scope: usize) {
        // First record all variables that need scope change
        let mut updates = HashMap::new();
        for ((var_name, var_fn_name), (depth, stack)) in &self.var_stack {
            if var_fn_name == fn_name && stack.len() > 0 {
                let var_top_scope = stack[stack.len() - 1];
                assert!(var_top_scope <= cur_scope);
                if var_top_scope == cur_scope {
                    updates.insert((var_name.to_string(), var_fn_name.to_string()), (depth - 1, stack[..stack.len() - 1].to_vec()));
                }
            }
        }
        // Update self.var_stack
        for (name, stack) in updates {
            self.var_stack.insert(name, stack);
        }
    }
}

impl<'ast> ZGen<'ast> {
    fn circ_lookup_type(&self, name: &str) -> Option<Ty> {
        match name {
            "%BP" => Some(Ty::Field),
            "%SP" => Some(Ty::Field),
            "%RP" => Some(Ty::Field),
            _ => match self.circ_get_value(Loc::local(name.to_string())).map_err(|e| format!("{e}")).ok()?
                {
                    Val::Term(t) => Some(t.type_().clone()),
                    _ => None,
                },
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
        blks.push(Block::new(0, 1, f_name.to_string(), 0));
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
                    func_blk_map.insert(f_name.to_string(), blks_len);
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
            let ret_type = f
                .returns
                .first().ok_or("No return type provided for one or more function")?;
            let ret_ty = self.type_impl_::<false>(&ret_type)?;

            // Use cvar to identify variable scoping for push and pull
            self.circ_enter_fn(f_name.to_string(), Some(ret_ty.clone()));

            // Create new Block, initial scope is 0
            blks.push(Block::new(blks_len, 1, f_name.to_string(), 0));
            blks_len += 1;

            // Every time a variable is assigned a value at a specific scope, it receives a new version number
            // Use var_scope_info to record the version number of each (var_name, fn_name) at each scope
            let mut var_scope_info: VarScopeInfo = VarScopeInfo::new();
            for p in f.parameters.clone().into_iter() {
                let p_id = p.id.value.clone();
                var_scope_info.declare_var(&p_id, &f_name, 0);
                let p_ty = self.type_impl_::<false>(&p.ty)?;
                self.decl_impl_::<false>(p_id.clone(), &p_ty)?;
                inputs.push((var_scope_info.reference_var(&p_id, &f_name)?, p_ty.clone()));     
            }

            // Iterate through Stmts
            for s in &f.statements {
                // All statements at function level have scope 0
                (blks, blks_len, var_scope_info) = self.bl_gen_stmt_::<IS_MAIN>(blks, blks_len, s, ret_type, &f_name, var_scope_info, 1, 0)?;
            }

            // Set terminator to ProgTerm if in main, point to %RP otherwise
            if IS_MAIN {
                blks[blks_len - 1].terminator = BlockTerminator::ProgTerm;
            } else {
                blks[blks_len - 1].terminator = BlockTerminator::Transition(bl_coda(NextBlock::Rp));
            }

            self.circ_exit_fn();
            self.maybe_garbage_collect();
        }

        Ok((blks, blks_len, inputs))
    }

    // TODO: Error handling in function call
    // The head block of the function is already created to facilitate any required initialization
    // Arguments have already been pre-processed (func-call replacement, scope unrolling)
    // Return type:
    // Blks, blks_len, entry_blk, func_count
    fn bl_gen_function_call_<const IS_MAIN: bool>(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        args: Vec<Expression<'ast>>, // We do not use &args here because Expressions might be reconstructed
        f_path: PathBuf,
        f_name: String,
        func_count: usize,
        mut var_scope_info: VarScopeInfo
    ) -> Result<(Vec<Block>, usize, usize, VarScopeInfo, usize), String> {
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

            // Enter Scope
            self.enter_scope_impl_::<false>();

            // Push %RP onto the stack if not in main
            if !IS_MAIN {
                // push %BP onto STACK
                blks[blks_len - 1].instructions.push(BlockContent::MemPush(("%BP".to_string(), Ty::Field, 0)));
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
                // Push %RP onto stack
                blks[blks_len - 1].instructions.push(BlockContent::MemPush(("%RP".to_string(), Ty::Field, 1)));
                // %SP = %SP + sp_offset
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_increment_stmt("%SP", 2)));
            }
        
            // Assign p@0 to a
            for (p, a) in f.parameters.clone().into_iter().zip(args) {
                let p_id = p.id.value.clone();
                let param_stmt = Statement::Definition(DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                        ty: p.ty,
                        identifier: IdentifierExpression {
                            value: var_scope_info.declare_var(&p_id, &f_name, 0),
                            span: Span::new("", 0, 0).unwrap()
                        },
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    expression: a.clone(),
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(param_stmt));
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
            let term = BlockTerminator::FuncCall(f_name.to_string());
            blks[blks_len - 1].terminator = term;

            // Exit Function - Create new Block
            // The new block should have the same number of execution bound as the previous block
            // As well as in the same scope of the same function
            let caller_name = blks[blks_len - 1].fn_name.to_string();
            let num_exec_bound = blks[blks_len - 1].fn_num_exec_bound;
            let caller_scope = blks[blks_len - 1].scope;
            blks.push(Block::new(blks_len, num_exec_bound, caller_name.clone(), caller_scope));
            blks_len += 1; 
            
            // Exit scope & POP local variables out
            self.exit_scope_impl_::<false>();
            if !IS_MAIN {
                blks[blks_len - 1].instructions.push(BlockContent::MemPop(("%RP".to_string(), Ty::Field, 1)));
                blks[blks_len - 1].instructions.push(BlockContent::MemPop(("%BP".to_string(), Ty::Field, 0)));
            }

            // Store Return value to a temporary variable "ret@X"
            let ret_ty = self
            .functions
            .get(&f_path)
            .ok_or_else(|| format!("No file '{:?}' attempting fn call", &f_path))?
            .get(&f_name)
            .ok_or_else(|| format!("No function '{}' attempting fn call", &f_name))?
            .returns
            .first().ok_or("No return type provided for one or more function")?;

            let ret_name = format!("ret@{}", func_count);
            self.decl_impl_::<false>(ret_name.clone(), &self.type_impl_::<false>(ret_ty)?)?;
            let ret_extended_name = var_scope_info.declare_var(&ret_name, &caller_name, caller_scope);
            let update_ret_stmt = Statement::Definition(DefinitionStatement {
                lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                    ty: ret_ty.clone(),
                    identifier: IdentifierExpression {
                        value: ret_extended_name,
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
        }

        Ok((blks, blks_len, 0, var_scope_info, func_count))
    }

    // Generate blocks from statements
    // Convert all assignments to declaration, they should behave the same since we don't have scoping.
    // Return value:
    // result[0]: list of blocks generated so far
    // result[1]: length of the generated blocks
    // result[2]: Scoping information of each variable
    fn bl_gen_stmt_<const IS_MAIN: bool>(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        s: &'ast Statement<'ast>,
        ret_ty: &'ast Type<'ast>,
        // function name
        f_name: &str,
        // Records the version number of each (var_name, fn_name) at each scope
        mut var_scope_info: VarScopeInfo,
        // How many times will this statement be executed within the function
        num_exec_bound: usize,
        // What is the current scope?
        mut cur_scope: usize,
    ) -> Result<(Vec<Block>, usize, VarScopeInfo), String> {
        debug!("Block Gen Stmt: {}", s.span().as_str());

        match s {
            Statement::Return(r) => {
                let ret_expr: Expression;
                let array_init_info: Vec<Expression>;
                (blks, blks_len, var_scope_info, ret_expr, _, _, array_init_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &r.expressions[0], f_name, 0, 0, var_scope_info)?;
                if array_init_info.len() > 0 { panic!("Inline array inside return statements not supported!") }
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

                // Set terminator to ProgTerm if in main, point to %RP otherwise
                if IS_MAIN {
                    blks[blks_len - 1].terminator = BlockTerminator::ProgTerm;
                } else {
                    blks[blks_len - 1].terminator = BlockTerminator::Transition(bl_coda(NextBlock::Rp));
                }

                // Create a dummy block in case there are anything after return
                // Will be eliminated during DBE
                blks.push(Block::new(blks_len, num_exec_bound, f_name.to_string(), cur_scope));
                blks_len += 1;

            }
            Statement::Assertion(a) => {
                let asst_expr: Expression;
                let array_init_info: Vec<Expression>;
                (blks, blks_len, var_scope_info, asst_expr, _, _, array_init_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &a.expression, f_name, 0, 0, var_scope_info)?;
                if array_init_info.len() > 0 { panic!("Inline array inside assertion statements not supported!") }
                let asst_stmt = Statement::Assertion(AssertionStatement {
                    expression: asst_expr,
                    message: a.message.clone(),
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(asst_stmt));
            }
            Statement::Iteration(it) => {
                // Standalone Scope for the Iterator
                cur_scope = self.bl_gen_enter_scope_(cur_scope)?;

                // Create new Block for iterator initialization & scoping resolution
                blks.push(Block::new(blks_len, num_exec_bound, f_name.to_string(), cur_scope));
                blks_len += 1;

                // Initialize the scoped iterator
                let v_name = it.index.value.clone();
                let ty = self.type_impl_::<false>(&it.ty)?;
                self.decl_impl_::<false>(v_name.clone(), &ty)?;
                let new_v_name = var_scope_info.declare_var(&v_name, f_name, cur_scope);

                let from_expr: Expression;
                let mut array_init_info: Vec<Expression>;
                (blks, blks_len, var_scope_info, from_expr, _, _, array_init_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &it.from, f_name, 0, 0, var_scope_info)?;
                if array_init_info.len() > 0 { panic!("From expr of for loops cannot be inline array!") }
                let to_expr: Expression;
                (blks, blks_len, var_scope_info, to_expr, _, _, array_init_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &it.to, f_name, 0, 0, var_scope_info)?;
                if array_init_info.len() > 0 { panic!("To expr of for loops cannot be inline array!") }

                // Record the number of iterations of the loop
                // Currently only support from_expr and to_expr being constants
                let loop_num_it = {
                    let from_const = if let Expression::Literal(LiteralExpression::DecimalLiteral(ref dle)) = from_expr {
                        dle.value.value.parse::<usize>().unwrap()
                    } else { panic!("Unsupported loop: from expression is not constant") };
                    let to_const = if let Expression::Literal(LiteralExpression::DecimalLiteral(ref dle)) = to_expr {
                        dle.value.value.parse::<usize>().unwrap()
                    } else { panic!("Unsupported loop: from expression is not constant") };
                    
                    to_const - from_const
                };

                // Create and push FROM statement
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

                // The block merge analysis requires a loop to start and end at the same & new scope
                // In practice this is translated to an empty block that serves as a loop header
                // Loop structure is of the following:
                // Scope:         X           X + 1         X + 2        X + 1          X
                // Block Name:  FROM BL -> LOOP HEADER -> LOOP BODY -> UPDATE BL -> LOOP TAIL

                // New Scope to enter LOOP HEADER
                cur_scope = self.bl_gen_enter_scope_(cur_scope)?;
                // Create new Block
                blks.push(Block::new(blks_len, loop_num_it * num_exec_bound, f_name.to_string(), cur_scope));
                blks_len += 1;
                let loop_header = blks_len - 1;

                // New Scope AGAIN to enter LOOP BODY
                cur_scope = self.bl_gen_enter_scope_(cur_scope)?;
                // Create new Block
                blks.push(Block::new(blks_len, loop_num_it * num_exec_bound, f_name.to_string(), cur_scope));
                blks_len += 1;
                
                // Iterate through Stmts
                for body in &it.statements {
                    (blks, blks_len, var_scope_info) = self.bl_gen_stmt_::<IS_MAIN>(blks, blks_len, body, ret_ty, f_name, var_scope_info, loop_num_it * num_exec_bound, cur_scope)?;
                }

                // Exit scoping for UPDATE BL
                (var_scope_info, cur_scope) = self.bl_gen_exit_scope_(var_scope_info, f_name, cur_scope)?;
                // Create new Block for iterator update
                blks.push(Block::new(blks_len, loop_num_it * num_exec_bound, f_name.to_string(), cur_scope));
                blks_len += 1;

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

                // Exit scoping for LOOP TAIL
                (var_scope_info, cur_scope) = self.bl_gen_exit_scope_(var_scope_info, f_name, cur_scope)?;
                // Create new Block to resolve any scope change on the iterator
                blks.push(Block::new(blks_len, loop_num_it * num_exec_bound, f_name.to_string(), cur_scope));
                blks_len += 1;

                // Create and push TRANSITION statement towards header & tail
                let loop_tail = blks_len - 1;
                let term = BlockTerminator::Transition(
                    bl_trans(
                        cond_expr(new_id.clone(), to_expr), 
                        NextBlock::Label(loop_header), 
                        NextBlock::Label(loop_tail)
                    )
                );
                blks[loop_header - 1].terminator = term.clone();
                blks[loop_tail - 1].terminator = term;

                // Exit scoping again to outside the loop
                (var_scope_info, cur_scope) = self.bl_gen_exit_scope_(var_scope_info, f_name, cur_scope)?;

                // Create new block
                blks.push(Block::new(blks_len, num_exec_bound, f_name.to_string(), cur_scope));
                blks_len += 1;
            }
            Statement::WhileLoop(w) => {
                // Process function calls in the condition
                let cond_expr: Expression;
                let array_init_info: Vec<Expression>;
                (blks, blks_len, var_scope_info, cond_expr, _, _, array_init_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &w.condition, f_name, 0, 0, var_scope_info)?;
                if array_init_info.len() > 0 { panic!("Inline array inside while loop condition not supported!") }

                // New Scope to enter LOOP BODY
                cur_scope = self.bl_gen_enter_scope_(cur_scope)?;
                // Create new Block. While loops cannot be unrolled.
                blks.push(Block::new(blks_len, num_exec_bound, f_name.to_string(), cur_scope));
                blks[blks_len].is_head_of_while_loop = true;
                blks_len += 1;
                let loop_header = blks_len - 1;
                
                // Iterate through Stmts. Stmts inside while loops can be merged.
                for body in &w.statements {
                    (blks, blks_len, var_scope_info) = self.bl_gen_stmt_::<IS_MAIN>(blks, blks_len, body, ret_ty, f_name, var_scope_info, num_exec_bound, cur_scope)?;
                }

                // Exit scoping for LOOP TAIL
                (var_scope_info, cur_scope) = self.bl_gen_exit_scope_(var_scope_info, f_name, cur_scope)?;
                // Create new block
                blks.push(Block::new(blks_len, num_exec_bound, f_name.to_string(), cur_scope));
                blks_len += 1;

                // Create and push TRANSITION statement towards header & tail
                let loop_tail = blks_len - 1;
                let term = BlockTerminator::Transition(
                    bl_trans(
                        cond_expr, 
                        NextBlock::Label(loop_header), 
                        NextBlock::Label(loop_tail)
                    )
                );
                blks[loop_header - 1].terminator = term.clone();
                blks[loop_tail - 1].terminator = term;
            }
            Statement::Conditional(c) => {
                // Process function calls in the condition
                let cond_expr: Expression;
                let array_init_info: Vec<Expression>;
                (blks, blks_len, var_scope_info, cond_expr, _, _, array_init_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &c.condition, f_name, 0, 0, var_scope_info)?;
                if array_init_info.len() > 0 { panic!("Inline array inside branch condition not supported!!") }

                let head_state = blks_len - 1;

                // If statements
                // Enter Scoping
                cur_scope = self.bl_gen_enter_scope_(cur_scope)?;
                // Create new Block
                blks.push(Block::new(blks_len, num_exec_bound, f_name.to_string(), cur_scope));
                blks_len += 1;
                // Iterate through Stmts
                for body in &c.ifbranch {
                    (blks, blks_len, var_scope_info) = self.bl_gen_stmt_::<IS_MAIN>(blks, blks_len, body, ret_ty, f_name, var_scope_info, num_exec_bound, cur_scope)?;
                }
                // Exit Scoping
                (var_scope_info, cur_scope) = self.bl_gen_exit_scope_(var_scope_info, f_name, cur_scope)?;
                let if_tail_state = blks_len - 1;

                // Else statements
                // Enter Scoping
                cur_scope = self.bl_gen_enter_scope_(cur_scope)?;
                // Create new Block
                blks.push(Block::new(blks_len, num_exec_bound, f_name.to_string(), cur_scope));
                blks_len += 1;
                // Iterate through Stmts
                for body in &c.elsebranch {
                    (blks, blks_len, var_scope_info) = self.bl_gen_stmt_::<IS_MAIN>(blks, blks_len, body, ret_ty, f_name, var_scope_info, num_exec_bound, cur_scope)?;
                }
                // Exit Scoping
                (var_scope_info, cur_scope) = self.bl_gen_exit_scope_(var_scope_info, f_name, cur_scope)?;
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
                blks.push(Block::new(blks_len, num_exec_bound, f_name.to_string(), cur_scope));
                blks_len += 1;
            }
            Statement::Definition(d) => {
                // XXX(unimpl) multi-assignment unimplemented
                assert!(d.lhs.len() <= 1);

                // Evaluate function calls in expression
                let mut lhs_expr = d.lhs.clone();
                let rhs_expr: Expression;
                let array_init_info: Vec<Expression>;
                (blks, blks_len, var_scope_info, rhs_expr, _, _, array_init_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &d.expression, f_name, 0, 0, var_scope_info)?;
                
                self.set_lhs_ty_defn::<false>(d)?;
                let e = self.expr_impl_::<false>(&d.expression)?;
                // Array declaration
                // If array_init_info is defined, then the RHS must be the same array
                if array_init_info.len() > 0 {
                    if let Some(l) = d.lhs.first() {
                        let lhs_id = match l {
                            TypedIdentifierOrAssignee::TypedIdentifier(l) => {
                                let decl_ty = self.type_impl_::<false>(&l.ty)?;
                                let ty = e.type_();
                                if &decl_ty != ty {
                                    return Err(format!(
                                        "Assignment type mismatch: {} annotated vs {} actual",
                                        decl_ty, ty,
                                    ));
                                }

                                // Unroll scoping on LHS
                                let arr_name = &l.identifier.value;
                                // Add the identifier to current scope
                                self.declare_init_impl_::<false>(
                                    arr_name.clone(),
                                    decl_ty.clone(),
                                    e,
                                )?;
                                let arr_extended_name = var_scope_info.declare_var(arr_name, f_name, cur_scope);
                                // Declare array
                                if let Ty::Array(size, entry_ty) = decl_ty {
                                    blks[blks_len - 1].instructions.push(BlockContent::ArrayInit((arr_extended_name.clone(), *entry_ty.clone(), size)));
                                    var_scope_info.arr_map.insert(arr_extended_name.clone(), *entry_ty.clone());
                                }
                                arr_extended_name
                            }
                            TypedIdentifierOrAssignee::Assignee(l) => {
                                // Array is already declared
                                let arr_extended_name = var_scope_info.reference_var(&l.id.value.clone(), f_name)?;
                                arr_extended_name
                            }
                        };
                        (blks, blks_len) = self.bl_gen_array_init_(blks, blks_len, lhs_id, array_init_info, &var_scope_info)?;
                    } else {
                        warn!("Statement with no LHS!");
                    }
                } 
                // Non-array declaration
                else {
                    let mut assignee_is_store = false;
                    // Handle Scoping change
                    if let Some(l) = d.lhs.first() {
                        match l {
                            TypedIdentifierOrAssignee::Assignee(l) => {
                                // No scoping change if lhs is an assignee, only need to make sure it has appeared before
                                let new_l = var_scope_info.reference_var(&l.id.value.clone(), f_name)?;

                                let new_id = IdentifierExpression {
                                    value: new_l.clone(),
                                    span: Span::new("", 0, 0).unwrap()
                                };

                                // if the LHS is an array member, convert the assignee to a store
                                let lhs_ty = self.circ_lookup_type(&l.id.value).ok_or_else(|| format!("Assignment failed: no variable {}", &new_l))?;
                                if let Ty::Array(_, entry_ty) = lhs_ty.clone() {
                                    assignee_is_store = true;
                                    if l.accesses.len() != 1 { return Err(format!("Assignment to multiple array entries unsupported")); }
                                    if let AssigneeAccess::Select(a) = &l.accesses[0] {
                                        if let RangeOrExpression::Expression(e) = &a.expression {
                                            let new_e: Expression;
                                            let tmp_arr_info: Vec<Expression>;
                                            (blks, blks_len, var_scope_info, new_e, _, _, tmp_arr_info) = 
                                                self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &e, f_name, 0, 0, var_scope_info)?;
                                            if tmp_arr_info.len() > 0 { panic!("Currently do not support array initialization inside array indices") }
                                            blks[blks_len - 1].instructions.push(BlockContent::Store((rhs_expr.clone(), *entry_ty.clone(), new_l, new_e)));
                                            let ty_mem_op_count = *blks[blks_len - 1].mem_op_by_ty.get(&entry_ty).unwrap_or(&0);
                                            blks[blks_len - 1].mem_op_by_ty.insert(*entry_ty.clone(), ty_mem_op_count + 3);
                                        } else {
                                            return Err(format!("Array range access not implemented!"));
                                        }
                                    } else {
                                        return Err(format!("Illegal access to array {}", new_l));
                                    }
                                }
                                // otherwise convert the assignee to a declaration
                                else {
                                    lhs_expr = vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                                        ty: ty_to_type(&lhs_ty)?,
                                        identifier: new_id.clone(),
                                        span: Span::new("", 0, 0).unwrap()
                                    })];
                                }
                            }
                            TypedIdentifierOrAssignee::TypedIdentifier(l) => {
                                let decl_ty = self.type_impl_::<false>(&l.ty)?;
                                let ty = e.type_();
                                if &decl_ty != ty {
                                    return Err(format!(
                                        "Assignment type mismatch: {} annotated vs {} actual",
                                        decl_ty, ty,
                                    ));
                                }

                                // Unroll scoping on LHS
                                let id = &l.identifier.value;
                                let new_l = var_scope_info.declare_var(id, f_name, cur_scope);

                                // Add the identifier to current scope
                                self.declare_init_impl_::<false>(
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
                    };
                    if !assignee_is_store {
                        let new_stmt = Statement::Definition(DefinitionStatement {
                            lhs: lhs_expr,
                            expression: rhs_expr,
                            span: Span::new("", 0, 0).unwrap()
                        });
                        blks[blks_len - 1].instructions.push(BlockContent::Stmt(new_stmt));
                    }
                }
            }
            Statement::CondStore(_) => { panic!("Conditional store statements unsupported.") }
        }
        Ok((blks, blks_len, var_scope_info))
    }

    // Generate blocks from expressions
    // Return value:
    // result[0 ~ 2] follows bl_gen_stmt
    // result[3]: new_expr reconstructs the expression, converts all function calls to %RET, and handles scoping
    // result[4]: func_count, how many function calls have occured in this statement?
    // result[5]: load_count, how many loads have occured in this statement?
    // result[5]: all (index, value) pair for array initialization
    // Since the return value of all function calls are stored in %RET, we need to differentiate them if
    // multiple function calls occur in the same statement
    fn bl_gen_expr_<const IS_MAIN: bool>(
        &'ast self, 
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        e: &'ast Expression<'ast>,
        f_name: &str,
        mut func_count: usize,
        mut load_count: usize,
        mut var_scope_info: VarScopeInfo
    ) -> Result<(Vec<Block>, usize, VarScopeInfo, Expression, usize, usize, Vec<Expression>), String> {
        debug!("Block Gen Expr: {}", e.span().as_str());

        let mut ret_e = e.clone();
        // All (index, value) pair for array initialization, currently cannot be put inside any other expression
        let mut array_init_info = Vec::new();

        match e {
            Expression::Ternary(t) => {
                let mut tmp_arr_info: Vec<Expression>;
                let new_e_first: Expression;
                let new_e_second: Expression;
                let new_e_third: Expression;
                (blks, blks_len, var_scope_info, new_e_first, func_count, load_count, tmp_arr_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &t.first, f_name, func_count, load_count, var_scope_info)?;
                if tmp_arr_info.len() > 0 { panic!("Currently do not support array initialization inside ternary expressions") }
                (blks, blks_len, var_scope_info, new_e_second, func_count, load_count, tmp_arr_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &t.second, f_name, func_count, load_count, var_scope_info)?;
                if tmp_arr_info.len() > 0 { panic!("Currently do not support array initialization inside ternary expressions") }
                (blks, blks_len, var_scope_info, new_e_third, func_count, load_count, tmp_arr_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &t.third, f_name, func_count, load_count, var_scope_info)?;
                if tmp_arr_info.len() > 0 { panic!("Currently do not support array initialization inside ternary expressions") }
                ret_e = Expression::Ternary(TernaryExpression {
                    first: Box::new(new_e_first),
                    second: Box::new(new_e_second),
                    third: Box::new(new_e_third),
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::Binary(b) => {
                let mut tmp_arr_info: Vec<Expression>;
                let new_e_left: Expression;
                let new_e_right: Expression;
                (blks, blks_len, var_scope_info, new_e_left, func_count, load_count, tmp_arr_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &b.left, f_name, func_count, load_count, var_scope_info)?;
                if tmp_arr_info.len() > 0 { panic!("Currently do not support array initialization inside binary expressions") }
                (blks, blks_len, var_scope_info, new_e_right, func_count, load_count, tmp_arr_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &b.right, f_name, func_count, load_count, var_scope_info)?;
                if tmp_arr_info.len() > 0 { panic!("Currently do not support array initialization inside binary expressions") }
                ret_e = Expression::Binary(BinaryExpression {
                    op: b.op.clone(),
                    left: Box::new(new_e_left),
                    right: Box::new(new_e_right),
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::Unary(u) => {
                let tmp_arr_info: Vec<Expression>;
                let new_e_expr: Expression;
                (blks, blks_len, var_scope_info, new_e_expr, func_count, load_count, tmp_arr_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &u.expression, f_name, func_count, load_count, var_scope_info)?;
                if tmp_arr_info.len() > 0 { panic!("Currently do not support array initialization inside unary expressions") }
                ret_e = Expression::Unary(UnaryExpression {
                    op: u.op.clone(),
                    expression: Box::new(new_e_expr),
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::Postfix(p) => {
                let mut tmp_arr_info: Vec<Expression>;
                // assume no functions in arrays, etc.
                assert!(!p.accesses.is_empty());
                match p.accesses.first() {
                    Some(Access::Call(c)) => {
                        let (callee_path, callee_name) = self.deref_import(&p.id.value);
                        let mut args: Vec<Expression> = Vec::new();
                        let mut new_expr: Expression;
                        for old_expr in &c.arguments.expressions {
                            (blks, blks_len, var_scope_info, new_expr, func_count, load_count, tmp_arr_info) = 
                                self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, old_expr, f_name, func_count, load_count, var_scope_info)?;
                            if tmp_arr_info.len() > 0 { panic!("Currently do not support array initialization inside function calls") }
                            args.push(new_expr);                       
                        }
     
                        // Do the function call
                        (blks, blks_len, _, var_scope_info, func_count) =
                            self.bl_gen_function_call_::<IS_MAIN>(blks, blks_len, args, callee_path.clone(), callee_name.clone(), func_count, var_scope_info)?;
    
                        let ret_name = format!("ret@{}", func_count);
                        let ret_extended_name = var_scope_info.reference_var(&ret_name, f_name)?;
                        ret_e = Expression::Identifier(IdentifierExpression {
                            value: ret_extended_name,
                            span: Span::new("", 0, 0).unwrap()
                        });
                        func_count += 1;
                    }
                    Some(Access::Select(s)) => {
                        if let RangeOrExpression::Expression(e) = &s.expression {
                            // Store the loaded value in a separate and return it
                            let load_name = format!("load@{}", load_count);
                            let arr_name = &p.id.value;
                            let arr_extended_name = var_scope_info.reference_var(&arr_name, f_name)?;
                            let load_ty = var_scope_info.arr_map.get(&arr_extended_name).ok_or_else(|| format!("Load failed: no array {}", &arr_extended_name))?.clone();
                            self.decl_impl_::<false>(load_name.clone(), &load_ty)?;
                            let cur_scope = blks[blks_len - 1].scope;
                            let load_extended_name = var_scope_info.declare_var(&load_name, &f_name, cur_scope);
                            
                            // Preprocess the indices
                            let new_e: Expression;
                            let tmp_arr_info: Vec<Expression>;
                            (blks, blks_len, var_scope_info, new_e, _, _, tmp_arr_info) = 
                                self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &e, f_name, 0, 0, var_scope_info)?;
                            if tmp_arr_info.len() > 0 { panic!("Currently do not support array initialization inside array indices") }
                            blks[blks_len - 1].instructions.push(BlockContent::Load((load_extended_name.clone(), load_ty.clone(), arr_extended_name.clone(), new_e)));
                            let ty_mem_op_count = *blks[blks_len - 1].mem_op_by_ty.get(&load_ty).unwrap_or(&0);
                            blks[blks_len - 1].mem_op_by_ty.insert(load_ty.clone(), ty_mem_op_count + 1);
                            load_count += 1;
                            ret_e = Expression::Identifier(IdentifierExpression {
                                value: load_extended_name,
                                span: Span::new("", 0, 0).unwrap()
                            });
                        } else {
                            return Err(format!("Array range access not implemented!"));
                        }
                    }
                    _ => { return Err(format!("Struct not implemented!")); }
                }
            }
            Expression::Identifier(i) => {
                let new_var: String = var_scope_info.reference_var(&i.value.clone(), &f_name)?;
                ret_e = Expression::Identifier(IdentifierExpression {
                    value: new_var,
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::Literal(_) => {}
            Expression::ArrayInitializer(ai) => {
                let init_ty = self.expr_impl_::<false>(&ai.value)?.type_().clone();
                let new_ai_value: Expression;
                (blks, blks_len, var_scope_info, new_ai_value, func_count, load_count, _) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &ai.value, f_name, func_count, load_count, var_scope_info)?;
                // Create a temporary variable to store the shared expression
                let init_name = "init@0".to_string();
                self.decl_impl_::<false>(init_name.clone(), &init_ty)?;
                let cur_scope = blks[blks_len - 1].scope;
                let init_extended_name = var_scope_info.declare_var(&init_name, &f_name, cur_scope);
                let init_ty = ty_to_type(&init_ty)?;
                let array_init_stmt = Statement::Definition(DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                        ty: init_ty,
                        identifier: IdentifierExpression {
                            value: init_extended_name.clone(),
                            span: Span::new("", 0, 0).unwrap()
                        },
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    // Assume that we only have ONE return variable
                    expression: new_ai_value.clone(),
                    span: Span::new("", 0, 0).unwrap()
                });
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(array_init_stmt));
                // Initialize the array to that temporary variable
                // Expression of init@
                let array_init_expr = Expression::Identifier(IdentifierExpression {
                    value: init_extended_name,
                    span: Span::new("", 0, 0).unwrap()
                });
                // Size of array
                let arr_size: usize = const_int(self.expr_impl_::<false>(&ai.count)?)?.try_into().unwrap();
                array_init_info = vec![array_init_expr.clone(); arr_size];
            }
            Expression::InlineArray(ia) => {
                for se in &ia.expressions {
                    if let SpreadOrExpression::Expression(e) = se {
                        let tmp_arr_info: Vec<Expression>;
                        let new_e: Expression;
                        (blks, blks_len, var_scope_info, new_e, func_count, load_count, tmp_arr_info) = 
                            self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &e, f_name, func_count, load_count, var_scope_info)?;
                        if tmp_arr_info.len() > 0 { panic!("Currently do not support array initialization inside inline arrays") }
                        array_init_info.push(new_e.clone());
                    } else {
                        return Err(format!("Spread not supported in inline arrays!"));
                    }
                }
            }
            Expression::InlineStruct(_) => { return Err(format!("Struct not supported!")); }
        }
        Ok((blks, blks_len, var_scope_info, ret_e, func_count, load_count, array_init_info))
    }

    // Generate blocks from an array initialization
    // Assume both the array and all entries are preprocessed
    // Returns the new blocks
    fn bl_gen_array_init_(
        &'ast self, 
        mut blks: Vec<Block<'ast>>,
        blks_len: usize,
        arr_extended_name: String,
        array_init_info: Vec<Expression<'ast>>,
        var_scope_info: &VarScopeInfo
    ) -> Result<(Vec<Block>, usize), String> {
        let mut index = 0;
        let entry_ty = var_scope_info.arr_map.get(&arr_extended_name).ok_or_else(|| format!("Assignment failed: no array {}", &arr_extended_name))?;
        for entry in array_init_info {
            let index_expr = Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                value: DecimalNumber {
                    value: index.to_string(),
                    span: Span::new("", 0, 0).unwrap()
                },
                suffix: Some(DecimalSuffix::Field(FieldSuffix {
                    span: Span::new("", 0, 0).unwrap()
                })),
                span: Span::new("", 0, 0).unwrap()
            }));
            blks[blks_len - 1].instructions.push(BlockContent::Store((entry, entry_ty.clone(), arr_extended_name.clone(), index_expr)));
            let ty_mem_op_count = *blks[blks_len - 1].mem_op_by_ty.get(&entry_ty).unwrap_or(&0);
            blks[blks_len - 1].mem_op_by_ty.insert(entry_ty.clone(), ty_mem_op_count + 3);
            index += 1;
        }
        Ok((blks, blks_len))
    }


    fn bl_gen_enter_scope_(
        &'ast self,
        cur_scope: usize,
    ) -> Result<usize, String> {
        // New Scoping
        self.enter_scope_impl_::<false>();

        Ok(cur_scope + 1)
    }

    fn bl_gen_exit_scope_(
        &'ast self,
        mut var_scope_info: VarScopeInfo,
        fn_name: &str,
        cur_scope: usize,
    ) -> Result<(VarScopeInfo, usize), String> {
        // Exit Scoping
        self.exit_scope_impl_::<false>();

        var_scope_info.exit_scope(fn_name, cur_scope);
        Ok((var_scope_info, cur_scope - 1))
    }

    // Convert a list of blocks to circ_ir
    pub fn bls_to_circ(&'ast self, blks: &Vec<Block>, mem_offset_map: &HashMap<String, usize>) {
        for b in blks {
            let f = &format!("Block_{}", b.name);
            self.circ_init_block(f);
            self.bl_to_circ::<false>(&b, f, mem_offset_map);
        }
    }

    // asserts var == cnst
    fn bl_gen_assert_const(&'ast self, var: &str, cnst: usize) {
        let lhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
            value: var.to_string(),
            span: Span::new("", 0, 0).unwrap()
        })).unwrap();
        let rhs_t = self.expr_impl_::<false>(&Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
            value: DecimalNumber {
                value: cnst.to_string(),
                span: Span::new("", 0, 0).unwrap()
            },
            suffix: Some(DecimalSuffix::Field(FieldSuffix {
                span: Span::new("", 0, 0).unwrap()
            })),
            span: Span::new("", 0, 0).unwrap()
        }))).unwrap();
        let b = bool(eq(lhs_t, rhs_t).unwrap()).unwrap();
        self.assert(b);
    }

    // asserts var1 == var2
    fn bl_gen_assert_eq(&'ast self, var1: &str, var2: &str) {
        let lhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
            value: var1.to_string(),
            span: Span::new("", 0, 0).unwrap()
        })).unwrap();
        let rhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
            value: var2.to_string(),
            span: Span::new("", 0, 0).unwrap()
        })).unwrap();
        let b = bool(eq(lhs_t, rhs_t).unwrap()).unwrap();
        self.assert(b);
    }

    // Convert a virtual memory operation to circ_ir
    // MODE: LOAD, STORE, DUMMY_LOAD
    fn vir_mem_to_circ<const MODE: usize>(
        &'ast self,
        f: &str,
        mut ty_mem_op_offset: BTreeMap<Ty, usize>,
        array_offset_map: &HashMap<String, usize>,
        ty: &Ty,
        arr: Option<&String>,
        id_expr: Option<&Expression<'ast>>,
    ) -> (BTreeMap<Ty, usize>, usize) {
        // Obtain the label for the memory operation
        let mut next_label = ty_mem_op_offset.get(&ty).unwrap().clone();

        // Declare the next PHY_ADDR, VIR_ADDR, VAL, L/S, and TS
        // For simplicity, call them a, b, c, l, t

        // INIT_ACCESS
        // For LOAD, this is to obtain the value
        // For STORE, this is to obtain the physical memory
        // For DUMMY_LOAD, this does nothing
        // PHY_ADDR as 'a'
        self.circ_declare_input(
            f,
            format!("%vm{:06}a", next_label),
            &Ty::Field,
            ZVis::Private(0),
            None,
            true,
        ).unwrap();
        // VIR_ADDR as 'b'
        self.circ_declare_input(
            f,
            format!("%vm{:06}b", next_label),
            ty,
            ZVis::Private(0),
            None,
            true,
        ).unwrap();
        // VAL as 'c'
        self.circ_declare_input(
            f,
            format!("%vm{:06}c", next_label),
            ty,
            ZVis::Private(0),
            None,
            true,
        ).unwrap();
        // LS as 'l'
        self.circ_declare_input(
            f,
            format!("%vm{:06}l", next_label),
            &Ty::Field,
            ZVis::Private(0),
            None,
            true,
        ).unwrap();
        // TS as 't'
        self.circ_declare_input(
            f,
            format!("%vm{:06}t", next_label),
            &Ty::Field,
            ZVis::Private(0),
            None,
            true,
        ).unwrap();
        // VIR_ADDR if exist
        if let Some(addr_expr) = id_expr {
            // lhs_t + offset_t == rhs_t
            let mut lhs_t = self.expr_impl_::<false>(&addr_expr).unwrap();
            // if lhs_t is not a field, cast it to a field
            if lhs_t.type_() != &Ty::Field {
                lhs_t = uint_to_field(lhs_t).unwrap();
            }
            let offset_t = self.expr_impl_::<false>(&Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                value: DecimalNumber {
                    value: array_offset_map.get(arr.unwrap()).unwrap().to_string(),
                    span: Span::new("", 0, 0).unwrap()
                },
                suffix: Some(DecimalSuffix::Field(FieldSuffix {
                    span: Span::new("", 0, 0).unwrap()
                })),
                span: Span::new("", 0, 0).unwrap()
            }))).unwrap();
            let rhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                value: format!("%vm{:06}b", next_label),
                span: Span::new("", 0, 0).unwrap()
            })).unwrap();
            let b = bool(eq(add(lhs_t, offset_t).unwrap(), rhs_t).unwrap()).unwrap();
            self.assert(b);
        }

        // LS
        self.bl_gen_assert_const(&format!("%vm{:06}l", next_label), LOAD);
        // TS
        self.bl_gen_assert_eq(&format!("%w1"), &format!("%vm{:06}t", next_label));

        // if STORE or DUMMY_LOAD, additional entries for 
        // 1. physical address retrieval / dummy retrieval
        // 2. invalidation / dummy invalidation
        if MODE == STORE || MODE == DUMMY_LOAD {
            // Increment label
            next_label += 1;

            // If STORE, increment timestamp
            if MODE == STORE {
                self.stmt_impl_::<false>(&bl_gen_increment_stmt("%w1", 1)).unwrap();
            }

            // INVALIDATION
            // PHY_ADDR as 'a'
            self.circ_declare_input(
                f,
                format!("%vm{:06}a", next_label),
                &Ty::Field,
                ZVis::Private(0),
                None,
                true,
            ).unwrap();
            // VIR_ADDR as 'b'
            self.circ_declare_input(
                f,
                format!("%vm{:06}b", next_label),
                ty,
                ZVis::Private(0),
                None,
                true,
            ).unwrap();
            // VAL as 'c'
            self.circ_declare_input(
                f,
                format!("%vm{:06}c", next_label),
                ty,
                ZVis::Private(0),
                None,
                true,
            ).unwrap();
            // LS as 'l'
            self.circ_declare_input(
                f,
                format!("%vm{:06}l", next_label),
                &Ty::Field,
                ZVis::Private(0),
                None,
                true,
            ).unwrap();
            // TS as 't'
            self.circ_declare_input(
                f,
                format!("%vm{:06}t", next_label),
                &Ty::Field,
                ZVis::Private(0),
                None,
                true,
            ).unwrap();


            // If STORE, PHY_ADDR matches with previous LOAD and VIR_ADDR & VAL are simply 0
            if MODE == STORE {
                self.bl_gen_assert_eq(&format!("%vm{:06}a", next_label - 1), &format!("%vm{:06}a", next_label));
                self.bl_gen_assert_const(&format!("%vm{:06}b", next_label), 0);
                self.bl_gen_assert_const(&format!("%vm{:06}c", next_label), 0);
            }
            // LS
            self.bl_gen_assert_const(&format!("%vm{:06}l", next_label), if MODE == STORE { STORE } else { LOAD });
            // TS
            self.bl_gen_assert_eq(&format!("%w1"), &format!("%vm{:06}t", next_label));

            // Increment next_label
            next_label += 1;

            // ALLOCATION
            // PHY_ADDR as 'a'
            self.circ_declare_input(
                f,
                format!("%vm{:06}a", next_label),
                &Ty::Field,
                ZVis::Private(0),
                None,
                true,
            ).unwrap();
            // VIR_ADDR as 'b'
            self.circ_declare_input(
                f,
                format!("%vm{:06}b", next_label),
                ty,
                ZVis::Private(0),
                None,
                true,
            ).unwrap();
            // VAL as 'c'
            self.circ_declare_input(
                f,
                format!("%vm{:06}c", next_label),
                ty,
                ZVis::Private(0),
                None,
                true,
            ).unwrap();
            // LS as 'l'
            self.circ_declare_input(
                f,
                format!("%vm{:06}l", next_label),
                &Ty::Field,
                ZVis::Private(0),
                None,
                true,
            ).unwrap();
            // TS as 't'
            self.circ_declare_input(
                f,
                format!("%vm{:06}t", next_label),
                &Ty::Field,
                ZVis::Private(0),
                None,
                true,
            ).unwrap();

            // If STORE, PHY_ADDR matches with TS
            if MODE == STORE {
                self.bl_gen_assert_eq(&format!("%w1"), &format!("%vm{:06}a", next_label));    
            }

            // VIR_ADDR
            if let Some(addr_expr) = id_expr {
                // lhs_t + offset_t == rhs_t
                let mut lhs_t = self.expr_impl_::<false>(&addr_expr).unwrap();
                // if lhs_t is not a field, cast it to a field
                if lhs_t.type_() != &Ty::Field {
                    lhs_t = uint_to_field(lhs_t).unwrap();
                }
                let offset_t = self.expr_impl_::<false>(&Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                    value: DecimalNumber {
                        value: array_offset_map.get(arr.unwrap()).unwrap().to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    },
                    suffix: Some(DecimalSuffix::Field(FieldSuffix {
                        span: Span::new("", 0, 0).unwrap()
                    })),
                    span: Span::new("", 0, 0).unwrap()
                }))).unwrap();
                let rhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                    value: format!("%vm{:06}b", next_label),
                    span: Span::new("", 0, 0).unwrap()
                })).unwrap();
                let b = bool(eq(add(lhs_t, offset_t).unwrap(), rhs_t).unwrap()).unwrap();
                self.assert(b);
            }
            // LS
            self.bl_gen_assert_const(&format!("%vm{:06}l", next_label), if MODE == STORE { STORE } else { LOAD });
            // TS
            self.bl_gen_assert_eq(&format!("%w1"), &format!("%vm{:06}t", next_label));
        }
        // VAL is handled individually depending on LOAD & STORE

        // Update label
        ty_mem_op_offset.insert(ty.clone(), next_label + 1);

        (ty_mem_op_offset, next_label)
    }

    // Convert a block to circ_ir
    // This can be done to either produce the constraints, or to estimate the size of constraints
    // In estimation mode, we rename all output variable from X -> oX, add assertion, and process the terminator
    pub fn bl_to_circ<const ESTIMATE: bool>(&self, b: &Block, f: &str, array_offset_map: &HashMap<String, usize>) {
        // setup stack frame for entry function
        // returns the next block, so return type is Field
        let ret_ty = Some(Ty::Field);
        self.circ_enter_fn(f.to_string(), ret_ty.clone());

        // Declare all inputs of the block
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
        // If not in estimation mode, declare all outputs of the block, and
        if !ESTIMATE {
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
        }

        // How many scoping memory operations have we encountered?
        let mut phy_mem_op_count = 0;
        // The label of the next memory operation on the specific type
        let mut ty_mem_op_offset = BTreeMap::new();
        let mut alloc_vir_mem_op_count = 0;
        for (ty, count) in &b.mem_op_by_ty {
            ty_mem_op_offset.insert(ty.clone(), alloc_vir_mem_op_count);
            alloc_vir_mem_op_count += count;
        }
        
        // Iterate over instructions, convert memory accesses into statements and then IR
        for i in &b.instructions {
            match i {
                BlockContent::MemPush((var, ty, offset)) => {
                    // Non-deterministically supply ADDR
                    self.circ_declare_input(
                        &f,
                        format!("%pm{:06}a", phy_mem_op_count),
                        ty,
                        ZVis::Private(0),
                        None,
                        true,
                    ).unwrap();
                    // Non-deterministically supply VAL
                    self.circ_declare_input(
                        &f,
                        format!("%pm{:06}v", phy_mem_op_count),
                        ty,
                        ZVis::Private(0),
                        None,
                        true,
                    ).unwrap();
                    // Assert correctness of address
                    let lhs_t = self.expr_impl_::<false>(&Expression::Binary(BinaryExpression {
                        op: BinaryOperator::Add,
                        left: Box::new(Expression::Identifier(IdentifierExpression {
                            // %SP
                            value: if ESTIMATE { "%SP".to_string() } else { "%w3".to_string() },
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
                        value: format!("%pm{:06}a", phy_mem_op_count),
                        span: Span::new("", 0, 0).unwrap()
                    })).unwrap();
                    let b = bool(eq(lhs_t, rhs_t).unwrap()).unwrap();
                    self.assert(b);
                    // Assert correctness of value
                    let lhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                        value: var.to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    })).unwrap();
                    let rhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                        value: format!("%pm{:06}v", phy_mem_op_count),
                        span: Span::new("", 0, 0).unwrap()
                    })).unwrap();
                    let b = bool(eq(lhs_t, rhs_t).unwrap()).unwrap();
                    self.assert(b);
                    phy_mem_op_count += 1;
                }
                BlockContent::MemPop((var, ty, offset)) => {
                    // Non-deterministically supply ADDR and VAL in memory
                    self.circ_declare_input(
                        &f,
                        format!("%pm{:06}a", phy_mem_op_count),
                        ty,
                        ZVis::Private(0),
                        None,
                        true,
                    ).unwrap();
                    self.circ_declare_input(
                        &f,
                        format!("%pm{:06}v", phy_mem_op_count),
                        ty,
                        ZVis::Private(0),
                        None,
                        true,
                    ).unwrap();
                    // Assert correctness of address
                    let lhs_t = self.expr_impl_::<false>(&Expression::Binary(BinaryExpression {
                        op: BinaryOperator::Add,
                        left: Box::new(Expression::Identifier(IdentifierExpression {
                            // %BP
                            value: if ESTIMATE { "%BP".to_string() } else { "%w4".to_string() },
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
                        value: format!("%pm{:06}a", phy_mem_op_count),
                        span: Span::new("", 0, 0).unwrap()
                    })).unwrap();
                    let b = bool(eq(lhs_t, rhs_t).unwrap()).unwrap();
                    self.assert(b);
                    // Assign POP value to val
                    let e = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                        value: format!("%pm{:06}v", phy_mem_op_count),
                        span: Span::new("", 0, 0).unwrap()
                    })).unwrap();
                    self.declare_init_impl_::<false>(
                        var.clone(),
                        ty.clone(),
                        e,
                    ).unwrap();
                    phy_mem_op_count += 1;  
                }
                BlockContent::ArrayInit(_) => {}
                BlockContent::Store((val_expr, ty, arr, id_expr)) => {
                    if ESTIMATE {}
                    else {
                        let next_label: usize;
                        // ADDR, IO, & TS
                        (ty_mem_op_offset, next_label) = self.vir_mem_to_circ::<STORE>(
                            f,
                            ty_mem_op_offset,
                            array_offset_map,
                            &ty,
                            Some(&arr),
                            Some(&id_expr)
                        );
                        // Assert correctness of VAL
                        let lhs_t = self.expr_impl_::<false>(&val_expr).unwrap();
                        let rhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                            value: format!("%vm{:06}c", next_label),
                            span: Span::new("", 0, 0).unwrap()
                        })).unwrap();
                        let b = bool(eq(lhs_t, rhs_t).unwrap()).unwrap();
                        self.assert(b);
                    }
                }
                BlockContent::Load((val, ty, arr, id_expr)) => {
                    if ESTIMATE {
                        let r = self.circ_declare_input(
                            &f,
                            val.clone(),
                            ty,
                            ZVis::Public,
                            None,
                            true,
                        );
                        r.unwrap();
                    } else {
                        let next_label: usize;
                        // ADDR, IO, & TS
                        (ty_mem_op_offset, next_label) = self.vir_mem_to_circ::<LOAD>(
                            f,
                            ty_mem_op_offset,
                            array_offset_map,
                            &ty,
                            Some(&arr),
                            Some(&id_expr)
                        );
                        // Assign LOAD value to val
                        let e = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                            value: format!("%vm{:06}c", next_label),
                            span: Span::new("", 0, 0).unwrap()
                        })).unwrap();
                        self.declare_init_impl_::<false>(
                            val.clone(),
                            ty.clone(),
                            e,
                        ).unwrap();
                    }
                }
                BlockContent::Stmt(stmt) => { self.stmt_impl_::<false>(&stmt).unwrap(); }
            }
        }
        
        // If in estimation mode, declare and assert all outputs of the block
        // Furthermore, process the terminator
        if ESTIMATE {
            // PROCESS OUTPUT
            for (name, ty) in &b.outputs {
                if let Some(x) = ty {
                    let output_name = format!("o{}", name);
                    // Declare the output
                    let r = self.circ_declare_input(
                        &f,
                        output_name.clone(),
                        x,
                        ZVis::Public,
                        None,
                        true,
                    );
                    r.unwrap();
                    // Assert the correctness of the output
                    let output_check_stmt = Statement::Assertion(AssertionStatement {
                        expression: Expression::Binary(BinaryExpression {
                            op: BinaryOperator::Eq,
                            left: Box::new(Expression::Identifier(IdentifierExpression {
                                value: output_name,
                                span: Span::new("", 0, 0).unwrap()
                            })),
                            right: Box::new(Expression::Identifier(IdentifierExpression {
                                value: name.to_string(),
                                span: Span::new("", 0, 0).unwrap()
                            })),
                            span: Span::new("", 0, 0).unwrap()
                        }),
                        message: None,
                        span: Span::new("", 0, 0).unwrap()
                    });
                    self.stmt_impl_::<false>(&output_check_stmt).unwrap();
                }
            }

            // PROCESS TERMINATOR
            // Should only be used to estimate the number of constraints
            // generate terminator statement
            let new_expr = {
                if let BlockTerminator::Transition(e) = &b.terminator {
                    e.clone()
                } else {
                    // If it is the end of the program, assign %BN to 0 (an arbitrary number)
                    Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                        value: DecimalNumber {
                            value: "0".to_string(),
                            span: Span::new("", 0, 0).unwrap()
                        },
                        suffix: Some(DecimalSuffix::Field(FieldSuffix {
                            span: Span::new("", 0, 0).unwrap()
                        })),
                        span: Span::new("", 0, 0).unwrap()
                    }))
                }
            };

            let output_block_check_stmt = Statement::Assertion(AssertionStatement {
                expression: Expression::Binary(BinaryExpression {
                    op: BinaryOperator::Eq,
                    left: Box::new(Expression::Identifier(IdentifierExpression {
                        value: format!("%oBN"),
                        span: Span::new("", 0, 0).unwrap()
                    })),
                    right: Box::new(new_expr.clone()),
                    span: Span::new("", 0, 0).unwrap()
                }),
                message: None,
                span: Span::new("", 0, 0).unwrap()
            });

            // Declare %oBN
            let r = self.circ_declare_input(
                &f,
                "%oBN".to_string(),
                &Ty::Field,
                ZVis::Public,
                None,
                true,
            );
            r.unwrap();
            // Process statement
            self.stmt_impl_::<false>(&output_block_check_stmt).unwrap();
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
                        .get_mut(f)
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
                    self.circ.borrow().cir_ctx().cs.borrow_mut().get_mut(f).unwrap().outputs.push(t);
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

    pub fn circ_init_block(&self, f: &str) {
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