// TODO: Recursion is not supported.
//       Generics are not supported.
//       Loop breaks are not supported.
//       Structs are not supported.
//       Multi-file program not supported
//       Can try eliminate ternaries with a constant condition
//       What would happen if block 0 is a loop to itself? Many analyses would break down!!!

// TODO: Should not count # of virtual addresses here b/c liveness analysis might remove some of them

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

const STORE: usize = 0;
const LOAD: usize = 1;
const INIT_STORE: usize = 2;
const DUMMY_LOAD: usize = 3;

const W_TS: &str = "%w1";
const W_SP: &str = "%w4";
const W_BP: &str = "%w5";

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

// Convert a field into other types, used for LOADs
fn field_to_ty(f: T, ty: &Ty) -> Result<T, String> {
    match ty {
        Ty::Uint(n) => Ok(T::new(Ty::Uint(*n), term![Op::PfToBv(*n); f.term])),
        Ty::Bool => field_to_bits(f, 1),
        Ty::Field => Ok(f),
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

// Generate the statement: var = 0
pub fn bl_gen_init_stmt<'ast>(var: &str, ty: &Ty) -> Statement<'ast> {
    let typ = ty_to_type(ty).unwrap();
    let var_init_stmt = Statement::Definition(DefinitionStatement {
        lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
            array_metadata: None,
            ty: typ.clone(),
            identifier: IdentifierExpression {
                value: var.to_string(),
                span: Span::new("", 0, 0).unwrap()
            },
            span: Span::new("", 0, 0).unwrap()
        })],
        expression: Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
            value: DecimalNumber {
                value: "0".to_string(),
                span: Span::new("", 0, 0).unwrap()
            },
            suffix: Some(ty_to_dec_suffix(&typ)),
            span: Span::new("", 0, 0).unwrap()
        })),
        span: Span::new("", 0, 0).unwrap()
    });
    var_init_stmt
}

// Generate the statement: var = var + offset
pub fn bl_gen_increment_stmt<'ast>(var: &str, offset: usize) -> Statement<'ast> {
    let var_update_stmt = Statement::Definition(DefinitionStatement {
        lhs: vec![TypedIdentifierOrAssignee::Assignee(Assignee {
            id: IdentifierExpression {
                value: var.to_string(),
                span: Span::new("", 0, 0).unwrap()
            },
            accesses: Vec::new(),
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
    var_update_stmt   
}

#[derive(Clone)]
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
    // Number of non-scoping-related memory accesses
    pub num_vm_ops: usize,
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
    //     val_expr         type   arr   id_expr           init?
    Store((Expression<'ast>, Ty, String, Expression<'ast>, bool)), // arr[id] = val
    //    var    type   arr   id_expr
    Load((String, Ty, String, Expression<'ast>)),  // val = arr[id]
    DummyLoad(),
    Branch((Expression<'ast>, Vec<BlockContent<'ast>>, Vec<BlockContent<'ast>>)),
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
            num_vm_ops: 0,
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
            num_vm_ops: old_bl.num_vm_ops,
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

    // Concatentate blocks together
    pub fn concat(&mut self, succ: Block<'ast>) {
        // Instructions
        self.instructions.extend(succ.instructions);
        // Terminator
        self.terminator = succ.terminator;
        // Add up memory operators
        self.num_vm_ops += succ.num_vm_ops;
    }

    pub fn pretty(&self) {
        println!("\nBlock {}:", self.name);
        println!("Func: {}, Scope: {}", self.fn_name, self.scope);
        println!("Exec Bound: {}, While Loop: {}, Num VM Ops: {}", self.fn_num_exec_bound, self.is_head_of_while_loop, self.num_vm_ops);
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
            pretty_block_content(1, c);
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
    // For each (var_name, fn_name), record all scopes that it has been defined
    // i.e., [0, 2, 3] means the variables has been defined in scope 0, 2, 3
    var_stack: HashMap<(String, String), Vec<(usize, Ty)>>,
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
    fn declare_var(&mut self, var_name: &str, fn_name: &str, cur_scope: usize, ty: Ty) -> String {
        let name = &(var_name.to_string(), fn_name.to_string());
        match self.var_stack.get(name) {
            Some(stack) => {
                assert!(stack.len() == 0 || stack[stack.len() - 1].0 <= cur_scope);
                // If stack[stack.len() - 1] == cur_scope, this is shadowing and we don't need to do anything
                if stack.len() == 0 || stack[stack.len() - 1].0 < cur_scope {
                    let new_stack = [stack.to_vec(), vec![(cur_scope, ty)]].concat();
                    let new_depth = new_stack.len() - 1;
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
                    self.var_stack.insert(name.clone(), new_stack);
                }
            },
            None => {
                // If the variable is never defined, add variable to var_version and var_stack
                self.var_stack.insert(name.clone(), vec![(cur_scope, ty)]);
                let version_list = vec![0];
                self.var_version.insert(name.clone(), version_list.to_vec());
            }
        }
        self.reference_var(var_name, fn_name).unwrap().0
    }

    // Given a variable, return "<var_name>.<func_name>.<scope>.<version>" and its type
    fn reference_var(&self, var_name: &str, fn_name: &str) -> Result<(String, Ty), String> {
        let name = &(var_name.to_string(), fn_name.to_string());
        if let Some(stack) = self.var_stack.get(&name) {
            let depth = stack.len() - 1;
            let version = self.var_version.get(&name).unwrap()[depth];
            let ty = stack[depth].1.clone();
            Ok((format!("{}.{}.{}.{}", var_name, fn_name, depth, version), ty))
        } else {
            Err(format!("get_var_extended_name failed: variable {} does not exist in function {}", var_name, fn_name))
        }
    }

    // exit the current scope
    fn exit_scope(&mut self, fn_name: &str, cur_scope: usize) {
        // First record all variables that need scope change
        let mut updates = HashMap::new();
        for ((var_name, var_fn_name), stack) in &self.var_stack {
            if var_fn_name == fn_name && stack.len() > 0 {
                let var_top_scope = stack[stack.len() - 1].0;
                assert!(var_top_scope <= cur_scope);
                if var_top_scope == cur_scope {
                    updates.insert((var_name.to_string(), var_fn_name.to_string()), stack[..stack.len() - 1].to_vec());
                }
            }
        }
        // Update self.var_stack
        for (name, stack) in updates {
            self.var_stack.insert(name, stack);
        }
    }
}

// All information regarding array initialization
pub struct ArrayInitInfo<'ast> {
    // All unique entries as expressions
    unique_contents: Vec<Expression<'ast>>,
    // Entries of the array, mapped to indices of unique_contents
    arr_entries: Vec<usize>
}

impl<'ast> ArrayInitInfo<'ast> {
    fn new() -> ArrayInitInfo<'ast> {
        ArrayInitInfo {
            unique_contents: Vec::new(),
            arr_entries: Vec::new()
        }
    }

    fn from_array_initializer(value: Expression<'ast>, arr_size: usize) -> ArrayInitInfo<'ast> {
        ArrayInitInfo {
            unique_contents: vec![value],
            arr_entries: vec![0; arr_size]
        }
    }

    fn from_inline_array(entries: Vec<Expression<'ast>>) -> ArrayInitInfo<'ast> {
        let mut unique_contents = Vec::new();
        let mut arr_entries = Vec::new();
        for e in entries.into_iter() {
            unique_contents.push(e.clone());
            arr_entries.push(unique_contents.len() - 1);
        }
        ArrayInitInfo {
            unique_contents,
            arr_entries
        }
    }

    // Check whether ArrayInitInfo is empty
    fn is_empty(&self) -> bool {
        return self.arr_entries.len() == 0;
    }
}

impl<'ast> ZGen<'ast> {
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
        blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_init_stmt("%SP", &Ty::Field)));
        // Initialize %BP
        blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_init_stmt("%BP", &Ty::Field)));
        // Initialize %TS for memory timestamp
        blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_init_stmt("%TS", &Ty::Field)));
        // Initialize %AS for allocating arrays
        blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_init_stmt("%AS", &Ty::Field)));

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
            let mut ret_ty = self.type_impl_::<false>(&ret_type)?;
            // If return type is an array, convert it to a pointer
            if let Ty::Array(_, _) = ret_ty {
                ret_ty = Ty::Field;
            }
            let ret_type = ty_to_type(&ret_ty)?;

            // Create new Block, initial scope is 0
            blks.push(Block::new(blks_len, 1, f_name.to_string(), 0));
            blks_len += 1;

            // Every time a variable is assigned a value at a specific scope, it receives a new version number
            // Use var_scope_info to record the version number of each (var_name, fn_name) at each scope
            let mut var_scope_info: VarScopeInfo = VarScopeInfo::new();
            for p in f.parameters.clone().into_iter() {
                let p_id = p.id.value.clone();
                let p_ty = self.type_impl_::<false>(&p.ty)?;
                // if p_ty is an array, convert p_ty to a field (pointer)
                if let Ty::Array(_, entry_ty) = p_ty {
                    let p_extended_id = var_scope_info.declare_var(&p_id, &f_name, 0, Ty::Field);
                    var_scope_info.arr_map.insert(p_extended_id.clone(), *entry_ty.clone());
                } else {
                    var_scope_info.declare_var(&p_id, &f_name, 0, p_ty);
                }
                inputs.push(var_scope_info.reference_var(&p_id, &f_name)?.clone());     
            }

            // Iterate through Stmts
            for s in &f.statements {
                // All statements at function level have scope 0
                (blks, blks_len, var_scope_info) = self.bl_gen_stmt_::<IS_MAIN>(blks, blks_len, s, &ret_type, &f_name, var_scope_info, 1, 0)?;
            }

            // Set terminator to ProgTerm if in main, point to %RP otherwise
            if IS_MAIN {
                blks[blks_len - 1].terminator = BlockTerminator::ProgTerm;
            } else {
                blks[blks_len - 1].terminator = BlockTerminator::Transition(bl_coda(NextBlock::Rp));
            }
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

            // Push %RP onto the stack if not in main
            if !IS_MAIN {
                // push %BP onto STACK
                blks[blks_len - 1].instructions.push(BlockContent::MemPush(("%BP".to_string(), Ty::Field, 0)));
                // %BP = %SP
                let bp_update_stmt = Statement::Definition(DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                        array_metadata: None,
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
                let mut p_ty = self.type_impl_::<false>(&p.ty)?;
                if let Ty::Array(_, _) = p_ty {
                    p_ty = Ty::Field;
                }
                let param_stmt = Statement::Definition(DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                        array_metadata: None,
                        ty: ty_to_type(&p_ty)?,
                        identifier: IdentifierExpression {
                            value: var_scope_info.declare_var(&p_id, &f_name, 0, p_ty),
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
                    array_metadata: None,
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
            if !IS_MAIN {
                blks[blks_len - 1].instructions.push(BlockContent::MemPop(("%RP".to_string(), Ty::Field, 1)));
                blks[blks_len - 1].instructions.push(BlockContent::MemPop(("%BP".to_string(), Ty::Field, 0)));
            }

            // Store Return value to a temporary variable "ret@X"
            let ret_type = self
                .functions
                .get(&f_path)
                .ok_or_else(|| format!("No file '{:?}' attempting fn call", &f_path))?
                .get(&f_name)
                .ok_or_else(|| format!("No function '{}' attempting fn call", &f_name))?
                .returns
                .first().ok_or("No return type provided for one or more function")?;
            let mut ret_ty = self.type_impl_::<false>(&ret_type)?;
            // If return type is an array, convert it to a pointer
            if let Ty::Array(_, _) = ret_ty {
                ret_ty = Ty::Field;
            }

            let ret_name = format!("ret@{}", func_count);
            let ret_extended_name = var_scope_info.declare_var(&ret_name, &caller_name, caller_scope, ret_ty.clone());
            let update_ret_stmt = Statement::Definition(DefinitionStatement {
                lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                    array_metadata: None,
                    ty: ty_to_type(&ret_ty)?,
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
        ret_ty: &Type<'ast>,
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
                let array_init_info: ArrayInitInfo;
                (blks, blks_len, var_scope_info, ret_expr, _, _, array_init_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &r.expressions[0], f_name, 0, 0, var_scope_info)?;
                if !array_init_info.is_empty() { panic!("Inline array inside return statements not supported!") }
                let ret_stmt = Statement::Definition(DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                        array_metadata: None,
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
                let array_init_info: ArrayInitInfo;
                (blks, blks_len, var_scope_info, asst_expr, _, _, array_init_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &a.expression, f_name, 0, 0, var_scope_info)?;
                if !array_init_info.is_empty() { panic!("Inline array inside assertion statements not supported!") }
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
                let new_v_name = var_scope_info.declare_var(&v_name, f_name, cur_scope, ty);

                let from_expr: Expression;
                let mut array_init_info: ArrayInitInfo;
                (blks, blks_len, var_scope_info, from_expr, _, _, array_init_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &it.from, f_name, 0, 0, var_scope_info)?;
                if !array_init_info.is_empty() { panic!("From expr of for loops cannot be inline array!") }
                let to_expr: Expression;
                (blks, blks_len, var_scope_info, to_expr, _, _, array_init_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &it.to, f_name, 0, 0, var_scope_info)?;
                if !array_init_info.is_empty() { panic!("To expr of for loops cannot be inline array!") }

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
                        array_metadata: None,
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
                        array_metadata: None,
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
                let array_init_info: ArrayInitInfo;
                (blks, blks_len, var_scope_info, cond_expr, _, _, array_init_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &w.condition, f_name, 0, 0, var_scope_info)?;
                if !array_init_info.is_empty() { panic!("Inline array inside while loop condition not supported!") }

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
                let array_init_info: ArrayInitInfo;
                (blks, blks_len, var_scope_info, cond_expr, _, _, array_init_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &c.condition, f_name, 0, 0, var_scope_info)?;
                if !array_init_info.is_empty() { panic!("Inline array inside branch condition not supported!!") }

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
                let array_init_info: ArrayInitInfo;
                (blks, blks_len, var_scope_info, rhs_expr, _, _, array_init_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &d.expression, f_name, 0, 0, var_scope_info)?;
                
                // RHS is array, if array_init_info is defined
                if !array_init_info.is_empty() {
                    if let Some(l) = d.lhs.first() {
                        let (lhs_id, is_declare) = match l {
                            TypedIdentifierOrAssignee::TypedIdentifier(l) => {
                                let decl_ty = self.type_impl_::<false>(&l.ty)?;

                                // Unroll scoping on LHS
                                let arr_name = &l.identifier.value;
                                // Add the identifier to current scope, declared as Field (pointer)
                                let arr_extended_name = var_scope_info.declare_var(arr_name, f_name, cur_scope, Ty::Field);
                                // Declare array
                                if let Ty::Array(size, entry_ty) = decl_ty {
                                    blks[blks_len - 1].instructions.push(BlockContent::ArrayInit((arr_extended_name.clone(), *entry_ty.clone(), size)));
                                    var_scope_info.arr_map.insert(arr_extended_name.clone(), *entry_ty.clone());
                                }

                                (arr_extended_name, true)
                            }
                            TypedIdentifierOrAssignee::Assignee(l) => {
                                // Array is already declared
                                let arr_extended_name = var_scope_info.reference_var(&l.id.value.clone(), f_name)?.0;
                                (arr_extended_name, false)
                            }
                        };
                        (blks, blks_len, var_scope_info) = self.bl_gen_array_init_(blks, blks_len, lhs_id, f_name, array_init_info, var_scope_info, is_declare)?;
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
                                let (new_l, lhs_ty) = var_scope_info.reference_var(&l.id.value.clone(), f_name)?;

                                let new_id = IdentifierExpression {
                                    value: new_l.clone(),
                                    span: Span::new("", 0, 0).unwrap()
                                };

                                // if the LHS is an array member, convert the assignee to a store
                                if let Some(entry_ty) = var_scope_info.arr_map.get(&new_l) {
                                    let entry_ty = entry_ty.clone();
                                    assignee_is_store = true;
                                    if l.accesses.len() != 1 { return Err(format!("Assignment to multiple array entries unsupported")); }
                                    if let AssigneeAccess::Select(a) = &l.accesses[0] {
                                        if let RangeOrExpression::Expression(e) = &a.expression {
                                            let new_e: Expression;
                                            let tmp_arr_info: ArrayInitInfo;
                                            (blks, blks_len, var_scope_info, new_e, _, _, tmp_arr_info) = 
                                                self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &e, f_name, 0, 0, var_scope_info)?;
                                            if !tmp_arr_info.is_empty() { panic!("Currently do not support array initialization inside array indices") }
                                            blks[blks_len - 1].instructions.push(BlockContent::Store((rhs_expr.clone(), entry_ty.clone(), new_l, new_e, false)));
                                            blks[blks_len - 1].num_vm_ops += 1;
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
                                        array_metadata: None,
                                        ty: ty_to_type(&lhs_ty)?,
                                        identifier: new_id.clone(),
                                        span: Span::new("", 0, 0).unwrap()
                                    })];
                                }
                            }
                            TypedIdentifierOrAssignee::TypedIdentifier(l) => {
                                let mut decl_ty = self.type_impl_::<false>(&l.ty)?;
                                let id = &l.identifier.value;

                                // If LHS is an array declaration but RHS is not an array, 
                                // first declare LHS as an array
                                // then convert LHS to a pointer
                                let new_l = {
                                    if let Ty::Array(_, entry_ty) = decl_ty {
                                        let new_l = var_scope_info.declare_var(id, f_name, cur_scope, Ty::Field);
                                        var_scope_info.arr_map.insert(new_l.clone(), *entry_ty.clone());
                                        decl_ty = Ty::Field;
                                        new_l
                                    } else {
                                        // Unroll scoping on LHS
                                        var_scope_info.declare_var(id, f_name, cur_scope, decl_ty.clone())
                                    }
                                };

                                let new_id = IdentifierExpression {
                                    value: new_l,
                                    span: Span::new("", 0, 0).unwrap()
                                };

                                // Convert the assignee to a declaration
                                lhs_expr = vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                                    array_metadata: None,
                                    ty: ty_to_type(&decl_ty)?,
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
            Statement::Witness(_) => { panic!("Witness statements unsupported.") }
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
    ) -> Result<(Vec<Block>, usize, VarScopeInfo, Expression, usize, usize, ArrayInitInfo), String> {
        debug!("Block Gen Expr: {}", e.span().as_str());

        let mut ret_e = e.clone();
        // All (index, value) pair for array initialization, currently cannot be put inside any other expression
        let mut array_init_info = ArrayInitInfo::new();

        match e {
            Expression::Ternary(t) => {
                let mut tmp_arr_info: ArrayInitInfo;
                let new_e_first: Expression;
                let new_e_second: Expression;
                let new_e_third: Expression;
                (blks, blks_len, var_scope_info, new_e_first, func_count, load_count, tmp_arr_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &t.first, f_name, func_count, load_count, var_scope_info)?;
                if !tmp_arr_info.is_empty() { panic!("Currently do not support array initialization inside ternary expressions") }
                (blks, blks_len, var_scope_info, new_e_second, func_count, load_count, tmp_arr_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &t.second, f_name, func_count, load_count, var_scope_info)?;
                if !tmp_arr_info.is_empty() { panic!("Currently do not support array initialization inside ternary expressions") }
                (blks, blks_len, var_scope_info, new_e_third, func_count, load_count, tmp_arr_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &t.third, f_name, func_count, load_count, var_scope_info)?;
                if !tmp_arr_info.is_empty() { panic!("Currently do not support array initialization inside ternary expressions") }
                ret_e = Expression::Ternary(TernaryExpression {
                    first: Box::new(new_e_first),
                    second: Box::new(new_e_second),
                    third: Box::new(new_e_third),
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::Binary(b) => {
                let mut tmp_arr_info: ArrayInitInfo;
                let new_e_left: Expression;
                let new_e_right: Expression;
                (blks, blks_len, var_scope_info, new_e_left, func_count, load_count, tmp_arr_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &b.left, f_name, func_count, load_count, var_scope_info)?;
                if !tmp_arr_info.is_empty() { panic!("Currently do not support array initialization inside binary expressions") }
                (blks, blks_len, var_scope_info, new_e_right, func_count, load_count, tmp_arr_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &b.right, f_name, func_count, load_count, var_scope_info)?;
                if !tmp_arr_info.is_empty() { panic!("Currently do not support array initialization inside binary expressions") }
                ret_e = Expression::Binary(BinaryExpression {
                    op: b.op.clone(),
                    left: Box::new(new_e_left),
                    right: Box::new(new_e_right),
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::Unary(u) => {
                let tmp_arr_info: ArrayInitInfo;
                let new_e_expr: Expression;
                (blks, blks_len, var_scope_info, new_e_expr, func_count, load_count, tmp_arr_info) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &u.expression, f_name, func_count, load_count, var_scope_info)?;
                if !tmp_arr_info.is_empty() { panic!("Currently do not support array initialization inside unary expressions") }
                ret_e = Expression::Unary(UnaryExpression {
                    op: u.op.clone(),
                    expression: Box::new(new_e_expr),
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::Postfix(p) => {
                // assume no functions in arrays, etc.
                assert!(!p.accesses.is_empty());
                match p.accesses.first() {
                    Some(Access::Call(c)) => {
                        let (callee_path, callee_name) = self.deref_import(&p.id.value);
                        let mut args: Vec<Expression> = Vec::new();
                        let mut new_expr: Expression;
                        let mut tmp_arr_info: ArrayInitInfo;
                        for old_expr in &c.arguments.expressions {
                            (blks, blks_len, var_scope_info, new_expr, func_count, load_count, tmp_arr_info) = 
                                self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, old_expr, f_name, func_count, load_count, var_scope_info)?;
                            if !tmp_arr_info.is_empty() { panic!("Currently do not support array initialization inside function calls") }
                            args.push(new_expr);                       
                        }
     
                        // Do the function call
                        (blks, blks_len, _, var_scope_info, func_count) =
                            self.bl_gen_function_call_::<IS_MAIN>(blks, blks_len, args, callee_path.clone(), callee_name.clone(), func_count, var_scope_info)?;
    
                        let ret_name = format!("ret@{}", func_count);
                        let ret_extended_name = var_scope_info.reference_var(&ret_name, f_name)?.0;
                        ret_e = Expression::Identifier(IdentifierExpression {
                            value: ret_extended_name,
                            span: Span::new("", 0, 0).unwrap()
                        });
                        func_count += 1;
                    }
                    Some(Access::Select(s)) => {
                        if let RangeOrExpression::Expression(e) = &s.expression {
                            // Store the loaded value in a separate variable and return it
                            let load_name = format!("load@{}", load_count);
                            let arr_name = &p.id.value;
                            let arr_extended_name = var_scope_info.reference_var(&arr_name, f_name)?.0;
                            let load_ty = var_scope_info.arr_map.get(&arr_extended_name).ok_or_else(|| format!("Load failed: no array {}", &arr_extended_name))?.clone();
                            let cur_scope = blks[blks_len - 1].scope;
                            let load_extended_name = var_scope_info.declare_var(&load_name, &f_name, cur_scope, load_ty.clone());
                            
                            // Preprocess the indices
                            let new_e: Expression;
                            let tmp_arr_info: ArrayInitInfo;
                            (blks, blks_len, var_scope_info, new_e, _, _, tmp_arr_info) = 
                                self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &e, f_name, 0, 0, var_scope_info)?;
                            if !tmp_arr_info.is_empty() { panic!("Currently do not support array initialization inside array indices") }
                            blks[blks_len - 1].instructions.push(BlockContent::Load((load_extended_name.clone(), load_ty.clone(), arr_extended_name.clone(), new_e)));
                            blks[blks_len - 1].num_vm_ops += 1;
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
                let new_var: String = var_scope_info.reference_var(&i.value.clone(), &f_name)?.0;
                ret_e = Expression::Identifier(IdentifierExpression {
                    value: new_var,
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::Literal(_) => {}
            Expression::ArrayInitializer(ai) => {
                let arr_size: usize = const_int(self.expr_impl_::<false>(&ai.count)?)?.try_into().unwrap();
                let new_ai_value: Expression;
                (blks, blks_len, var_scope_info, new_ai_value, func_count, load_count, _) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &ai.value, f_name, func_count, load_count, var_scope_info)?;
                array_init_info = ArrayInitInfo::from_array_initializer(new_ai_value, arr_size);
            }
            Expression::InlineArray(ia) => {
                let mut new_e_list = Vec::new();
                for se in &ia.expressions {
                    if let SpreadOrExpression::Expression(e) = se {
                        let tmp_arr_info: ArrayInitInfo;
                        let new_e: Expression;
                        (blks, blks_len, var_scope_info, new_e, func_count, load_count, tmp_arr_info) = 
                            self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &e, f_name, func_count, load_count, var_scope_info)?;
                        if !tmp_arr_info.is_empty() { panic!("Currently do not support array initialization inside inline arrays") }
                        new_e_list.push(new_e);
                    } else {
                        return Err(format!("Spread not supported in inline arrays!"));
                    }
                }
                array_init_info = ArrayInitInfo::from_inline_array(new_e_list);
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
        f_name: &str,
        array_init_info: ArrayInitInfo<'ast>,
        mut var_scope_info: VarScopeInfo,
        is_declare: bool // if is_declare, then array is being initialized
    ) -> Result<(Vec<Block>, usize, VarScopeInfo), String> {
        let entry_ty = var_scope_info.arr_map.get(&arr_extended_name).ok_or_else(|| format!("Assignment failed: no array {}", &arr_extended_name))?.clone();
        let cur_scope = blks[blks_len - 1].scope;

        // Start by declaring all init@X to unique_contents
        for i in 0..array_init_info.unique_contents.len() {
            let init_name = format!("init@{}", i);
            let init_extended_name = var_scope_info.declare_var(&init_name, &f_name, cur_scope, entry_ty.clone());
            let entry_ty = ty_to_type(&entry_ty)?;
            let array_init_stmt = Statement::Definition(DefinitionStatement {
                lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                    array_metadata: None,
                    ty: entry_ty,
                    identifier: IdentifierExpression {
                        value: init_extended_name.clone(),
                        span: Span::new("", 0, 0).unwrap()
                    },
                    span: Span::new("", 0, 0).unwrap()
                })],
                // Assume that we only have ONE return variable
                expression: array_init_info.unique_contents[i].clone(),
                span: Span::new("", 0, 0).unwrap()
            });
            blks[blks_len - 1].instructions.push(BlockContent::Stmt(array_init_stmt));
        }

        // Then assigning each entries in array to corresponding init@X
        let mut index = 0;
        for entry in array_init_info.arr_entries {
            let entry_name = format!("init@{}", entry);
            let entry_extended_name = var_scope_info.reference_var(&entry_name, &f_name)?.0;
            let entry_expr = Expression::Identifier(IdentifierExpression {
                value: entry_extended_name,
                span: Span::new("", 0, 0).unwrap()
            });

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
            blks[blks_len - 1].instructions.push(BlockContent::Store((entry_expr, entry_ty.clone(), arr_extended_name.clone(), index_expr, is_declare)));
            blks[blks_len - 1].num_vm_ops += 1;
            index += 1;
        }
        Ok((blks, blks_len, var_scope_info))
    }

    fn bl_gen_enter_scope_(
        &'ast self,
        cur_scope: usize,
    ) -> Result<usize, String> {
        // New Scoping
        Ok(cur_scope + 1)
    }

    fn bl_gen_exit_scope_(
        &'ast self,
        mut var_scope_info: VarScopeInfo,
        fn_name: &str,
        cur_scope: usize,
    ) -> Result<(VarScopeInfo, usize), String> {
        // Exit Scoping
        var_scope_info.exit_scope(fn_name, cur_scope);
        Ok((var_scope_info, cur_scope - 1))
    }

    // Convert a list of blocks to circ_ir
    pub fn bls_to_circ(&'ast self, blks: &Vec<Block>) {
        for b in blks {
            let f = &format!("Block_{}", b.name);
            self.circ_init_block(f);
            self.bl_to_circ::<false>(&b, f);
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
        self.assert(b).unwrap();
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
        self.assert(b).unwrap();
    }

    /*
    // Convert a virtual memory operation to circ_ir
    // MODE: LOAD, STORE, DUMMY_LOAD, INIT_STORE
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

        // RETRIEVAL
        // For LOAD, this is to obtain the value
        // For STORE, this is to obtain the physical memory
        // For DUMMY_LOAD, this does nothing
        // For INIT_STORE, skip
        if MODE == LOAD || MODE == STORE || MODE == DUMMY_LOAD {
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
        }

        // INCREMENT TIMESTAMP
        if MODE == STORE || MODE == INIT_STORE {
            self.stmt_impl_::<false>(&bl_gen_increment_stmt("%w1", 1)).unwrap();
        }

        // INVALIDATION
        if MODE == STORE || MODE == DUMMY_LOAD {
            // Increment label
            next_label += 1;

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


            // If STORE, PHY_ADDR matches with previous LOAD and VIR_ADDR is 0
            if MODE == STORE {
                self.bl_gen_assert_eq(&format!("%vm{:06}a", next_label - 1), &format!("%vm{:06}a", next_label));
                self.bl_gen_assert_const(&format!("%vm{:06}b", next_label), 0);
            }
            // LS
            self.bl_gen_assert_const(&format!("%vm{:06}l", next_label), if MODE == STORE { STORE } else { LOAD });
            // TS
            self.bl_gen_assert_eq(&format!("%w1"), &format!("%vm{:06}t", next_label));

            // Increment next_label
            next_label += 1;
        }
        
        // ALLOCATION
        if MODE == STORE || MODE == DUMMY_LOAD || MODE == INIT_STORE {
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

            // If STORE or INIT_STORE, PHY_ADDR matches with TS
            if MODE == STORE || MODE == INIT_STORE {
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
            self.bl_gen_assert_const(&format!("%vm{:06}l", next_label), if MODE == STORE || MODE == INIT_STORE { STORE } else { LOAD });
            // TS
            self.bl_gen_assert_eq(&format!("%w1"), &format!("%vm{:06}t", next_label));
        }
        // VAL is handled individually depending on LOAD & STORE

        // Update label
        ty_mem_op_offset.insert(ty.clone(), next_label + 1);

        (ty_mem_op_offset, next_label)
    }
    */

    // Convert a virtual memory operation to circ_ir
    // MODE: LOAD, STORE, DUMMY_LOAD, INIT_STORE
    fn vir_mem_to_circ<const MODE: usize>(
        &'ast self,
        vir_mem_op_count: usize,
        arr: Option<&String>,
        id_expr: Option<&Expression<'ast>>,
    ) {
        // ADDR if exist
        if let Some(addr_expr) = id_expr {
            // lhs_t + offset_t == rhs_t
            let mut lhs_t = self.expr_impl_::<false>(&addr_expr).unwrap();
            // if lhs_t is not a field, cast it to a field
            if lhs_t.type_() != &Ty::Field {
                lhs_t = uint_to_field(lhs_t).unwrap();
            }
            let offset_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                value: arr.unwrap().to_string(),
                span: Span::new("", 0, 0).unwrap()
            })).unwrap();
            let rhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                value: format!("%vm{:06}a", vir_mem_op_count),
                span: Span::new("", 0, 0).unwrap()
            })).unwrap();
            let b = bool(eq(add(lhs_t, offset_t).unwrap(), rhs_t).unwrap()).unwrap();
            self.assert(b).unwrap();
        }
        // LS
        let ls = if MODE == STORE || MODE == INIT_STORE { STORE } else { LOAD };
        self.bl_gen_assert_const(&format!("%vm{:06}l", vir_mem_op_count), ls);
        // TS, increment if STORE
        if MODE == STORE {
            self.stmt_impl_::<false>(&bl_gen_increment_stmt(W_TS, 1)).unwrap();
        }
        self.bl_gen_assert_eq(&W_TS, &format!("%vm{:06}t", vir_mem_op_count));
        // DATA is updated individually by LOAD or STORE
    }

    pub fn inst_to_circ<const ESTIMATE: bool>(&self, 
        i: &BlockContent, 
        f: &str,
        mut phy_mem_op_count: usize,
        mut vir_mem_op_count: usize
    ) -> (usize, usize) {
        match i {
            BlockContent::MemPush((var, _, offset)) => {
                // Non-deterministically supply ADDR
                self.circ_declare_input(
                    &f,
                    format!("%pm{:06}a", phy_mem_op_count),
                    &Ty::Field,
                    ZVis::Private(0),
                    None,
                    true,
                    &None,
                ).unwrap();
                // Non-deterministically supply VAL
                self.circ_declare_input(
                    &f,
                    format!("%pm{:06}v", phy_mem_op_count),
                    &Ty::Field,
                    ZVis::Private(0),
                    None,
                    true,
                    &None,
                ).unwrap();
                // Assert correctness of address
                let lhs_t = self.expr_impl_::<false>(&Expression::Binary(BinaryExpression {
                    op: BinaryOperator::Add,
                    left: Box::new(Expression::Identifier(IdentifierExpression {
                        // %SP
                        value: if ESTIMATE { "%SP".to_string() } else { W_SP.to_string() },
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
                self.assert(b).unwrap();
                // Assert correctness of value
                let mut lhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                    value: var.to_string(),
                    span: Span::new("", 0, 0).unwrap()
                })).unwrap();
                // Store the value as Field
                if lhs_t.type_() != &Ty::Field {
                    lhs_t = uint_to_field(lhs_t).unwrap();
                }
                let rhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                    value: format!("%pm{:06}v", phy_mem_op_count),
                    span: Span::new("", 0, 0).unwrap()
                })).unwrap();
                let b = bool(eq(lhs_t, rhs_t).unwrap()).unwrap();
                self.assert(b).unwrap();
                phy_mem_op_count += 1;
            }
            BlockContent::MemPop((var, ty, offset)) => {
                // Non-deterministically supply ADDR and VAL in memory
                self.circ_declare_input(
                    &f,
                    format!("%pm{:06}a", phy_mem_op_count),
                    &Ty::Field,
                    ZVis::Private(0),
                    None,
                    true,
                    &None,
                ).unwrap();
                self.circ_declare_input(
                    &f,
                    format!("%pm{:06}v", phy_mem_op_count),
                    &Ty::Field,
                    ZVis::Private(0),
                    None,
                    true,
                    &None,
                ).unwrap();
                // Assert correctness of address
                let lhs_t = self.expr_impl_::<false>(&Expression::Binary(BinaryExpression {
                    op: BinaryOperator::Add,
                    left: Box::new(Expression::Identifier(IdentifierExpression {
                        // %BP
                        value: if ESTIMATE { "%BP".to_string() } else { W_BP.to_string() },
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
                self.assert(b).unwrap();
                // Assign POP value to val
                let mut e = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                    value: format!("%pm{:06}v", phy_mem_op_count),
                    span: Span::new("", 0, 0).unwrap()
                })).unwrap();
                // Convert the loaded value to the correct type
                e = field_to_ty(e, &ty).unwrap();
                self.declare_init_impl_::<false>(
                    var.clone(),
                    ty.clone(),
                    e,
                ).unwrap();
                phy_mem_op_count += 1;  
            }
            BlockContent::ArrayInit((arr, _, _)) => {
                if ESTIMATE {
                    self.circ_declare_input(
                        &f,
                        arr.to_string(),
                        &Ty::Field,
                        ZVis::Private(0),
                        None,
                        true,
                        &None,
                    ).unwrap();
                }
            }
            BlockContent::Store((val_expr, _, arr, id_expr, init)) => {
                if ESTIMATE {}
                else {
                    // ADDR, LS, & TS
                    if *init {
                        self.vir_mem_to_circ::<INIT_STORE>(
                            vir_mem_op_count,
                            Some(&arr),
                            Some(&id_expr)
                        );
                    } else {
                        self.vir_mem_to_circ::<STORE>(
                            vir_mem_op_count,
                            Some(&arr),
                            Some(&id_expr)
                        );
                    }
                    // Assert correctness of DATA, always stored as Field
                    let mut lhs_t = self.expr_impl_::<false>(&val_expr).unwrap();
                    if lhs_t.type_() != &Ty::Field {
                        lhs_t = uint_to_field(lhs_t).unwrap();
                    }
                    let rhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                        value: format!("%vm{:06}d", vir_mem_op_count),
                        span: Span::new("", 0, 0).unwrap()
                    })).unwrap();
                    let b = bool(eq(lhs_t, rhs_t).unwrap()).unwrap();
                    self.assert(b).unwrap();
                    // Update Label
                    vir_mem_op_count += 1;
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
                        &None,
                    );
                    r.unwrap();
                } else {
                    // ADDR, LS, & TS
                    self.vir_mem_to_circ::<LOAD>(
                        vir_mem_op_count,
                        Some(&arr),
                        Some(&id_expr)
                    );
                    // Assign LOAD value to data
                    let mut e = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                        value: format!("%vm{:06}d", vir_mem_op_count),
                        span: Span::new("", 0, 0).unwrap()
                    })).unwrap();
                    // Convert the loaded value to the correct type
                    e = field_to_ty(e, &ty).unwrap();
                    self.declare_init_impl_::<false>(
                        val.clone(),
                        ty.clone(),
                        e,
                    ).unwrap();
                    vir_mem_op_count += 1;
                }
            }
            BlockContent::DummyLoad() => {
                // ADDR, LS, & TS
                self.vir_mem_to_circ::<DUMMY_LOAD>(
                    vir_mem_op_count,
                    None,
                    None
                );
                vir_mem_op_count += 1;
            }
            BlockContent::Branch((cond, if_insts, else_insts)) => {
                let cond = self.expr_impl_::<false>(&cond).unwrap();
                let cbool = bool(cond.clone()).unwrap();

                // Mem_ops overlap in two branches
                let mut if_phy_mem_op_count = phy_mem_op_count;
                let mut if_vir_mem_op_count = vir_mem_op_count;
                let mut else_phy_mem_op_count = phy_mem_op_count;
                let mut else_vir_mem_op_count = vir_mem_op_count;

                self.circ_enter_condition(cbool.clone());
                for i in if_insts {
                    (if_phy_mem_op_count, if_vir_mem_op_count) = self.inst_to_circ::<ESTIMATE>(i, f, if_phy_mem_op_count, if_vir_mem_op_count);
                }
                self.circ_exit_condition();
                self.circ_enter_condition(term![NOT; cbool]);
                for i in else_insts {
                    (else_phy_mem_op_count, else_vir_mem_op_count) = self.inst_to_circ::<ESTIMATE>(i, f, else_phy_mem_op_count, else_vir_mem_op_count);
                }
                self.circ_exit_condition();

                // No phy_op should every occur in branches, and the same amount of vir_op should occur in two branches
                assert_eq!(if_phy_mem_op_count, phy_mem_op_count);
                assert_eq!(else_phy_mem_op_count, phy_mem_op_count);
                assert_eq!(if_vir_mem_op_count, else_vir_mem_op_count);

                phy_mem_op_count = if_phy_mem_op_count;
                vir_mem_op_count = if_vir_mem_op_count;
            }
            BlockContent::Stmt(stmt) => { self.stmt_impl_::<false>(&stmt).unwrap(); }
        }
        (phy_mem_op_count, vir_mem_op_count)
    }

    // Convert a block to circ_ir
    // This can be done to either produce the constraints, or to estimate the size of constraints
    // In estimation mode, we rename all output variable from X -> oX, add assertion, and process the terminator
    pub fn bl_to_circ<const ESTIMATE: bool>(&self, b: &Block, f: &str) {
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
                    &None,
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
                        &None,
                    );
                    r.unwrap();
                }
            }
        }

        // How many scoping memory operations have we encountered?
        let mut phy_mem_op_count = 0;
        // How many virtual memory operations have we encountered?
        let mut vir_mem_op_count = 0;
        
        // Declare all virtual memory accesses to avoid dealing with branching
        for i in 0..b.num_vm_ops {
            // Declare the next ADDR, DATA, L/S, and TS
            // VIR_ADDR as 'a'
            self.circ_declare_input(
                f,
                format!("%vm{:06}a", i),
                &Ty::Field,
                ZVis::Private(0),
                None,
                true,
                &None,
            ).unwrap();
            // VAL as 'd'
            self.circ_declare_input(
                f,
                format!("%vm{:06}d", i),
                &Ty::Field,
                ZVis::Private(0),
                None,
                true,
                &None,
            ).unwrap();
            // LS as 'l'
            self.circ_declare_input(
                f,
                format!("%vm{:06}l", i),
                &Ty::Field,
                ZVis::Private(0),
                None,
                true,
                &None,
            ).unwrap();
            // TS as 't'
            self.circ_declare_input(
                f,
                format!("%vm{:06}t", i),
                &Ty::Field,
                ZVis::Private(0),
                None,
                true,
                &None,
            ).unwrap();
        }

        // Iterate over instructions, convert memory accesses into statements and then IR
        for i in &b.instructions {
            (phy_mem_op_count, vir_mem_op_count) = self.inst_to_circ::<ESTIMATE>(i, f, phy_mem_op_count, vir_mem_op_count);
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
                        &None,
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
                &None,
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
                        .circ_declare_input(&f, name, ty, ZVis::Public, Some(ret_val.clone()), false, &None)
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