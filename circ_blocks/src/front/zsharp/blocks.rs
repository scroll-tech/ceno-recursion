// TODO: Recursion is not supported.
//       Generics are not supported.
//       Loop breaks are not supported.
//       Structs are not supported.
//       Multi-file program not supported
//       Can try eliminate ternaries with a constant condition
//       What would happen if block 0 is a loop to itself? Many analyses would break down!!!

use blocks_optimization::bl_trans_map;
use blocks_optimization::rp_replacement_stmt;
use log::debug;

use zokrates_pest_ast::*;
use crate::front::field_list::FieldList;
use crate::front::zsharp::ZGen;
use crate::front::zsharp::Ty;
use crate::front::zsharp::PathBuf;
use crate::front::zsharp::pretty::*;
use std::collections::{HashMap, BTreeMap, BTreeSet};
use std::convert::TryInto;
use crate::front::zsharp::*;

const STORE: usize = 0;
const LOAD: usize = 1;
const INIT_STORE: usize = 2;
const DUMMY_LOAD: usize = 3;

const W_TS: &str = "%w1";
const W_AS: &str = "%w2";
const W_SP: &str = "%w3";
const W_BP: &str = "%w4";

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

pub fn ty_to_dec_suffix<'ast>(ty: &Type<'ast>) -> DecimalSuffix<'ast> {
    let span = Span::new("", 0, 0).unwrap();
    match ty {
        Type::Basic(BasicType::Field(_)) => { DecimalSuffix::Field(FieldSuffix { span }) }
        Type::Basic(BasicType::U8(_)) => { DecimalSuffix::U8(U8Suffix { span }) }
        Type::Basic(BasicType::U16(_)) => { DecimalSuffix::U16(U16Suffix { span }) }
        Type::Basic(BasicType::U32(_)) => { DecimalSuffix::U32(U32Suffix { span }) }
        Type::Basic(BasicType::U64(_)) => { DecimalSuffix::U64(U64Suffix { span }) }
        _ => { panic!("Type not supported for loop iterator: {:?}.", ty) }
    }
}

pub fn ty_to_type<'ast>(ty: &Ty) -> Result<Type<'ast>, String> {
    debug!("Ty to type: {:?}", ty);

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
        Ty::Field | Ty::Array(..) => Ok(Type::Basic(BasicType::Field(FieldType {
            span: Span::new("", 0, 0).unwrap()
        }))),
        _ => Err(format!("Type not supported: {:?}", ty))
    }
}

// Convert a field into other types, used for LOADs
fn field_to_ty(f: T, ty: &Ty) -> Result<T, String> {
    match ty {
        Ty::Uint(n) => Ok(T::new(Ty::Uint(*n), term![Op::PfToBv(*n); f.term])),
        Ty::Bool => field_to_bool(f),
        Ty::Field => Ok(f),
        _ => Err(format!("Type not supported: {:?}", ty))
    }
}

// Given a (potentially struct) type and access pattern,
// return size of type (# of fields to express it) and offset to the access
fn access_to_offset(ty: &Ty, acc: &[MemberAccess]) -> (usize, usize){
    if let Ty::Struct(_, members) = ty {
        let mut size = 0;
        let mut offset = size;
        // if acc_encountered is true, then offset no longer increases
        let mut acc_encountered = acc.len() == 0;
        for m_name in members.org_fields() {
            let m_ty = members.search(m_name).unwrap().1;
            if acc.len() > 0 && &acc[0].id.value == m_name {
                let (m_size, m_offset) = access_to_offset(m_ty, &acc[1..]);
                size += m_size;
                offset += m_offset;
                acc_encountered = true;
            } else {
                let (m_size, _) = access_to_offset(m_ty, &[]);
                size += m_size;
                if !acc_encountered { offset += m_size };
            }
        }
        assert!(acc_encountered);
        (size, offset)
    } 
    // All non-struct types have size 1
    else {
        return (1, 0);
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
        NextBlock::Rp(f_name) => Expression::Identifier(IdentifierExpression {
            value: format!("rp@.{}", f_name),
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
        expression: match ty {
            Ty::Bool => {
                Expression::Literal(LiteralExpression::BooleanLiteral(BooleanLiteralExpression {
                    value: "false".to_string(),
                    span: Span::new("", 0, 0).unwrap()
                }))
            },
            _ => {
                Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                    value: DecimalNumber {
                        value: "0".to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    },
                    suffix: Some(ty_to_dec_suffix(&typ)),
                    span: Span::new("", 0, 0).unwrap()
                }))
            }
        },
        span: Span::new("", 0, 0).unwrap()
    });
    var_init_stmt
}

// Generate the statement: var = var + offset
pub fn bl_gen_increment_stmt<'ast>(var: &str, offset: usize, ty: &Ty) -> Statement<'ast> {
    let typ = ty_to_type(ty).unwrap();
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
                suffix: Some(ty_to_dec_suffix(&typ)),
                span: Span::new("", 0, 0).unwrap()
            }))),
            span: Span::new("", 0, 0).unwrap()
        }),
        span: Span::new("", 0, 0).unwrap()
    });     
    var_update_stmt   
}

// Flatten out any struct in pre-order
pub fn flatten_var(var_name: &str, ty: &Ty, var_list: &mut Vec<(String, Ty)>) {
    if let Ty::Struct(_, members) = ty {
        for m in members.org_fields() {
            let m_ty = members.search(m).unwrap().1;
            let member_name = format!("{}^{}", var_name, m);
            flatten_var(&member_name, &m_ty, var_list);
        }
    } else {
        var_list.push((var_name.to_string(), ty.clone()));
    }
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
    // Number of read-only memory accesses
    pub num_ro_ops: usize,
    // Number of non-scoping-related memory accesses
    pub num_vm_ops: usize,
    // Name of the function the block is in
    pub fn_name: String,
    // Depth of the scope of the function
    pub scope: usize,
    // Number of (estimated) constraints generated by the block
    pub num_cons: usize,
}

#[derive(Clone, PartialEq, Debug)]
pub enum BlockContent<'ast> {
    //       val   type  liveness
    Witness((String, Ty, bool)), // Dead witnesses will still be provided by the prover, and thus liveness must be explicitly stated
    //       val   type  offset  
    MemPush((String, Ty, usize)), // %PHY[%SP + offset] = val
    MemPop((String, Ty, usize)),  // val = %PHY[%BP + offset]
    //          arr   type size_expr         read_only
    ArrayInit((String, Ty, Expression<'ast>, bool)), 
    //     val_expr         type   arr   id_expr           init?  read-only?
    Store((Expression<'ast>, Ty, String, Expression<'ast>, bool,  bool)), // arr[id] = val, if read-only then no timestamp & load/store
    //    var    type   arr   id_expr           read_only?
    Load((String, Ty, String, Expression<'ast>, bool)),  // val = arr[id], if read-only then no timestamp & load/store
    //        read_only?
    DummyLoad(bool),
    Branch((Expression<'ast>, Vec<BlockContent<'ast>>, Vec<BlockContent<'ast>>)),
    Stmt(Statement<'ast>) // other statements
}

#[derive(Clone)]
// Coda is the number of total types of blocks
pub enum BlockTerminator<'ast> {
    Transition(Expression<'ast>), // Expression that should be evaluated to either a const int or "rp@"
    FuncCall(String), // Placeholders before blocks corresponding to each function has been determined
    ProgTerm // The program terminates
}

#[derive(Clone, PartialEq)]
// The next block either has a usize label or is pointed by rp@
// Used to construct Block Transition
pub enum NextBlock {
    Label(usize),
    Rp(String) // String refer to the name of the CALLEE
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
            num_ro_ops: 0,
            num_vm_ops: 0,
            fn_name,
            scope,
            num_cons: 0,
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
            num_ro_ops: old_bl.num_ro_ops,
            num_vm_ops: old_bl.num_vm_ops,
            fn_name: old_bl.fn_name.clone(),
            scope: old_bl.scope,
            num_cons: old_bl.num_cons,
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
        self.num_ro_ops += succ.num_ro_ops;
        self.num_vm_ops += succ.num_vm_ops;
        // Add up number of constraints
        self.num_cons += succ.num_cons;
    }

    pub fn pretty(&self) {
        println!("\nBlock {}:", self.name);
        println!("Func: {}, Scope: {}", self.fn_name, self.scope);
        println!("Exec Bound: {}, While Loop: {}", self.fn_num_exec_bound, self.is_head_of_while_loop);
        println!("RO Ops: {}, VM Ops: {}", self.num_ro_ops, self.num_vm_ops);
        println!("Num Cons: {}", if self.num_cons == 0 { "-".to_string() } else { self.num_cons.to_string() });
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
    // Set of names of all of the constants
    constants: BTreeSet<(String, Ty)>,
}

impl VarScopeInfo {
    fn new() -> VarScopeInfo {
        VarScopeInfo {
            var_version: HashMap::new(),
            var_stack: HashMap::new(),
            constants: BTreeSet::new(),
        }
    }

    // Declare a variable in a given scope of a given function, return the new variable name
    // If the declared variable is a struct, declare itself and all members, return the new struct
    fn declare_var(&mut self, var_name: &str, fn_name: &str, cur_scope: usize, ty: Ty) -> String {
        let name = &(var_name.to_string(), fn_name.to_string());
        // Declare struct members
        if let Ty::Struct(_, members) = &ty {
            for (m, m_ty) in members.fields() {
                let member_name = format!("{}^{}", var_name, m);
                self.declare_var(&member_name, fn_name, cur_scope, m_ty.clone());
            }
        }
        // Declare self
        match self.var_stack.get(name) {
            Some(stack) => {
                assert!(stack.len() == 0 || stack[stack.len() - 1].0 <= cur_scope);
                // If stack[stack.len() - 1] == cur_scope, this is shadowing
                // allocate a new version if declared type does not match with existing type
                if stack.len() > 0 && stack[stack.len() - 1].0 == cur_scope {
                    if ty != stack[stack.len() - 1].1 {
                        let mut new_stack = stack.to_vec();
                        new_stack[stack.len() - 1].1 = ty;
                        let new_depth = new_stack.len() - 1;
                        let mut version_list = self.var_version.get(name).unwrap().to_vec();
                        version_list[new_depth] += 1;
                        self.var_version.insert(name.clone(), version_list);
                        self.var_stack.insert(name.clone(), new_stack);
                    }
                } else {
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
        // Check whether the variable is local
        if let Some(stack) = self.var_stack.get(&name) {
            let depth = stack.len() - 1;
            let version = self.var_version.get(&name).unwrap()[depth];
            let ty = stack[depth].1.clone();
            Ok((format!("{}.{}.{}.{}", var_name, fn_name, depth, version), ty))
        } else {
            Err(format!("reference_var failed: variable {} does not exist in function {}", var_name, fn_name))
        }
    }

    fn add_constant(&mut self, const_name: &str, const_ty: Ty) {
        self.constants.insert((const_name.to_string(), const_ty));
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
    // Is the initializer length runtime knowledge?
    // If dynamic, then unique_contents.len() == 1
    dynamic: bool,
    // All unique entries as expressions
    unique_contents: Vec<Expression<'ast>>,
    // Length expression of array, if dynamic
    dyn_length: Option<Expression<'ast>>,
    // Entries of the array, mapped to indices of unique_contents
    arr_entries: Option<Vec<usize>>,
    read_only: bool,
    entry_ty: Ty,
}

impl<'ast> ArrayInitInfo<'ast> {
    fn from_static_array_initializer(value: Expression<'ast>, arr_size: usize, read_only: bool, entry_ty: Ty) -> ArrayInitInfo<'ast> {
        ArrayInitInfo {
            dynamic: false,
            unique_contents: vec![value],
            dyn_length: None,
            arr_entries: Some(vec![0; arr_size]),
            read_only,
            entry_ty
        }
    }

    fn from_dyn_array_initializer(value: Expression<'ast>, dyn_arr_len: Expression<'ast>, read_only: bool, entry_ty: Ty) -> ArrayInitInfo<'ast> {
        ArrayInitInfo {
            dynamic: true,
            unique_contents: vec![value],
            dyn_length: Some(dyn_arr_len),
            arr_entries: None,
            read_only,
            entry_ty,
        }
    }

    fn from_inline_array(entries: Vec<Expression<'ast>>, read_only: bool, entry_ty: Ty) -> ArrayInitInfo<'ast> {
        let mut unique_contents = Vec::new();
        let mut arr_entries = Vec::new();
        for e in entries.into_iter() {
            unique_contents.push(e.clone());
            arr_entries.push(unique_contents.len() - 1);
        }
        ArrayInitInfo {
            dynamic: false,
            unique_contents,
            dyn_length: None,
            arr_entries: Some(arr_entries),
            read_only,
            entry_ty
        }
    }

    // Return array length as an expression
    fn len_as_expr(&self, const_ty: &Ty) -> Expression<'ast> {
        if self.dynamic {
            self.dyn_length.clone().unwrap()
        } else {
            let to_expr = Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                value: DecimalNumber {
                    value: self.arr_entries.clone().unwrap().len().to_string(),
                    span: Span::new("", 0, 0).unwrap()
                },
                suffix: Some(ty_to_dec_suffix(&ty_to_type(const_ty).unwrap())),
                span: Span::new("", 0, 0).unwrap()
            }));
            to_expr
        }
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
        // XXX: %SP is now a program input
        // blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_init_stmt("%SP", &Ty::Field)));
        // Initialize %BP
        blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_init_stmt("%BP", &Ty::Field)));
        // Initialize %TS for memory timestamp
        blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_init_stmt("%TS", &Ty::Field)));
        // Initialize %AS for allocating arrays
        // XXX: %AS is now a program input
        // blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_init_stmt("%AS", &Ty::Field)));

        // Create a mapping from each function name to (entry_bl, exit_bl, inline?)
        let mut func_blk_map: BTreeMap<String, (usize, usize, bool)> = BTreeMap::new();
        // Create global variable scope info
        let mut var_scope_info: VarScopeInfo = VarScopeInfo::new();
        // constants
        let files = &self.asts.iter().map(|(p, _)| p).collect();
        (blks, blks_len, var_scope_info) = self.bl_gen_constants(blks, blks_len, &files, var_scope_info)
            .unwrap_or_else(|e| panic!("gen_constants failed: {}", e));
        // main functions
        let inputs: Vec<(String, Ty)>;
        (blks, blks_len, inputs, var_scope_info) = self.bl_gen_function_init_::<true>(blks, blks_len, f_file.clone(), f_name, var_scope_info)
            .unwrap_or_else(|e| panic!("const_entry_fn failed: {}", e));

        func_blk_map.insert("main".to_string(), (0, blks_len - 1, false));
        // other functions
        for (func_file, funcs) in &self.functions {
            for (f_name, f) in funcs {
                if f_name != "main" {
                    let entry_bl = blks_len;
                    (blks, blks_len, _, var_scope_info) = self.bl_gen_function_init_::<false>(blks, blks_len, func_file.clone(), f_name.to_string(), var_scope_info)
                        .unwrap_or_else(|e| panic!("const_entry_fn failed: {}", e));
                    func_blk_map.insert(f_name.to_string(), (entry_bl, blks_len - 1, f.inline.is_some()));
                }
            }
        }

        // Convert func call terminators into coresponding block label
        let mut new_blks = Vec::new();
        let mut next_new_blk_label = blks_len;
        for next_bl in 0..blks_len {
            (new_blks, next_new_blk_label) = self.bl_gen_func_call_to_bl_label(&blks, &func_blk_map, new_blks, next_new_blk_label, next_bl, 0, &BTreeMap::new());
        }
        (new_blks.into_iter().map(|i| i.unwrap()).collect(), 0, inputs)
    }

    fn bl_gen_func_call_to_bl_label(
        &'ast self,
        blks: &Vec<Block<'ast>>,
        func_blk_map: &BTreeMap<String, (usize, usize, bool)>,
        mut new_blks: Vec<Option<Block<'ast>>>,
        mut next_new_blk_label: usize,
        cur_bl: usize,
        offset: usize,
        label_map: &BTreeMap<usize, usize>,
    ) -> (Vec<Option<Block<'ast>>>, usize) {
        let mut blk = Block::clone(cur_bl + offset, &blks[cur_bl]);
        // If we encounter any rp@ = <counter>, update <counter> to label_map[<counter>]
        for i in 0..blk.instructions.len() {
            let bc = blk.instructions[i].clone();
            if let Some(new_bc) = rp_replacement_stmt(bc, label_map.clone()) {
                blk.instructions[i] = new_bc;
            }
        }

        match &blk.terminator {
            BlockTerminator::FuncCall(f_name) => {
                let (entry_bl, exit_bl, inline) = func_blk_map.get(f_name).unwrap();
                // if inline, copy all blocks
                if *inline {
                    blk.terminator = BlockTerminator::Transition(bl_coda(NextBlock::Label(next_new_blk_label)));
                    let offset = next_new_blk_label - entry_bl;
                    next_new_blk_label += exit_bl - entry_bl + 1;
                    let mut next_label_map = BTreeMap::new();
                    for next_bl in *entry_bl..*exit_bl + 1 {
                        next_label_map.insert(next_bl, next_bl + offset);
                    }
                    for next_bl in *entry_bl..*exit_bl + 1 {
                        (new_blks, next_new_blk_label) = self.bl_gen_func_call_to_bl_label(blks, func_blk_map, new_blks, next_new_blk_label, next_bl, offset, &next_label_map);
                    }
                } else {
                    blk.terminator = BlockTerminator::Transition(bl_coda(NextBlock::Label(*entry_bl)));
                }
            },
            BlockTerminator::Transition(e) => {
                // Update terminator
                blk.terminator = BlockTerminator::Transition(bl_trans_map(e, label_map));
            },
            BlockTerminator::ProgTerm => {}
        }

        if new_blks.len() <= cur_bl + offset {
            new_blks.extend(vec![None; cur_bl + offset + 1 - new_blks.len()]);
        }
        new_blks[cur_bl + offset] = Some(blk);
        (new_blks, next_new_blk_label)
    }

    // Treat constants as normal variables and pass all of them along every function call
    // Unused constants will be eliminated by liveness analysis
    // Every constant is always the 0.0 version in each function, local variables might shadow them afterwards
    // First declare constants as variables of the main function
    fn bl_gen_constants(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        files: &Vec<&PathBuf>,
        mut var_scope_info: VarScopeInfo
    ) -> Result<(Vec<Block>, usize, VarScopeInfo), String> {
        // Initialize a new constant block
        // Push all constant declarations into it
        blks.push(Block::new(blks_len, 1, "main".to_string(), 0));
        blks_len += 1;

        for p in files {
            for d in &self.asts.get(*p).unwrap().declarations {
                match d {
                    ast::SymbolDeclaration::Constant(c) => {
                        debug!("processing decl: const {} in {}", c.id.value, p.display());
                        // Convert the constant definition into definition statement
                        let d = DefinitionStatement {
                            lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                                array_metadata: c.array_metadata.clone(),
                                ty: c.ty.clone(),
                                identifier: c.id.clone(),
                                span: Span::new("", 0, 0).unwrap()
                            })],
                            expression: c.expression.clone(),
                            span: Span::new("", 0, 0).unwrap()
                        };
                        (blks, blks_len, var_scope_info) = self.bl_gen_assign_::<true>(blks, blks_len, &d, "main", 0, var_scope_info)?;
                        var_scope_info.add_constant(&c.id.value, self.type_impl_::<false>(&c.ty)?);
                    }
                    _ => {}
                }
            }
        }

        Ok((blks, blks_len, var_scope_info))
    }

    // Convert each function to blocks
    // Generic: IS_MAIN determines if we are in the main function:
    //   1. We don't update the exit block of MAIN to rp@
    //   2. Return value of main is not a struct & stored in %RET, return value of every function, if struct, is stored in ret@
    //   3. If not in the main function, declare all constants again
    // Return type:
    // Blks, blks_len
    fn bl_gen_function_init_<const IS_MAIN: bool>(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        f_path: PathBuf,
        f_name: String,
        mut var_scope_info: VarScopeInfo
    ) -> Result<(Vec<Block>, usize, Vec<(String, Ty)>, VarScopeInfo), String> {
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
            if let Ty::Struct(..) = ret_ty {
                if IS_MAIN {
                    panic!("%RET cannot be a struct!");
                }
            }

            // Create new Block, initial scope is 0
            blks.push(Block::new(blks_len, 1, f_name.to_string(), 0));
            blks_len += 1;

            // Declare all parameters
            for p in f.parameters.clone().into_iter() {
                let p_id = p.id.value.clone();
                let p_ty = self.type_impl_::<false>(&p.ty)?;
                var_scope_info.declare_var(&p_id, &f_name, 0, p_ty.clone());
                // Flatten out inputs
                let mut flattened_p = Vec::new();
                flatten_var(&p_id, &p_ty, &mut flattened_p);
                for (p_entry, _) in flattened_p {
                    inputs.push(var_scope_info.reference_var(&p_entry, &f_name)?.clone());
                }
            }
            // Declare all constants, if not main
            // Constants of main function are already declared in bl_gen_constants
            if !IS_MAIN {
                for (c_name, c_ty) in var_scope_info.constants.clone() {
                    var_scope_info.declare_var(&c_name, &f_name, 0, c_ty);
                }
            }

            // Iterate through Stmts
            for s in &f.statements {
                // All statements at function level have scope 0
                (blks, blks_len, var_scope_info) = self.bl_gen_stmt_::<IS_MAIN>(blks, blks_len, s, &ret_ty, &f_name, var_scope_info, 1, 0)?;
            }

            // Set terminator to ProgTerm if in main, point to rp@ otherwise
            if IS_MAIN {
                blks[blks_len - 1].terminator = BlockTerminator::ProgTerm;
            } else {
                blks[blks_len - 1].terminator = BlockTerminator::Transition(bl_coda(NextBlock::Rp(blks[blks_len - 1].fn_name.clone())));
            }
        }

        Ok((blks, blks_len, inputs, var_scope_info))
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
            let caller_name = blks[blks_len - 1].fn_name.to_string();
            let caller_scope = blks[blks_len - 1].scope;

            // Assign p^0 to a
            for (p, a) in f.parameters.clone().into_iter().zip(args) {
                let p_id = p.id.value.clone();
                let p_ty = self.type_impl_::<false>(&p.ty)?;
                var_scope_info.declare_var(&p_id, &f_name, 0, p_ty.clone());
                (blks, blks_len) = self.bl_gen_def_stmt_(blks, blks_len, &p_id, &a, &p_ty, &f_name, &caller_name, &var_scope_info)?;
            }
            // Assign all constants from one function to another
            for (c_name, c_ty) in var_scope_info.constants.clone() {
                var_scope_info.declare_var(&c_name, &f_name, 0, c_ty.clone());
                let const_expr = Expression::Identifier(IdentifierExpression {
                    value: c_name.to_string(),
                    span: Span::new("", 0, 0).unwrap()
                });
                let new_const_expr: Expression;
                (blks, blks_len, var_scope_info, new_const_expr, _, _, _, _) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &const_expr, &caller_name, func_count, 0, 0, 0, var_scope_info)?;
                (blks, blks_len) = self.bl_gen_def_stmt_(blks, blks_len, &c_name, &new_const_expr, &c_ty, &f_name, &caller_name, &var_scope_info)?;
            }


            // Set up rp@ and block terminator
            let rp_update_stmt = Statement::Definition(DefinitionStatement {
                lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                    array_metadata: None,
                    ty: Type::Basic(BasicType::Field(FieldType {
                        span: Span::new("", 0, 0).unwrap()
                    })),
                    identifier: IdentifierExpression {
                        value: format!("rp@.{}", f_name),
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
            let num_exec_bound = blks[blks_len - 1].fn_num_exec_bound;
            blks.push(Block::new(blks_len, num_exec_bound, caller_name.clone(), caller_scope));
            blks_len += 1; 

            // Store Return value to a temporary variable "ret^X"
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
            if let Ty::Array(..) = ret_ty {
                ret_ty = Ty::Field;
            }

            let ret_name = format!("ret^{}", func_count);
            var_scope_info.declare_var(&ret_name, &caller_name, caller_scope, ret_ty.clone());
            let ret_expr = Expression::Identifier(IdentifierExpression {
                value: format!("%RET.{}", f_name),
                span: Span::new("", 0, 0).unwrap()
            });
            (blks, blks_len) = self.bl_gen_def_stmt_(blks, blks_len, &ret_name, &ret_expr, &ret_ty, &caller_name, &f_name, &var_scope_info)?;
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
        ret_ty: &Ty,
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
                assert_eq!(r.expressions.len(), 1);
                let ret_expr: Expression;
                (blks, blks_len, var_scope_info, ret_expr, _, _, _, _) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &r.expressions[0], f_name, 0, 0, 0, 0, var_scope_info)?;
                // Convert the statement to %RET = ret_expr
                // Note return variable should be reference as %RET.<f_name> to allow different type for different functions
                let ret_name = "%RET".to_string();
                (blks, blks_len) = self.bl_gen_def_stmt_(blks, blks_len, &ret_name, &ret_expr, &ret_ty, f_name, f_name, &var_scope_info)?;

                // Set terminator to ProgTerm if in main, point to rp@ otherwise
                if IS_MAIN {
                    blks[blks_len - 1].terminator = BlockTerminator::ProgTerm;
                } else {
                    blks[blks_len - 1].terminator = BlockTerminator::Transition(bl_coda(NextBlock::Rp(blks[blks_len - 1].fn_name.clone())));
                }

                // Create a dummy block in case there are anything after return
                // Will be eliminated during DBE
                blks.push(Block::new(blks_len, num_exec_bound, f_name.to_string(), cur_scope));
                blks_len += 1;

            }
            Statement::Assertion(a) => {
                let asst_expr: Expression;
                (blks, blks_len, var_scope_info, asst_expr, _, _, _, _) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &a.expression, f_name, 0, 0, 0, 0, var_scope_info)?;
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
                let new_v_name = var_scope_info.declare_var(&v_name, f_name, cur_scope, ty.clone());

                let from_expr: Expression;
                let mut func_count = 0;
                let mut array_count = 0;
                let mut struct_count = 0;
                let mut load_count = 0;
                (blks, blks_len, var_scope_info, from_expr, func_count, array_count, struct_count, load_count) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &it.from, f_name, func_count, array_count, struct_count, load_count, var_scope_info)?;
                let to_expr: Expression;
                (blks, blks_len, var_scope_info, to_expr, _, _, _, _) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &it.to, f_name, func_count, array_count, struct_count, load_count, var_scope_info)?;

                // Record the number of iterations of the loop
                let (loop_num_it, cnst_for_loop) = {
                    // Indicator of whether both from and to are constants
                    let mut cnst_for_loop = true;
                    let from_const = if let Expression::Literal(LiteralExpression::DecimalLiteral(ref dle)) = from_expr {
                        dle.value.value.parse::<usize>().unwrap()
                    } else {
                        cnst_for_loop = false;
                        0
                    };
                    let to_const = if let Expression::Literal(LiteralExpression::DecimalLiteral(ref dle)) = to_expr {
                        dle.value.value.parse::<usize>().unwrap()
                    } else {
                        cnst_for_loop = false;
                        0
                    };
                    if !cnst_for_loop { (1, cnst_for_loop) } else { (to_const - from_const, cnst_for_loop) }
                };

                // Create and push FROM statement
                let new_id = IdentifierExpression {
                    value: new_v_name.to_string(),
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
                // If number of iterations is not constant, then treat it as a while loop
                if !cnst_for_loop {
                    blks[blks_len].is_head_of_while_loop = true;
                }
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
                blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_increment_stmt(&new_v_name, 1, &ty)));

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
                (blks, blks_len, var_scope_info, cond_expr, _, _, _, _) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &w.condition, f_name, 0, 0, 0, 0, var_scope_info)?;

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
                (blks, blks_len, var_scope_info, cond_expr, _, _, _, _) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &c.condition, f_name, 0, 0, 0, 0, var_scope_info)?;

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
                (blks, blks_len, var_scope_info) = self.bl_gen_assign_::<IS_MAIN>(blks, blks_len, d, f_name, cur_scope, var_scope_info)?;
            }
            Statement::CondStore(_) => { panic!("Conditional store statements unsupported.") }
            Statement::Witness(w, ) => {
                let wit_ty = self.type_impl_::<false>(&w.ty)?;
                let wit_name = w.id.value.to_string();
                let wit_extended_name = var_scope_info.declare_var(&wit_name, f_name, cur_scope, wit_ty.clone());
                blks[blks_len - 1].instructions.push(BlockContent::Witness((wit_extended_name, wit_ty, true)));
            }
            Statement::ArrayDecl(a) => {
                // Convert the statement into an ArrayInit
                let arr_ty = self.type_impl_::<false>(&a.ty)?;
                let arr_name = a.id.value.to_string();
                let arr_extended_name = var_scope_info.declare_var(&arr_name, f_name, cur_scope, arr_ty.clone());
                if let Type::Array(aty) = &a.ty {
                    let index_ty = self.bl_gen_type_(&aty.dimensions[0].1, f_name, &var_scope_info)?;
                    let new_len_expr: Expression;
                    (blks, blks_len, var_scope_info, new_len_expr, _, _, _, _) = 
                        self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &aty.dimensions[0].1, f_name, 0, 0, 0, 0, var_scope_info)?;
                    let entry_ty = if let Ty::Array(_, _, entry_ty) = arr_ty { *entry_ty.clone() } else { unreachable!() };
                    
                    // Compute the actual allocated size
                    let new_size_expr = self.bl_gen_pointer_offset_(new_len_expr, &Vec::new(), &index_ty, &entry_ty)?;
                    blks[blks_len - 1].instructions.push(BlockContent::ArrayInit((arr_extended_name, entry_ty, new_size_expr, aty.dimensions[0].0.is_some())));
                } else {
                    return Err(format!("Declaring non-array {} as an array!", arr_extended_name));
                }
            }
        }
        Ok((blks, blks_len, var_scope_info))
    }

    // Given two types of an assignment statement, determine whether RHS can "fit" into LHS
    // RHS "fits" if it either matches LHS, or for every array in LHS with dynamic length (len = 0), RHS provides the same array with a fixed length
    fn bl_gen_type_check(
        lhs: &Ty,
        rhs: &Ty
    ) -> Result<(), String> {
        match (lhs, rhs) {
            (Ty::Array(lhs_ro, lhs_len, lhs_entry_ty), Ty::Array(rhs_ro, rhs_len, rhs_entry_ty)) => {
                let ro_check = lhs_ro == rhs_ro;
                let len_check = lhs_len == rhs_len || *lhs_len == 0 || *rhs_len == 0;
                let entry_ty_check = Self::bl_gen_type_check(lhs_entry_ty, rhs_entry_ty);
                if ro_check && len_check && entry_ty_check.is_ok() {
                    Ok(())
                } else {
                    Err(format!("Type Check failed: lhs - {:?}, rhs - {:?}", lhs, rhs))
                }
            }
            (Ty::Struct(lhs_name, lhs_field_ty), Ty::Struct(rhs_name, rhs_field_ty)) => {
                if lhs_name != rhs_name {
                    Err(format!("Type Check failed: lhs - {:?}, rhs - {:?}", lhs, rhs))
                } else {
                    if lhs_field_ty.fields().zip(rhs_field_ty.fields())
                        .map(|(lhs_field, rhs_field)| lhs_field.0 == rhs_field.0 && Self::bl_gen_type_check(&lhs_field.1, &rhs_field.1).is_ok())
                        .fold(true, |acc, b| acc && b) {
                            Ok(())
                    } else {
                        Err(format!("Type Check failed: lhs - {:?}, rhs - {:?}", lhs, rhs))
                    }
                }
            }
            _ => {
                if lhs == rhs { Ok(()) } else {
                    Err(format!("Type Check failed: lhs - {:?}, rhs - {:?}", lhs, rhs))
                }
            }
        }
    }

    // Generate blocks from an assignment
    // Assignment LHS to RHS expression
    // If LHS is array, perform pointer (field) assignment
    // if LHS is struct, perform assignment on individual members
    fn bl_gen_assign_<const IS_MAIN: bool>(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        d: &DefinitionStatement<'ast>,
        f_name: &str,
        cur_scope: usize,
        mut var_scope_info: VarScopeInfo,
    ) -> Result<(Vec<Block>, usize, VarScopeInfo), String> {
        debug!("Block Gen Assign");

        // XXX(unimpl) multi-assignment unimplemented
        assert!(d.lhs.len() <= 1);

        // Evaluate function calls in expression
        let rhs_ty = self.bl_gen_type_(&d.expression, f_name, &var_scope_info)?;
        let rhs_expr: Expression;
        (blks, blks_len, var_scope_info, rhs_expr, _, _, _, _) = 
            self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &d.expression, f_name, 0, 0, 0, 0, var_scope_info)?;

        // Handle Scoping change
        if let Some(l) = d.lhs.first() {
            match l {
                TypedIdentifierOrAssignee::Assignee(l) => {
                    let mut skip_stmt_gen = false;

                    let mut l_name = l.id.value.clone();
                    // No scoping change if lhs is an assignee, only need to make sure it has appeared before
                    let mut lhs_ty = var_scope_info.reference_var(&l.id.value.clone(), f_name)?.1;

                    let mut acc_counter = 0;
                    while acc_counter < l.accesses.len() {
                        let acc = &l.accesses[acc_counter];
                        match acc {
                            AssigneeAccess::Member(m) => {
                                l_name = format!("{}^{}", l_name, m.id.value);
                                let member_ty = var_scope_info.reference_var(&l_name, f_name)?.1;
                                lhs_ty = member_ty;
                            }
                            AssigneeAccess::Select(s) => {
                                let (new_l, arr_ty) = var_scope_info.reference_var(&l_name, f_name)?;
                                if let Ty::Array(ro, _, entry_ty) = arr_ty {
                                    let struct_ty = *entry_ty.clone();
                                    let mut entry_ty = *entry_ty.clone();
                                    Self::bl_gen_type_check(&entry_ty, &rhs_ty)?;
                                    skip_stmt_gen = true;
                                    if let RangeOrExpression::Expression(e) = &s.expression {
                                        // For all subsequent struct member accesses, compute index and rhs
                                        let mut member_accesses = Vec::new();
                                        acc_counter += 1;
                                        while acc_counter < l.accesses.len() {
                                            if let AssigneeAccess::Member(m) = &l.accesses[acc_counter] {
                                                member_accesses.push(m.clone());
                                                if let Ty::Struct(_, members) = &entry_ty {
                                                    entry_ty = members.search(&m.id.value)
                                                        .ok_or(format!("Array struct {} does not have member {}!", l.id.value, m.id.value))?.1.clone();
                                                } else {
                                                    return Err(format!("Cannot perform member access on non-struct {}!", l.id.value));
                                                }
                                            } else {
                                                break;
                                            }
                                            acc_counter += 1;
                                        }

                                        // Process the index
                                        let index_ty = self.bl_gen_type_(&e, f_name, &var_scope_info)?;
                                        let new_index_expr: Expression;
                                        (blks, blks_len, var_scope_info, new_index_expr, _, _, _, _) = 
                                            self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &e, f_name, 0, 0, 0, 0, var_scope_info)?;
                                        // Perform pointer arithmetics
                                        (blks, blks_len) = self.bl_gen_store_(blks, blks_len, &new_l, &index_ty, &new_index_expr, &rhs_expr, &entry_ty, f_name, &var_scope_info, false, &struct_ty, &member_accesses, ro)?;
                                    } else {
                                        return Err(format!("Array range access not implemented!"));
                                    }
                                    lhs_ty = entry_ty;
                                } else {
                                    return Err(format!("Cannot perform store: {} is not an array!", new_l));
                                }
                            }
                        }
                        acc_counter += 1;
                    }
                    Self::bl_gen_type_check(&lhs_ty, &rhs_ty)?;
                    if !skip_stmt_gen {
                        (blks, blks_len) = 
                            self.bl_gen_def_stmt_(blks, blks_len, &l_name, &rhs_expr, &rhs_ty, f_name, f_name, &var_scope_info)?;
                    }
                }
                TypedIdentifierOrAssignee::TypedIdentifier(l) => {
                    // If array is dynamically bounded, cannot use type_impl_ because bound might involve variables undefined in circ
                    let l_name = l.identifier.value.to_string();
                    let lhs_ty = self.type_impl_::<false>(&l.ty)?;
                    Self::bl_gen_type_check(&lhs_ty, &rhs_ty)?;
                    var_scope_info.declare_var(&l_name, f_name, cur_scope, lhs_ty.clone());
                    (blks, blks_len) = 
                        self.bl_gen_def_stmt_(blks, blks_len, &l_name, &rhs_expr, &rhs_ty, f_name, f_name, &var_scope_info)?;
                }
            }
        } else {
            panic!("Statement with no LHS!");
        }
        Ok((blks, blks_len, var_scope_info))
    }

    // Generate definition statements l = r_expr that might involve structs
    // Assume that r_expr has been processed
    // Allow f_name for LHS and RHS to be different for function calls
    fn bl_gen_def_stmt_(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        l: &str,
        new_r_expr: &Expression<'ast>,
        ty: &Ty,
        l_f_name: &str,
        r_f_name: &str,
        var_scope_info: &VarScopeInfo,
    ) -> Result<(Vec<Block>, usize), String> {
        debug!("Block Gen Def Stmt: {} = {}", l, new_r_expr.span().as_str());
        // reference lhs
        // if LHS is %RET or its members, only append function name
        let new_l = if l.len() >= 4 && &l[..4] == "%RET" {
            format!("{}.{}", l, l_f_name)
        } else {
            var_scope_info.reference_var(&l, l_f_name)?.0
        };
        // Struct assignment
        if let Ty::Struct(_, members) = ty {
            // rhs needs to be an identifier
            if let Expression::Identifier(ie) = &new_r_expr {
                // Strip scope & f_name out of r
                let r = ie.value.split(".").next().unwrap_or("");
                for (m, m_ty) in members.fields() {
                    let l_member = format!("{l}^{m}");
                    let r_member = format!("{r}^{m}");
                    let new_r_member = if r_member.len() >= 4 && &r_member[..4] == "%RET" {
                        format!("{}.{}", r_member, r_f_name)
                    } else {
                        var_scope_info.reference_var(&r_member, r_f_name)?.0
                    };
                    let new_r_member_expr = Expression::Identifier(IdentifierExpression {
                        value: new_r_member,
                        span: Span::new("", 0, 0).unwrap()
                    });
                    (blks, blks_len) = self.bl_gen_def_stmt_(blks, blks_len, &l_member, &new_r_member_expr, m_ty, l_f_name, r_f_name, var_scope_info)?;
                }
            } else {
                return Err(format!("Struct assignment failed: cannot identify RHS of definition statement: {:?}", new_r_expr));
            }
        }
        // Other assignment
        else {
            let decl_stmt = DefinitionStatement {
                lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                    array_metadata: None,
                    // if ty is an array, convert it to a field
                    ty: ty_to_type(if let Ty::Array(..) = ty { &Ty::Field } else { ty }).unwrap(),
                    identifier: IdentifierExpression {
                        value: new_l,
                        span: Span::new("", 0, 0).unwrap()
                    },
                    span: Span::new("", 0, 0).unwrap()
                })],
                expression: new_r_expr.clone(),
                span: Span::new("", 0, 0).unwrap()
            };
            blks[blks_len - 1].instructions.push(BlockContent::Stmt(Statement::Definition(decl_stmt)));
        }
        Ok((blks, blks_len))
    }

    // Generate store instructions, similar to bl_gen_def_stmt
    // Note: The compiler DOES NOT reason about whether we can store an entry into a read_only slot
    //       If an illegal store is performed, it will be rejected by the proof
    fn bl_gen_store_(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        arr_extended_name: &str,
        index_ty: &Ty,
        new_index_expr: &Expression<'ast>,
        new_entry_expr: &Expression<'ast>,
        cur_ty: &Ty,
        r_f_name: &str,
        var_scope_info: &VarScopeInfo,
        is_alloc: bool,
        struct_ty: &Ty,
        prev_accesses: &Vec<MemberAccess>,
        read_only: bool,
    ) -> Result<(Vec<Block>, usize), String> {
        debug!("Block Gen Store: {}[{}] = {}", arr_extended_name, new_index_expr.span().as_str(), new_entry_expr.span().as_str());

        // Struct store
        if let Ty::Struct(_, members) = cur_ty {
            // entry needs to be an identifier
            if let Expression::Identifier(ie) = &new_entry_expr {
                // Strip scope & f_name out of r
                let r = ie.value.split(".").next().unwrap_or("");
                for (m, m_ty) in members.fields() {
                    let new_r_member = var_scope_info.reference_var(&format!("{r}^{m}"), r_f_name)?.0;
                    let new_r_member_expr = Expression::Identifier(IdentifierExpression {
                        value: new_r_member,
                        span: Span::new("", 0, 0).unwrap()
                    });
                    let mut next_accesses = prev_accesses.clone();
                    next_accesses.push(MemberAccess {
                        id: IdentifierExpression {
                            value: m.to_string(),
                            span: Span::new("", 0, 0).unwrap()
                        },
                        span: Span::new("", 0, 0).unwrap()
                    });
                    (blks, blks_len) = self.bl_gen_store_(
                        blks, 
                        blks_len, 
                        arr_extended_name,
                        index_ty,
                        new_index_expr,
                        &new_r_member_expr,
                        m_ty,
                        r_f_name,
                        var_scope_info,
                        is_alloc,
                        struct_ty,
                        &next_accesses,
                        read_only,
                    )?;
                }
            } else {
                return Err(format!("Struct assignment failed: cannot identify RHS of definition statement: {:?}", new_entry_expr));
            }
        }
        // Other assignment
        else {
            let cur_ty = if let Ty::Array(..) = cur_ty { Ty::Field } else { cur_ty.clone() };
            let new_offset_expr = self.bl_gen_pointer_offset_(new_index_expr.clone(), prev_accesses, index_ty, struct_ty)?;
            let store_instr = BlockContent::Store((new_entry_expr.clone(), cur_ty, arr_extended_name.to_string(), new_offset_expr, is_alloc, read_only));
            blks[blks_len - 1].instructions.push(store_instr);
            if read_only {
                blks[blks_len - 1].num_ro_ops += 1;
            } else {
                blks[blks_len - 1].num_vm_ops += 1;
            }
        }
        Ok((blks, blks_len))
    }

    // Generate load instructions
    fn bl_gen_load_(
        &'ast self,
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        l: &str,
        arr_extended_name: &str,
        index_ty: &Ty,
        new_index_expr: &Expression<'ast>,
        cur_ty: &Ty,
        l_f_name: &str,
        var_scope_info: &VarScopeInfo,
        struct_ty: &Ty,
        prev_accesses: &Vec<MemberAccess>,
        read_only: bool,
    ) -> Result<(Vec<Block>, usize), String> {
        debug!("Block Gen Load: {} = {}[{}]", l, arr_extended_name, new_index_expr.span().as_str());

        // declare lhs, only reference the var if not reserved register
        let new_l = if l.chars().next().unwrap() == '%' { l.to_string() } else { var_scope_info.reference_var(&l, l_f_name)?.0 };
        // Struct load
        if let Ty::Struct(_, members) = cur_ty {
            for (m, m_ty) in members.fields() {
                let l_member = format!("{l}^{m}");
                let mut next_accesses = prev_accesses.clone();
                next_accesses.push(MemberAccess {
                    id: IdentifierExpression {
                        value: m.to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    },
                    span: Span::new("", 0, 0).unwrap()
                });
                (blks, blks_len) = self.bl_gen_load_(
                    blks, 
                    blks_len, 
                    &l_member,
                    arr_extended_name,
                    index_ty,
                    new_index_expr,
                    m_ty,
                    l_f_name,
                    var_scope_info,
                    struct_ty,
                    &next_accesses,
                    read_only,
                )?;
            }
        }
        // Other assignment
        else {
            let cur_ty = if let Ty::Array(..) = cur_ty { Ty::Field } else { cur_ty.clone() };
            let new_offset_expr = self.bl_gen_pointer_offset_(new_index_expr.clone(), prev_accesses, index_ty, struct_ty)?;
            let load_instr = BlockContent::Load((new_l, cur_ty, arr_extended_name.to_string(), new_offset_expr, read_only));
            blks[blks_len - 1].instructions.push(load_instr);
            if read_only {
                blks[blks_len - 1].num_ro_ops += 1;
            } else {
                blks[blks_len - 1].num_vm_ops += 1;
            }
        }
        Ok((blks, blks_len))
    }

    // Generate blocks from expressions
    // Return value:
    // result[0 ~ 2] follows bl_gen_stmt
    // result[3]: new_expr reconstructs the expression, converts all function calls to %RET, and handles scoping
    // result[4]: func_count, how many function calls have occured in this statement?
    // result[5]: array_count, how many arrays have been initiated in this statement?
    // result[6]: load_count, how many loads have occured in this statement?
    // result[7]: all (index, value) pair for array initialization
    // Since the return value of all function calls are stored in %RET, we need to differentiate them if
    // multiple function calls occur in the same statement
    fn bl_gen_expr_<const IS_MAIN: bool>(
        &'ast self, 
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        e: &Expression<'ast>,
        f_name: &str,
        mut func_count: usize,
        mut array_count: usize,
        mut struct_count: usize,
        mut load_count: usize,
        mut var_scope_info: VarScopeInfo
    ) -> Result<(Vec<Block>, usize, VarScopeInfo, Expression, usize, usize, usize, usize), String> {
        debug!("Block Gen Expr: {}", e.span().as_str());

        let mut ret_e = e.clone();
        match e {
            Expression::Ternary(t) => {
                let new_e_first: Expression;
                let new_e_second: Expression;
                let new_e_third: Expression;
                (blks, blks_len, var_scope_info, new_e_first, func_count, array_count, struct_count, load_count) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &t.first, f_name, func_count, array_count, struct_count, load_count, var_scope_info)?;
                (blks, blks_len, var_scope_info, new_e_second, func_count, array_count, struct_count, load_count) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &t.second, f_name, func_count, array_count, struct_count, load_count, var_scope_info)?;
                (blks, blks_len, var_scope_info, new_e_third, func_count, array_count, struct_count, load_count) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &t.third, f_name, func_count, array_count, struct_count, load_count, var_scope_info)?;
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
                (blks, blks_len, var_scope_info, new_e_left, func_count, array_count, struct_count, load_count) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &b.left, f_name, func_count, array_count, struct_count, load_count, var_scope_info)?;
                (blks, blks_len, var_scope_info, new_e_right, func_count, array_count, struct_count, load_count) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &b.right, f_name, func_count, array_count, struct_count, load_count, var_scope_info)?;
                ret_e = Expression::Binary(BinaryExpression {
                    op: b.op.clone(),
                    left: Box::new(new_e_left),
                    right: Box::new(new_e_right),
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::Unary(u) => {
                let new_e_expr: Expression;
                (blks, blks_len, var_scope_info, new_e_expr, func_count, array_count, struct_count, load_count) = 
                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &u.expression, f_name, func_count, array_count, struct_count, load_count, var_scope_info)?;
                ret_e = Expression::Unary(UnaryExpression {
                    op: u.op.clone(),
                    expression: Box::new(new_e_expr),
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::Postfix(p) => {
                // assume no functions in arrays, etc.
                assert!(p.accesses.len() > 0);
                let mut ret_name = p.id.value.to_string();
                let mut acc_counter = 0;
                while acc_counter < p.accesses.len() {
                    let acc = &p.accesses[acc_counter];
                    match acc {
                        Access::Call(c) => {
                            assert_eq!(p.accesses.len(), 1);

                            let (callee_path, callee_name) = self.deref_import(&p.id.value);
                            let mut args: Vec<Expression> = Vec::new();
                            let mut new_expr: Expression;

                            for old_expr in &c.arguments.expressions {
                                (blks, blks_len, var_scope_info, new_expr, func_count, array_count, struct_count, load_count) = 
                                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, old_expr, f_name, func_count, array_count, struct_count, load_count, var_scope_info)?;
                                args.push(new_expr);                       
                            }
        
                            // Do the function call
                            (blks, blks_len, _, var_scope_info, func_count) =
                                self.bl_gen_function_call_::<IS_MAIN>(blks, blks_len, args, callee_path.clone(), callee_name.clone(), func_count, var_scope_info)?;
        
                            ret_name = format!("ret^{}", func_count);
                            func_count += 1;
                            acc_counter += 1;
                        }
                        Access::Select(s) => {
                            if let RangeOrExpression::Expression(e) = &s.expression {
                                // Store the loaded value in a separate variable and return it
                                let load_name = format!("load^{}", load_count);
                                let arr_name = &ret_name;
                                let (arr_extended_name, arr_ty) = var_scope_info.reference_var(&arr_name, f_name)?;
                                let (ro, mut load_ty) = if let Ty::Array(ro, _, load_ty) = arr_ty {
                                    (ro, *load_ty.clone())
                                } else {
                                    return Err(format!("Loading from a variable {} that is not an array!", arr_extended_name));
                                };
                                let struct_ty = load_ty.clone();
                                let cur_scope = blks[blks_len - 1].scope;

                                // Assert that all remaining accesses are struct member accesses
                                let mut member_accesses = Vec::new();
                                acc_counter += 1;
                                while acc_counter < p.accesses.len() {
                                    if let Access::Member(m) = &p.accesses[acc_counter] {
                                        member_accesses.push(m.clone());
                                        if let Ty::Struct(_, members) = &load_ty {
                                            load_ty = members.search(&m.id.value)
                                                .ok_or(format!("Array struct {} does not have member {}!", arr_name, m.id.value))?.1.clone();
                                        } else {
                                            return Err(format!("Cannot perform member access on non-struct {}!", arr_name));
                                        }
                                    } else {
                                        break;
                                    }
                                    acc_counter += 1;
                                }
                                var_scope_info.declare_var(&load_name, &f_name, cur_scope, load_ty.clone());

                                // Process the index
                                let index_ty = self.bl_gen_type_(&e, f_name, &var_scope_info)?;
                                let new_index_expr: Expression;
                                (blks, blks_len, var_scope_info, new_index_expr, func_count, array_count, struct_count, load_count) = 
                                    self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &e, f_name, func_count, array_count, struct_count, load_count, var_scope_info)?;
                                // Perform pointer arithmetics
                                (blks, blks_len) = self.bl_gen_load_(
                                    blks, 
                                    blks_len, 
                                    &load_name,
                                    &arr_extended_name,
                                    &index_ty, 
                                    &new_index_expr, 
                                    &load_ty, 
                                    f_name, 
                                    &var_scope_info, 
                                    &struct_ty,
                                    &member_accesses,
                                    ro,
                                )?;
                                load_count += 1;
                                ret_name = load_name;
                            } else {
                                return Err(format!("Array range access not implemented!"));
                            }
                        }
                        Access::Member(m) => {
                            // Construct p^member
                            ret_name = format!{"{}^{}", ret_name, m.id.value};
                            acc_counter += 1;
                        }
                    }
                }
                let ret_extended_name = var_scope_info.reference_var(&ret_name, f_name)?.0;
                ret_e = Expression::Identifier(IdentifierExpression {
                    value: ret_extended_name,
                    span: Span::new("", 0, 0).unwrap()
                });
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
                let entry_ty = self.bl_gen_type_(&ai.value, f_name, &var_scope_info)?;
                // Note: if ai.count is not constant, expr_impl_ would fail
                let arr_size: Result<usize, String> = {
                    self.expr_impl_::<false>(&ai.count).and_then(|e| const_int(e)).and_then(|i| i.try_into().or_else(|_| Err("".to_string())))
                };
                let array_init_info = if let Ok(arr_size) = arr_size {
                    ArrayInitInfo::from_static_array_initializer(*ai.value.clone(), arr_size, ai.dim_ro.is_some(), entry_ty.clone())
                } else {
                    ArrayInitInfo::from_dyn_array_initializer(*ai.value.clone(), *ai.count.clone(), ai.dim_ro.is_some(), entry_ty)
                };
                let arr_extended_name: String;
                (blks, blks_len, var_scope_info, arr_extended_name, func_count, array_count, struct_count, load_count) = 
                    self.bl_gen_array_init_::<IS_MAIN>(blks, blks_len, func_count, array_count, struct_count, load_count, f_name, array_init_info, var_scope_info)?;
                ret_e = Expression::Identifier(IdentifierExpression {
                    value: arr_extended_name,
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::InlineArray(ia) => {
                let mut e_list = Vec::new();
                let mut entry_ty = Ty::Field;
                for se in &ia.expressions {
                    if let SpreadOrExpression::Expression(e) = se {
                        entry_ty = self.bl_gen_type_(&e, f_name, &var_scope_info)?;
                        e_list.push(e.clone());
                    } else {
                        return Err(format!("Spread not supported in inline arrays!"));
                    }
                }
                let array_init_info = ArrayInitInfo::from_inline_array(e_list, ia.dim_ro.is_some(), entry_ty.clone());
                let arr_extended_name: String;
                (blks, blks_len, var_scope_info, arr_extended_name, func_count, array_count, struct_count, load_count) = 
                    self.bl_gen_array_init_::<IS_MAIN>(blks, blks_len, func_count, array_count, struct_count, load_count, f_name, array_init_info, var_scope_info)?;
                ret_e = Expression::Identifier(IdentifierExpression {
                    value: arr_extended_name,
                    span: Span::new("", 0, 0).unwrap()
                });
            }
            Expression::InlineStruct(is) => {
                // Assume that type analysis has ensured correctness of the inline_struct
                let cur_scope = blks[blks_len - 1].scope;
                // Process all struct members
                let mut new_member_expr_list = Vec::new();
                for ism in &is.members {
                    let new_member_expr: Expression;
                    (blks, blks_len, var_scope_info, new_member_expr, func_count, array_count, struct_count, load_count) = 
                        self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &ism.expression, f_name, func_count, array_count, struct_count, load_count, var_scope_info)?;
                    new_member_expr_list.push(new_member_expr);
                }

                // Declare the inline struct
                let struct_name = format!("struct^{}", struct_count);
                let struct_ty = self.bl_gen_type_(&e, f_name, &var_scope_info)?;
                let new_struct_name = var_scope_info.declare_var(&struct_name, f_name, cur_scope, struct_ty);
                let mut ism_counter = 0;
                for ism in &is.members {
                     // Assign member_name to new_member_expr
                    let member_ty = self.bl_gen_type_(&ism.expression, f_name, &var_scope_info)?;
                    let member_name = format!("struct^{}^{}", struct_count, &ism.id.value);
                    var_scope_info.declare_var(&member_name, f_name, cur_scope, member_ty.clone());
                    let new_member_expr = &new_member_expr_list[ism_counter];

                    (blks, blks_len) =
                        self.bl_gen_def_stmt_(blks, blks_len, &member_name, new_member_expr, &member_ty, f_name, f_name, &var_scope_info)?;
                    ism_counter += 1;
                }
                ret_e = Expression::Identifier(IdentifierExpression {
                    value: new_struct_name,
                    span: Span::new("", 0, 0).unwrap()
                });
                struct_count += 1;
            }
        }
        Ok((blks, blks_len, var_scope_info, ret_e, func_count, array_count, struct_count, load_count))
    }

    // Convert array index into pointer offset and generate an expression
    fn bl_gen_pointer_offset_(
        &'ast self, 
        new_index_expr: Expression<'ast>,
        accesses: &Vec<MemberAccess>,
        index_ty: &Ty,
        entry_ty: &Ty,
    ) -> Result<Expression, String> {
        let (size, offset) = access_to_offset(entry_ty, accesses);
        assert!(size > 0 && offset < size);
        // returns size * new_index_expr + offset
        if size > 1 {
            let index_ty_suffix = ty_to_dec_suffix(&ty_to_type(index_ty)?);
            let mult_expr = Expression::Binary(BinaryExpression {
                op: BinaryOperator::Mul,
                left: Box::new(Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                    value: DecimalNumber {
                        value: size.to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    },
                    suffix: Some(index_ty_suffix.clone()),
                    span: Span::new("", 0, 0).unwrap()
                }))),
                right: Box::new(new_index_expr),
                span: Span::new("", 0, 0).unwrap()
            });
            let add_expr = if offset == 0 { mult_expr } else {
                Expression::Binary(BinaryExpression {
                    op: BinaryOperator::Add,
                    left: Box::new(mult_expr),
                    right: Box::new(Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                        value: DecimalNumber {
                            value: offset.to_string(),
                            span: Span::new("", 0, 0).unwrap()
                        },
                        suffix: Some(index_ty_suffix.clone()),
                        span: Span::new("", 0, 0).unwrap()
                    }))),
                    span: Span::new("", 0, 0).unwrap()
                })
            };
            Ok(add_expr)
        } else {
            Ok(new_index_expr)
        }
    }

    // Generate blocks from an array initialization
    // Assume both the array and all entries are preprocessed
    // Returns the new blocks
    fn bl_gen_array_init_<const IS_MAIN: bool>(
        &'ast self, 
        mut blks: Vec<Block<'ast>>,
        mut blks_len: usize,
        mut func_count: usize,
        mut array_count: usize,
        mut struct_count: usize,
        mut load_count: usize,
        f_name: &str,
        array_init_info: ArrayInitInfo<'ast>,
        mut var_scope_info: VarScopeInfo,
    ) -> Result<(Vec<Block>, usize, VarScopeInfo, String, usize, usize, usize, usize), String> {
        debug!("Block Gen Array Init");

        // Any form of array initialization involves allocation
        let is_alloc = true;
        let cur_array_count = array_count; // used by init

        let cur_scope = blks[blks_len - 1].scope;
        let entry_ty = array_init_info.entry_ty.clone();
        let read_only = array_init_info.read_only;
        let arr_len = if let Some(arr_content) = &array_init_info.arr_entries { arr_content.len() } else { 0 };
        // Assign array^X to be the temporary array
        let arr_name = format!("array^{}", array_count);
        let arr_extended_name = var_scope_info.declare_var(&arr_name, &f_name, cur_scope, Ty::Array(read_only, arr_len, Box::new(entry_ty.clone())));
        array_count += 1;
        
        // Initialize array
        // Process the index
        let index_ty = Ty::Uint(32);
        let len_expr = array_init_info.len_as_expr(&index_ty);
        let new_len_expr: Expression;
        (blks, blks_len, var_scope_info, new_len_expr, func_count, array_count, struct_count, load_count) = 
            self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &len_expr, f_name, func_count, array_count, struct_count, load_count, var_scope_info)?;
        // Perform pointer arithmetics
        let new_size_expr = self.bl_gen_pointer_offset_(new_len_expr, &Vec::new(), &index_ty, &entry_ty)?;
        blks[blks_len - 1].instructions.push(BlockContent::ArrayInit((arr_extended_name.clone(), entry_ty.clone(), new_size_expr, read_only)));

        // Start by declaring all init^X to unique_contents
        for i in 0..array_init_info.unique_contents.len() {
            // First process the content
            let content_expr: Expression;
            (blks, blks_len, var_scope_info, content_expr, func_count, array_count, struct_count, load_count) = 
                self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &array_init_info.unique_contents[i], f_name, func_count, array_count, struct_count, load_count, var_scope_info)?;
            // Then assign it to a temporary variable init^X
            let init_name = format!("init^{}^{}", cur_array_count, i);
            var_scope_info.declare_var(&init_name, &f_name, cur_scope, entry_ty.clone());
            (blks, blks_len) = self.bl_gen_def_stmt_(blks, blks_len, &init_name, &content_expr, &entry_ty, f_name, f_name, &var_scope_info)?;
        }

        // Then assigning each entries in array to corresponding init^X
        // if there is only one unique entry, then assign the array through a simplified for loop
        if array_init_info.unique_contents.len() == 1 {
            let index_name = "index@";
            let index_extended_name = var_scope_info.declare_var(&index_name, &f_name, cur_scope, index_ty.clone());
            
            // Init
            blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_init_stmt(&index_extended_name, &index_ty)));
            
            // Loop body
            let num_exec_bound = blks[blks_len - 1].fn_num_exec_bound;
            blks.push(Block::new(blks_len, num_exec_bound, f_name.to_string(), cur_scope + 1));
            blks_len += 1;
            // Decide if loop is bounded
            if array_init_info.dynamic {
                blks[blks_len - 1].is_head_of_while_loop = true;
            } else {
                blks[blks_len - 1].fn_num_exec_bound = array_init_info.arr_entries.clone().unwrap().len() * num_exec_bound;
            }
            let loop_header = blks_len - 1;

            // Store stmt & increment iterator
            let entry_name = format!("init^{}^0", cur_array_count);
            let entry_extended_name = var_scope_info.reference_var(&entry_name, &f_name)?.0;
            let new_entry_expr = Expression::Identifier(IdentifierExpression {
                value: entry_extended_name,
                span: Span::new("", 0, 0).unwrap()
            });
            let new_index_expr = Expression::Identifier(IdentifierExpression {
                value: index_extended_name.to_string(),
                span: Span::new("", 0, 0).unwrap()
            });
            (blks, blks_len) = self.bl_gen_store_(blks, blks_len, &arr_extended_name, &index_ty, &new_index_expr, &new_entry_expr, &entry_ty, f_name, &var_scope_info, is_alloc, &entry_ty, &Vec::new(), read_only)?;
            blks[blks_len - 1].instructions.push(BlockContent::Stmt(bl_gen_increment_stmt(&index_extended_name, 1, &index_ty)));
            
            // Bound
            blks.push(Block::new(blks_len, num_exec_bound, f_name.to_string(), cur_scope));
            blks_len += 1;
            // Update terminator
            let loop_tail = blks_len - 1;
            let new_id = IdentifierExpression {
                value: index_extended_name,
                span: Span::new("", 0, 0).unwrap()
            };
            let to_expr = array_init_info.len_as_expr(&index_ty).clone();
            let new_to_expr: Expression;
            (blks, blks_len, var_scope_info, new_to_expr, func_count, array_count, struct_count, load_count) = 
                self.bl_gen_expr_::<IS_MAIN>(blks, blks_len, &to_expr, f_name, func_count, array_count, struct_count, load_count, var_scope_info)?;
            let term = BlockTerminator::Transition(
                bl_trans(
                    cond_expr(new_id.clone(), new_to_expr),
                    NextBlock::Label(loop_header), 
                    NextBlock::Label(loop_tail)
                )
            );
            blks[loop_header - 1].terminator = term.clone();
            blks[loop_tail - 1].terminator = term;
        }
        // otherwise assign individual entries
        else {
            let mut index = 0;
            for entry in array_init_info.arr_entries.unwrap() {
                let entry_name = format!("init^{}^{}", cur_array_count, entry);
                let entry_extended_name = var_scope_info.reference_var(&entry_name, &f_name)?.0;
                let new_entry_expr = Expression::Identifier(IdentifierExpression {
                    value: entry_extended_name,
                    span: Span::new("", 0, 0).unwrap()
                });

                let new_index_expr = Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                    value: DecimalNumber {
                        value: index.to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    },
                    suffix: Some(ty_to_dec_suffix(&ty_to_type(&index_ty).unwrap())),
                    span: Span::new("", 0, 0).unwrap()
                }));
                (blks, blks_len) = self.bl_gen_store_(blks, blks_len, &arr_extended_name, &index_ty, &new_index_expr, &new_entry_expr, &entry_ty, f_name, &var_scope_info, is_alloc, &entry_ty, &Vec::new(), read_only)?;
                index += 1;
            }
        }
        Ok((blks, blks_len, var_scope_info, arr_extended_name, func_count, array_count, struct_count, load_count))
    }

    // Given an expression, return its type
    // This is performed after a type check, so assume all typing are correct
    fn bl_gen_type_(
        &'ast self, 
        e: &'ast Expression<'ast>,
        f_name: &str,
        var_scope_info: &VarScopeInfo
    ) -> Result<Ty, String> {
        debug!("Block Gen Type: {}", e.span().as_str());

        let ty = match e {
            Expression::Ternary(t) => {
                let second_ty = self.bl_gen_type_(&t.second, f_name, var_scope_info)?;
                second_ty
            }
            Expression::Binary(b) => {
                let left_ty = self.bl_gen_type_(&b.left, f_name, var_scope_info)?;
                match b.op {
                    BinaryOperator::Eq | BinaryOperator::NotEq | BinaryOperator::Lt | BinaryOperator::Gt | BinaryOperator::Lte | BinaryOperator::Gte => Ty::Bool,
                    _ => left_ty
                }
            }
            Expression::Unary(u) => {
                let expr_ty = self.bl_gen_type_(&u.expression, f_name, var_scope_info)?;
                match u.op {
                    UnaryOperator::ToField(_) => Ty::Field,
                    _ => expr_ty
                }
            }
            Expression::Postfix(p) => {
                // assume no functions in arrays, etc.
                assert!(!p.accesses.is_empty());
                if let Some(Access::Call(_)) = p.accesses.first() {
                    assert!(p.accesses.len() == 1);
                    let (callee_path, callee_name) = self.deref_import(&p.id.value);
                    let callee = self
                    .functions
                    .get(&callee_path)
                    .ok_or_else(|| format!("No file '{:?}' attempting fn call", &callee_path))?
                    .get(&callee_name)
                    .ok_or_else(|| format!("No function '{}' attempting fn call", &callee_name))?;

                    // Get the return type because we need to convert it into a variable
                    let ret_type = callee
                    .returns
                    .first().ok_or("No return type provided for one or more function")?;
                    let ret_ty = self.type_impl_::<false>(&ret_type)?;
                    ret_ty
                } else {
                    let var_name = &p.id.value;
                    let (var_extended_name, mut var_ty) = var_scope_info.reference_var(&var_name, f_name)?;
                    for acc in &p.accesses {
                        var_ty = match acc {
                            Access::Call(_) => {
                                return Err(format!("First order functions not implemented!"));
                            }
                            Access::Select(s) => {
                                if let RangeOrExpression::Expression(_) = &s.expression {
                                    let load_ty = if let Ty::Array(_, _, load_ty) = var_ty {
                                        *load_ty.clone()
                                    } else {
                                        return Err(format!("Loading from a variable {} that is not an array!", var_extended_name));
                                    };
                                    load_ty
                                } else {
                                    return Err(format!("Array range access not implemented!"));
                                }
                            }
                            Access::Member(m) => {
                                let member_name = &m.id.value;
                                let member_ty = if let Ty::Struct(_, members) = var_ty {
                                    members.search(member_name).ok_or_else(|| format!("Member {} does not exist in struct {}!", member_name, var_extended_name))?.1.clone()
                                } else {
                                    return Err(format!("Accessing member {} of a variable {} that is not a struct!", member_name, var_extended_name));
                                };
                                member_ty
                            }
                        };
                    }
                    var_ty
                }
            }
            Expression::Identifier(i) => {
                var_scope_info.reference_var(&i.value.clone(), &f_name)?.1
            }
            Expression::Literal(_) => {
                self.expr_impl_::<false>(&e)?.type_().clone()
            }
            Expression::ArrayInitializer(ai) => {
                let ai_len = self.const_usize_impl_::<false>(&*ai.count);
                let ai_len = if let Ok(ai_len) = ai_len { ai_len } else { 0 };
                Ty::Array(ai.dim_ro.is_some(), ai_len, Box::new(self.bl_gen_type_(&ai.value, f_name, var_scope_info)?)) // array length does not matter
            }
            Expression::InlineArray(ia) => {
                if ia.expressions.len() == 0 {
                    Ty::Array(ia.dim_ro.is_some(), 0, Box::new(Ty::Field))
                }
                else if let SpreadOrExpression::Expression(e) = &ia.expressions[0] {
                    Ty::Array(ia.dim_ro.is_some(), ia.expressions.len(), Box::new(self.bl_gen_type_(e, f_name, var_scope_info)?)) // array length does not matter
                } else {
                    return Err(format!("Spread not supported in inline arrays!"));
                }
            }
            Expression::InlineStruct(is) => {
                let mut struct_ty = Vec::new();
                for member in &is.members {
                    let member_name = member.id.value.to_string();
                    let member_ty = self.bl_gen_type_(&member.expression, f_name, var_scope_info)?;
                    struct_ty.push((member_name, member_ty));
                }
                Ty::Struct(is.ty.value.clone(), FieldList::new(struct_ty))
            }
        };
        Ok(ty)
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

    // Convert a virtual memory operation to circ_ir
    // MODE: LOAD, STORE, DUMMY_LOAD, INIT_STORE
    fn vir_mem_to_circ<const MODE: usize>(
        &'ast self,
        mem_op_count: usize,
        arr: Option<&String>,
        id_expr: Option<&Expression<'ast>>,
        read_only: bool,
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
                value: if read_only {
                    format!("%pm{:06}a", mem_op_count)
                } else {
                    format!("%vm{:06}a", mem_op_count)
                },
                span: Span::new("", 0, 0).unwrap()
            })).unwrap();
            let b = bool(eq(add(lhs_t, offset_t).unwrap(), rhs_t).unwrap()).unwrap();
            self.assert(b).unwrap();
        }
        // LS and TS only applicable if not read_only
        if !read_only {
            // LS
            let ls = if MODE == STORE || MODE == INIT_STORE { STORE } else { LOAD };
            self.bl_gen_assert_const(&format!("%vm{:06}l", mem_op_count), ls);
            // TS, increment if STORE
            if MODE == STORE {
                self.stmt_impl_::<false>(&bl_gen_increment_stmt(W_TS, 1, &Ty::Field)).unwrap();
            }
            self.bl_gen_assert_eq(&W_TS, &format!("%vm{:06}t", mem_op_count));
        }
        // DATA is updated individually by LOAD or STORE
    }

    pub fn inst_to_circ<const ESTIMATE: bool>(&self, 
        i: &BlockContent, 
        f: &str,
        mut wit_count: usize,
        mut phy_mem_op_count: usize,
        mut ro_mem_op_count: usize, 
        mut vir_mem_op_count: usize,
    ) -> (usize, usize, usize, usize) {
        debug!("Inst to Circ: {:?}", i);
        match i {
            BlockContent::Witness((var, ty, alive)) => {
                // Witness statements are never in brnaches, so can be declared sequentially
                if *alive {
                    // Non-deterministically supply WIT
                    self.circ_declare_input(
                        &f,
                        format!("%wt{:06}", wit_count),
                        if let Ty::Array(..) = ty { &Ty::Field } else { ty },
                        ZVis::Private(0),
                        None,
                        true,
                        &None,
                    ).unwrap();
                    // Assign VAR to WIT
                    let e = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                        value: format!("%wt{:06}", wit_count),
                        span: Span::new("", 0, 0).unwrap()
                    })).unwrap();
                    self.declare_init_impl_::<false>(
                        var.clone(),
                        ty.clone(),
                        e,
                    ).unwrap();
                    wit_count += 1;
                }
            }
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
            BlockContent::ArrayInit((arr, _, len_expr, read_only)) => {
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
                } else {
                    // If read_only, allocate on stack (%SP), otherwise allocate on virtual memory (%AS)
                    let mem_pointer = if *read_only { W_SP } else { W_AS };
                    // Declare the array as a pointer (field), set to mem_pointer
                    let as_expr = Expression::Identifier(IdentifierExpression {
                        value: mem_pointer.to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    });
                    let as_t = self.expr_impl_::<false>(&as_expr).unwrap();
                    self.declare_init_impl_::<false>(
                        arr.to_string(),
                        Ty::Field,
                        as_t.clone(),
                    ).unwrap();
                    // Increment mem_pointer by size of array
                    let mut len_t = self.expr_impl_::<false>(&len_expr).unwrap();
                    if len_t.type_() != &Ty::Field {
                        len_t = uint_to_field(len_t).unwrap();
                    }
                    let new_as_t = add(as_t, len_t).unwrap();
                    self.assign_impl_::<false>(mem_pointer, &[][..], new_as_t, false).unwrap();
                }
            }
            BlockContent::Store((val_expr, _, arr, id_expr, init, read_only)) => {
                if ESTIMATE {}
                else {
                    let rhs_t = if *read_only {
                        // ADDR
                        self.vir_mem_to_circ::<STORE>(
                            ro_mem_op_count,
                            Some(&arr),
                            Some(&id_expr),
                            *read_only,
                        );
                        let rhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                            value: format!("%pm{:06}v", ro_mem_op_count),
                            span: Span::new("", 0, 0).unwrap()
                        })).unwrap();
                        // Update Label
                        ro_mem_op_count += 1;
                        rhs_t
                    } else {
                        // ADDR, LS, & TS
                        if *init {
                            self.vir_mem_to_circ::<INIT_STORE>(
                                vir_mem_op_count,
                                Some(&arr),
                                Some(&id_expr),
                                *read_only,
                            );
                        } else {
                            self.vir_mem_to_circ::<STORE>(
                                vir_mem_op_count,
                                Some(&arr),
                                Some(&id_expr),
                                *read_only,
                            );
                        }
                        let rhs_t = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                            value: format!("%vm{:06}d", vir_mem_op_count),
                            span: Span::new("", 0, 0).unwrap()
                        })).unwrap();
                        // Update Label
                        vir_mem_op_count += 1;
                        rhs_t
                    };

                    // Assert correctness of DATA, always stored as Field
                    let mut lhs_t = self.expr_impl_::<false>(&val_expr).unwrap();
                    if lhs_t.type_() != &Ty::Field {
                        lhs_t = uint_to_field(lhs_t).unwrap();
                    }
                    let b = bool(eq(lhs_t, rhs_t).unwrap()).unwrap();
                    self.assert(b).unwrap();
                }
            }
            BlockContent::Load((val, ty, arr, id_expr, read_only)) => {
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
                    let mut e = if *read_only {
                        // ADDR
                        self.vir_mem_to_circ::<LOAD>(
                            ro_mem_op_count,
                            Some(&arr),
                            Some(&id_expr),
                            *read_only,
                        );
                        // Assign LOAD value to data
                        let e = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                            value: format!("%pm{:06}v", ro_mem_op_count),
                            span: Span::new("", 0, 0).unwrap()
                        })).unwrap();
                        ro_mem_op_count += 1;
                        e
                    } else {
                        // ADDR, LS, & TS
                        self.vir_mem_to_circ::<LOAD>(
                            vir_mem_op_count,
                            Some(&arr),
                            Some(&id_expr),
                            *read_only,
                        );
                        // Assign LOAD value to data
                        let e = self.expr_impl_::<false>(&Expression::Identifier(IdentifierExpression {
                            value: format!("%vm{:06}d", vir_mem_op_count),
                            span: Span::new("", 0, 0).unwrap()
                        })).unwrap();
                        vir_mem_op_count += 1;
                        e
                    };
                    // Convert the loaded value to the correct type
                    e = field_to_ty(e, &ty).unwrap();
                    self.declare_init_impl_::<false>(
                        val.clone(),
                        ty.clone(),
                        e,
                    ).unwrap();
                }
            }
            BlockContent::DummyLoad(read_only) => {
                // ADDR, LS, & TS
                self.vir_mem_to_circ::<DUMMY_LOAD>(
                    if *read_only { ro_mem_op_count } else { vir_mem_op_count },
                    None,
                    None,
                    *read_only,
                );
                if *read_only {
                    ro_mem_op_count += 1;
                } else {
                    vir_mem_op_count += 1;
                }
            }
            BlockContent::Branch((cond, if_insts, else_insts)) => {
                let cond = self.expr_impl_::<false>(&cond).unwrap();
                let cbool = bool(cond.clone()).unwrap();

                // Mem_ops overlap in two branches
                let mut if_wit_count = wit_count;
                let mut else_wit_count = wit_count;
                let mut if_phy_mem_op_count = phy_mem_op_count;
                let mut if_ro_mem_op_count = ro_mem_op_count;
                let mut if_vir_mem_op_count = vir_mem_op_count;
                let mut else_phy_mem_op_count = phy_mem_op_count;
                let mut else_ro_mem_op_count = ro_mem_op_count;
                let mut else_vir_mem_op_count = vir_mem_op_count;

                self.circ_enter_condition(cbool.clone());
                for i in if_insts {
                    (if_wit_count, if_phy_mem_op_count, if_ro_mem_op_count, if_vir_mem_op_count) = self.inst_to_circ::<ESTIMATE>(i, f, wit_count, if_phy_mem_op_count, if_ro_mem_op_count, if_vir_mem_op_count);
                }
                self.circ_exit_condition();
                self.circ_enter_condition(term![NOT; cbool]);
                for i in else_insts {
                    (else_wit_count, else_phy_mem_op_count, else_ro_mem_op_count, else_vir_mem_op_count) = self.inst_to_circ::<ESTIMATE>(i, f, wit_count, else_phy_mem_op_count, else_ro_mem_op_count, else_vir_mem_op_count);
                }
                self.circ_exit_condition();

                // No witness should be declared in branches
                assert_eq!(if_wit_count, wit_count);
                assert_eq!(else_wit_count, wit_count);
                // No phy_op should every occur in branches, and the same amount of vir_op should occur in two branches
                assert_eq!(if_phy_mem_op_count, phy_mem_op_count);
                assert_eq!(else_phy_mem_op_count, phy_mem_op_count);
                assert_eq!(if_ro_mem_op_count, else_ro_mem_op_count);
                assert_eq!(if_vir_mem_op_count, else_vir_mem_op_count);

                phy_mem_op_count = if_phy_mem_op_count;
                ro_mem_op_count = if_ro_mem_op_count;
                vir_mem_op_count = if_vir_mem_op_count;
            }
            BlockContent::Stmt(stmt) => {
                self.stmt_impl_::<false>(&stmt).unwrap();
            }
        }
        (wit_count, phy_mem_op_count, ro_mem_op_count, vir_mem_op_count)
    }

    // Convert a block to circ_ir
    // This can be done to either produce the constraints, or to estimate the size of constraints
    // In estimation mode, we rename all output variable from X -> oX, add assertion, and process the terminator
    pub fn bl_to_circ<const ESTIMATE: bool>(&self, b: &Block, f: &str) {
        debug!("Bl to Circ: {}", b.name);

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
                    // Declare arrays as field
                    if let Ty::Array(..) = x { &Ty::Field } else { x },
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
                        // Declare arrays as field
                        if let Ty::Array(..) = x { &Ty::Field } else { x },
                        ZVis::Public,
                        None,
                        true,
                        &None,
                    );
                    r.unwrap();
                }
            }
        }

        // How many witnesses have we encountered?
        let mut wit_count = 0;
        // How many scoping memory operations have we encountered? Counter starts at b.num_ro_ops
        let mut phy_mem_op_count = b.num_ro_ops;
        // How many read-only memory operations have we encountered?
        let mut ro_mem_op_count = 0;
        // How many virtual memory operations have we encountered?
        let mut vir_mem_op_count = 0;
        
        // Declare all read-only memory accesses to avoid dealing with branching
        for i in 0..b.num_ro_ops {
            // Declare the next ADDR and DATA
            // VIR_ADDR as 'a'
            self.circ_declare_input(
                f,
                format!("%pm{:06}a", i),
                &Ty::Field,
                ZVis::Private(0),
                None,
                true,
                &None,
            ).unwrap();
            // VAL as 'd'
            self.circ_declare_input(
                f,
                format!("%pm{:06}v", i),
                &Ty::Field,
                ZVis::Private(0),
                None,
                true,
                &None,
            ).unwrap();
        }
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
            (wit_count, phy_mem_op_count, ro_mem_op_count, vir_mem_op_count) = self.inst_to_circ::<ESTIMATE>(i, f, wit_count, phy_mem_op_count, ro_mem_op_count, vir_mem_op_count);
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
                        if let Ty::Array(..) = x { &Ty::Field } else { x },
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