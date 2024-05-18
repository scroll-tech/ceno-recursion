// Multiple problems with liveness analysis:
// A declaration is dead, but assignments are alive
// PUSH is not equivalent to a change in scope. Instead of popping out the last state,
// PUSH should result in the union of the last two states.

use std::collections::VecDeque;
use zokrates_pest_ast::*;
use crate::front::zsharp::blocks::*;
use std::collections::{HashMap, HashSet, BTreeMap, BTreeSet};
use crate::front::zsharp::Ty;
use itertools::Itertools;
use std::cmp::max;
use std::iter::FromIterator;

use crate::front::zsharp::ZGen;
use crate::front::Computations;
use crate::target::r1cs::trans::to_r1cs;
use crate::front::zsharp::cfg;

use crate::front::zsharp::ZSharp;

const MIN_BLOCK_SIZE: usize = 1024;
const CFG_VERBOSE: bool = false;

fn type_to_ty(t: Type) -> Result<Ty, String> {
    match t {
        Type::Basic(BasicType::U8(_)) => Ok(Ty::Uint(8)),
        Type::Basic(BasicType::U16(_)) => Ok(Ty::Uint(16)),
        Type::Basic(BasicType::U32(_)) => Ok(Ty::Uint(32)),
        Type::Basic(BasicType::U64(_)) => Ok(Ty::Uint(64)),
        Type::Basic(BasicType::Boolean(_)) => Ok(Ty::Bool),
        Type::Basic(BasicType::Field(_)) => Ok(Ty::Field),
        Type::Array(_) => Err(format!("Arrays not supported")),
        Type::Struct(_) => Err(format!("Structs not supported")),
    }
}

fn print_cfg(
    successor: &Vec<HashSet<usize>>,
    predecessor: &Vec<HashSet<usize>>,
    exit_bls: &HashSet<usize>,
    entry_bls_fn: &HashSet<usize>,
    successor_fn: &Vec<HashSet<usize>>,
    predecessor_fn: &Vec<HashSet<usize>>,
    exit_bls_fn: &HashSet<usize>,
) {
    println!("\n\n--\nControl Flow Graph:");
    println!("\nSuccessor:");
    for s in 0..successor.len() {
        print!("Block {}: prog [ ", s);
        for b in successor[s].iter() {
            print!("{} ", *b);
        }
        print!("]; in-func [ ");
        for b in successor_fn[s].iter() {
            print!("{} ", *b);
        }
        println!("]");
    }
    println!("\nPredecessor:");
    for s in 0..predecessor.len() {
        print!("Block {}: prog [ ", s);
        for b in predecessor[s].iter() {
            print!("{} ", *b);
        }
        print!("]; in-func [ ");
        for b in predecessor_fn[s].iter() {
            print!("{} ", *b);
        }
        println!("]");
    }
    print!("\nExit Blocks:");
    for b in exit_bls {
        print!(" {}", *b);
    }
    println!();
    print!("\nFunction Entry Blocks:");
    for b in entry_bls_fn {
        print!(" {}", *b);
    }
    println!();
    print!("\nFunction Exit Blocks:");
    for b in exit_bls_fn {
        print!(" {}", *b);
    }
    println!();
}

fn print_bls(bls: &Vec<Block>, entry_bl: &usize) {
    println!("Entry block: {entry_bl}");  
    for b in bls {
        b.pretty();
        println!("");
    }    
}

// --
// HELPER FUNCTIONS
// --
// If bc is a statement of form field %RP = val,
// return val
fn rp_find_val(bc: BlockContent) -> Option<usize> {
    // We can ignore memory for now
    // The only case currently is %RP on the left & constant on the right
    if let BlockContent::Stmt(Statement::Definition(d)) = bc {
        if let TypedIdentifierOrAssignee::TypedIdentifier(ty) = &d.lhs[0] {
            if ty.identifier.value == "%RP".to_string() {
                if let Expression::Literal(LiteralExpression::DecimalLiteral(dle)) = &d.expression {
                    let tmp_bl: usize = dle.value.value.trim().parse().expect("Dead Block Elimination failed: %RP is assigned to a non-constant value");
                    return Some(tmp_bl);
                } else {
                    panic!("Dead Block Elimination failed: %RP is assigned to a non-constant value")
                }
            }
        }
        if let TypedIdentifierOrAssignee::Assignee(a) = &d.lhs[0] {
            if a.id.value == "%RP".to_string() {
                if let Expression::Literal(LiteralExpression::DecimalLiteral(dle)) = &d.expression {
                    let tmp_bl: usize = dle.value.value.trim().parse().expect("Dead Block Elimination failed: %RP is assigned to a non-constant value");
                    return Some(tmp_bl);
                } else {
                    panic!("Dead Block Elimination failed: %RP is assigned to a non-constant value")
                }
            }
        }
    }
    return None;
}

// If bc is a statement of form %RP = old_val and old_val is a key in val_map,
// replace it with %RP = val_map[val]
fn rp_replacement_stmt(bc: BlockContent, val_map: HashMap<usize, usize>) -> Option<BlockContent> {
    if let BlockContent::Stmt(Statement::Definition(d)) = bc {
        let mut is_rp = false;
        if let TypedIdentifierOrAssignee::Assignee(a) = &d.lhs[0] {
            if a.id.value == "%RP".to_string() {
                is_rp = true;
            }
        }
        if let TypedIdentifierOrAssignee::TypedIdentifier(ty) = &d.lhs[0] {
            if ty.identifier.value == "%RP".to_string() {
                is_rp = true;
            }
        }
        if is_rp {
            if let Expression::Literal(LiteralExpression::DecimalLiteral(dle)) = &d.expression {
                let tmp_bl: usize = dle.value.value.trim().parse().unwrap();
                if let Some(new_bl) = val_map.get(&tmp_bl) {
                    let new_rp_stmt = Statement::Definition(DefinitionStatement {
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
                                value: new_bl.to_string(),
                                span: Span::new("", 0, 0).unwrap()
                            },
                            suffix: Some(DecimalSuffix::Field(FieldSuffix {
                                span: Span::new("", 0, 0).unwrap()
                            })),
                            span: Span::new("", 0, 0).unwrap()
                        })),
                        span: Span::new("", 0, 0).unwrap()
                    });
                    return Some(BlockContent::Stmt(new_rp_stmt));
                }
            }
        }
    }
    return None;
}

// Given an expression consisted of only ternary, literals, and identifiers,
// Find all the literal values and %RP it mentioned
fn bl_trans_find_val(e: &Expression) -> Vec<NextBlock> {
    match e {
        Expression::Ternary(te) => {
            let mut ret = bl_trans_find_val(&te.second);
            ret.append(&mut bl_trans_find_val(&te.third));
            return ret;
        }
        Expression::Literal(le) => {
            if let LiteralExpression::DecimalLiteral(dle) = le {
                let val: usize = dle.value.value.trim().parse().expect("Dead Block Elimination failed: %RP is assigned to a non-constant value");
                return vec![NextBlock::Label(val)];
            } else { panic!("Unexpected value in Block Transition") }
        }
        Expression::Identifier(ie) => {
            if ie.value == "%RP".to_string() {
                return vec![NextBlock::Rp]
            } else {
                panic!("Unexpected variable in Block Transition")
            }
        }
        _ => { panic!("Unexpected expression in Block Transition") }
    }
}

// Given an expression consisted of only ternary, literals, and identifiers,
// Replace all literal values according to label_map
// Skip all %RP or other references to variables
fn bl_trans_map<'ast>(e: &Expression<'ast>, label_map: &HashMap<usize, usize>) -> Expression<'ast> {
    match e {
        Expression::Ternary(te) => {
            let new_second = bl_trans_map(&te.second, label_map);
            let new_third = bl_trans_map(&te.third, label_map);
            if new_second == new_third {
                return new_second;
            } else {
                return Expression::Ternary(TernaryExpression {
                    first: Box::new(*te.first.clone()),
                    second: Box::new(new_second),
                    third: Box::new(new_third),
                    span: e.span().clone()
                });
            }
        }
        Expression::Literal(le) => {
            if let LiteralExpression::DecimalLiteral(dle) = le {
                let val: usize = dle.value.value.trim().parse().expect("Dead Block Elimination failed: %RP is assigned to a non-constant value");
                return bl_coda(NextBlock::Label(*label_map.get(&val).unwrap()));
            } else { panic!("Unexpected value in Block Transition") }
        }
        Expression::Identifier(_) => {
            return e.clone();
        }
        _ => { panic!("Unexpected expression in Block Transition") }
    }
}

// Given an expression consisted of only ternary, literals, and identifiers,
// Replace all occurrences of old_val to new_val, which is an expression
// I don't think we can combine bl_trans_map and bl_trans_replace together efficiently.
fn bl_trans_replace<'ast>(e: &Expression<'ast>, old_val: usize, new_val: &Expression<'ast>) -> Expression<'ast> {
    match e {
        Expression::Ternary(te) => {
            let new_second = bl_trans_replace(&te.second, old_val, new_val);
            let new_third = bl_trans_replace(&te.third, old_val, new_val);
            if new_second == new_third {
                return new_second;
            } else {
                return Expression::Ternary(TernaryExpression {
                    first: Box::new(*te.first.clone()),
                    second: Box::new(new_second),
                    third: Box::new(new_third),
                    span: e.span().clone()
                });
            }
        }
        Expression::Literal(le) => {
            if let LiteralExpression::DecimalLiteral(dle) = le {
                let val: usize = dle.value.value.trim().parse().expect("Dead Block Elimination failed: %RP is assigned to a non-constant value");
                if val == old_val {
                    return new_val.clone();
                } else {
                    return e.clone();
                }
            } else { panic!("Unexpected value in Block Transition") }
        }
        Expression::Identifier(_) => {
            return e.clone();
        }
        _ => { panic!("Unexpected expression in Block Transition") }
    }
}

// Sort functions in topological order
fn top_sort_helper(
    cur_name: &str,
    call_graph: &HashMap<String, HashSet<String>>,
    mut visited: HashMap<String, bool>,
    mut chain: Vec<String>
) -> (Vec<String>, HashMap<String, bool>) {
    visited.insert(cur_name.to_string(), true);
    for s in call_graph.get(cur_name).unwrap() {
        if !visited.get(s).unwrap() {
            (chain, visited) = top_sort_helper(s, call_graph, visited, chain);
        }
    }
    chain.insert(0, cur_name.to_string());
    return (chain, visited);
}

fn _fn_top_sort(
    bls: &Vec<Block>,
    successor: &Vec<HashSet<usize>>,
    successor_fn: &Vec<HashSet<usize>>,
) -> Vec<String> {
    // First construct function call graph
    let mut fn_call_graph: HashMap<String, HashSet<String>> = HashMap::new();
    // Initialize every function to NOT VISITED
    let mut visited = HashMap::new();
    fn_call_graph.insert("main".to_string(), HashSet::new());
    for cur_bl in 0..bls.len() {
        let b = &bls[cur_bl];
        let caller_name = b.fn_name.to_string();
        if !visited.contains_key(&caller_name) {
            visited.insert(caller_name.to_string(), false);
            fn_call_graph.insert(caller_name.to_string(), HashSet::new());
        }
        // if cur_bl is a caller of a function, add the call to call graph
        if successor_fn[cur_bl].len() != 0 && successor_fn[cur_bl] != successor[cur_bl] {
            assert_eq!(successor[cur_bl].len(), 1);
            assert_eq!(successor_fn[cur_bl].len(), 1);
            let callee_name = bls[Vec::from_iter(successor[cur_bl].clone())[0]].fn_name.to_string();

            let mut callee_list = fn_call_graph.get(&caller_name).unwrap().clone();
            callee_list.insert(callee_name);
            fn_call_graph.insert(caller_name, callee_list);
        }
    }
    // Next perform top sort using call graph
    top_sort_helper("main", &fn_call_graph, visited, Vec::new()).0
}

// Given an expression, find all variables it references
fn expr_find_val(e: &Expression) -> HashSet<String> {
    match e {
        Expression::Ternary(t) => {
            let mut ret: HashSet<String> = expr_find_val(&t.first);
            ret.extend(expr_find_val(&t.second));
            ret.extend(expr_find_val(&t.third));
            ret
        }
        Expression::Binary(b) => {
            let mut ret: HashSet<String> = expr_find_val(&b.left);
            ret.extend(expr_find_val(&b.right));
            ret
        }
        Expression::Unary(u) => expr_find_val(&u.expression),
        Expression::Postfix(p) => {
            let mut ret: HashSet<String> = HashSet::new();
            ret.insert(p.id.value.clone());
            for aa in &p.accesses {
                if let Access::Select(a) = aa {
                    if let RangeOrExpression::Expression(e) = &a.expression {
                        ret.extend(expr_find_val(e));
                    } else {
                        panic!("Range access not supported.")
                    }
                } else {
                    panic!("Unsupported membership access.")
                }
            }
            ret
        }
        Expression::Identifier(i) => {
            let mut ret: HashSet<String> = HashSet::new();
            ret.insert(i.value.clone());
            ret
        }
        Expression::Literal(_) => HashSet::new(),
        _ => {
            panic!("Unsupported Expression.");
        }
    }
}

// Given a statement, find all variables it defines and references
// Return value:
// ret[0]: all variables that S defines (KILL)
// ret[1]: all variables that S references (GEN)
fn stmt_find_val(s: &Statement) -> (HashSet<String>, HashSet<String>) {
    match s {
        Statement::Return(_) => {
            panic!("Blocks should not contain return statements.")
        }
        Statement::Definition(d) => {
            let mut kill_set = HashSet::new();
            for l in &d.lhs {
                match l {
                    TypedIdentifierOrAssignee::Assignee(p) => {
                        kill_set.insert(p.id.value.clone());
                        for aa in &p.accesses {
                            if let AssigneeAccess::Select(a) = aa {
                                if let RangeOrExpression::Expression(e) = &a.expression {
                                    kill_set.extend(expr_find_val(e));
                                } else {
                                    panic!("Range access not supported.")
                                }
                            } else {
                                panic!("Unsupported membership access.")
                            }
                        }
                    }
                    TypedIdentifierOrAssignee::TypedIdentifier(ti) => {
                        kill_set.insert(ti.identifier.value.clone());
                    }
                }
            }
            (kill_set, expr_find_val(&d.expression))
        }
        Statement::Assertion(a) => (HashSet::new(), expr_find_val(&a.expression)),
        Statement::Conditional(c) => {
            // KILL is empty
            // GEN is the union of the two branches
            // Iterate through if branch
            let mut if_gen_set = HashSet::new();
            for s in c.ifbranch.iter().rev() {
                let (kill, gen) = stmt_find_val(&s);
                if_gen_set = la_kill(if_gen_set, &kill);
                if_gen_set = la_gen(if_gen_set, &gen);
            }
            let mut else_gen_set = HashSet::new();
            for s in c.elsebranch.iter().rev() {
                let (kill, gen) = stmt_find_val(&s);
                else_gen_set = la_kill(else_gen_set, &kill);
                else_gen_set = la_gen(else_gen_set, &gen);
            }
            let mut gen_set = HashSet::new();
            gen_set.extend(if_gen_set);
            gen_set.extend(else_gen_set);
            gen_set.extend(expr_find_val(&c.condition));
            (HashSet::new(), gen_set)
        }
        Statement::Iteration(_) => { panic!("Blocks should not contain iteration statements.") }
        Statement::WhileLoop(_) => { panic!("Blocks should not contain while loop statements.") }
        Statement::CondStore(_) => { panic!("Blocks should not contain conditional store statements.") }
    }
}

// Given a statement, decide if it is of form %SP = %SP + x
fn is_sp_push(s: &Statement) -> bool {
    if let Statement::Definition(d) = s {
        let mut is_sp = false;
        if let TypedIdentifierOrAssignee::Assignee(a) = &d.lhs[0] {
            if a.id.value == "%SP".to_string() {
                is_sp = true;
            }
        }
        if let TypedIdentifierOrAssignee::TypedIdentifier(ty) = &d.lhs[0] {
            if ty.identifier.value == "%SP".to_string() {
                is_sp = true;
            }
        }
        if is_sp {
            if let Expression::Binary(b) = &d.expression {
                if let Expression::Identifier(ie) = &*b.left {
                    if ie.value == "%SP".to_string() && b.op == BinaryOperator::Add {
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

// Given a statement, decide if it is of form %BP = %SP
fn is_bp_update(s: &Statement) -> bool {
    if let Statement::Definition(d) = s {
        if let TypedIdentifierOrAssignee::TypedIdentifier(td) = &d.lhs[0] {
            if td.identifier.value == "%BP".to_string() {
                if let Expression::Identifier(ie) = &d.expression {
                    if ie.value == "%SP".to_string() {
                        return true;
                    }
                }
            }
        }
        if let TypedIdentifierOrAssignee::Assignee(a) = &d.lhs[0] {
            if a.id.value == "%BP".to_string() {
                if let Expression::Identifier(ie) = &d.expression {
                    if ie.value == "%SP".to_string() {
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

// Liveness analysis
// GEN all variables in gen
fn la_gen(
    mut state: HashSet<String>,
    gen: &HashSet<String>
) -> HashSet<String> {
    // Add all gens to state
    state.extend(gen.clone());
    state
}

// KILL all variables in kill
fn la_kill(
    mut state: HashSet<String>,
    kill: &HashSet<String>
) -> HashSet<String> {
    // Remove all kills to state
    for v in kill {
        state.remove(v);
    }
    state
}

// Decide if var is alive in the current scope given state
fn is_alive(
    state: &HashSet<String>,
    var: &String
) -> bool {
    state.get(var) != None
}

// Join for block merge
fn bm_join(
    state: Option<usize>,
    other: usize
) -> Option<usize> {
    if let Some(cur_state) = state {
        if cur_state != other { Some(0) }
        else { Some(other) }
    } else { Some(other) }
}

// Convert a terminator into a list of instructions
// Returns the constructed statement as well as how many times it should repeat (if in a loop)
fn term_to_instr<'ast>(
    bls: &Vec<Block>,
    term: &Expression<'ast>,
    instr_list: &Vec<Vec<BlockContent<'ast>>>,
    cur_bl: usize,
) -> (Vec<BlockContent<'ast>>, usize) {
    // There are three cases for the terminator
    // A ternary should be converted to an if / else statement
    // A constant literal should be converted to the corresponding instruction list x looping
    // Any reference to %RP should result in the termination of the conversion
    match term {
        Expression::Ternary(t) => {
            let (left_instr, left_repeat) = term_to_instr(bls, &t.second, instr_list, cur_bl);
            let (right_instr, right_repeat) = term_to_instr(bls, &t.third, instr_list, cur_bl);
            // If both left and right are empty, don't construct if / else
            if left_instr.len() == 0 && right_instr.len() == 0 {
                return (Vec::new(), 1);
            }

            // Restrictions on loop structure
            assert_eq!(right_repeat, 1);
            assert!(left_repeat == 1 || right_instr.len() == 0);

            // No memory ops should be contained within left_instr & right_instr
            let left_stmt = left_instr.iter().map(|i|
                if let BlockContent::Stmt(s) = i { s.clone() } else { panic!{"Terminator to instruction failed: branch blocks should not contain memory operations!"} }
            ).collect();
            let right_stmt = right_instr.iter().map(|i|
                if let BlockContent::Stmt(s) = i { s.clone() } else { panic!{"Terminator to instruction failed: branch blocks should not contain memory operations!"} }
            ).collect();
            let cond_stmt = Statement::Conditional(ConditionalStatement {
                condition: *t.first.clone(),
                ifbranch: left_stmt,
                dummy: Vec::new(),
                elsebranch: right_stmt,
                span: Span::new("", 0, 0).unwrap()
            });

            (vec![BlockContent::Stmt(cond_stmt); left_repeat], 1)
        }
        Expression::Literal(le) => {
            if let LiteralExpression::DecimalLiteral(dle) = le {
                let cur_scope = bls[cur_bl].scope;
                let next_bl: usize = dle.value.value.parse().unwrap();
                let next_scope = bls[next_bl].scope;
                if next_scope > cur_scope {
                    // Copy from instr_list only if scope of next_bl is higher than cur_scope
                    // DO NOT unroll the loops here. We need to unroll with the condition
                    (instr_list[next_bl].clone(), bls[next_bl].fn_num_exec_bound / bls[cur_bl].fn_num_exec_bound)
                } else {
                    (Vec::new(), 1)
                }
            } else {
                panic!("Terminator to instruction failed: terminator cannot contain boolean or hex")
            }
        }
        Expression::Identifier(_) => {
            panic!("Terminator to instruction failed: cannot merge blocks terminating in %RP")
        }
        _ => { panic!("Terminator to instruction failed: terminator must be ternary, literal, or %RP") }
    }
}

// New io map with only reserved registers
// Reserve registers 0 - 7 for %V, %BN, %RET, %TS, %AS, %RP, %SP, and %BP
fn new_io_map() -> HashMap<String, usize> {
    let mut io_map: HashMap<String, usize> = HashMap::new();
    (_, io_map, _) = var_name_to_reg_id_expr::<1>("%V".to_string(), io_map);
    (_, io_map, _) = var_name_to_reg_id_expr::<1>("%BN".to_string(), io_map);
    (_, io_map, _) = var_name_to_reg_id_expr::<1>("%RET".to_string(), io_map);
    (_, io_map, _) = var_name_to_reg_id_expr::<1>("%TS".to_string(), io_map);
    (_, io_map, _) = var_name_to_reg_id_expr::<1>("%AS".to_string(), io_map);
    (_, io_map, _) = var_name_to_reg_id_expr::<1>("%RP".to_string(), io_map);
    (_, io_map, _) = var_name_to_reg_id_expr::<1>("%SP".to_string(), io_map);
    (_, io_map, _) = var_name_to_reg_id_expr::<1>("%BP".to_string(), io_map);

    io_map
}

// New witness map with only reserved registers
// Reserve registers 0 - 5 for %RET, %TS, %AS, %RP, %SP, and %BP
fn new_witness_map() -> HashMap<String, usize> {
    let mut witness_map: HashMap<String, usize> = HashMap::new();
    (_, witness_map, _) = var_name_to_reg_id_expr::<0>("%RET".to_string(), witness_map);
    (_, witness_map, _) = var_name_to_reg_id_expr::<0>("%TS".to_string(), witness_map);
    (_, witness_map, _) = var_name_to_reg_id_expr::<0>("%AS".to_string(), witness_map);
    (_, witness_map, _) = var_name_to_reg_id_expr::<0>("%RP".to_string(), witness_map);
    (_, witness_map, _) = var_name_to_reg_id_expr::<0>("%SP".to_string(), witness_map);
    (_, witness_map, _) = var_name_to_reg_id_expr::<0>("%BP".to_string(), witness_map);

    witness_map
}

// Turn all variables in a statement to a register reference
// Whenever we meet a variable X, if reg_map contains X and scope_map[X] = Y, update X to %Y
// otherwise, update X to %<reg_size> and add X to reg_map
// Returns the new statement and new reg_map
fn var_to_reg_stmt<'ast>(
    s: &Statement<'ast>, 
    mut reg_map: HashMap<String, usize>, 
) -> (Statement<'ast>, HashMap<String, usize>) {
    match s {
        Statement::Return(_) => {
            panic!("Blocks should not contain return statements.");
        }
        Statement::Assertion(a) => {
            let new_expr: Expression;
            (new_expr, reg_map) = var_to_reg_expr(&a.expression, reg_map);
            let new_stmt = AssertionStatement {
                expression: new_expr,
                message: a.message.clone(),
                span: a.span
            };
            (Statement::Assertion(new_stmt), reg_map)
        }
        Statement::Conditional(c) => {
            let new_cond: Expression;
            (new_cond, reg_map) = var_to_reg_expr(&c.condition, reg_map);
            let mut new_ifbranch = Vec::new();
            for s in &c.ifbranch {
                let new_stmt: Statement;
                (new_stmt, reg_map) = var_to_reg_stmt(s, reg_map);
                new_ifbranch.push(new_stmt);
            }
            let mut new_elsebranch = Vec::new();
            for s in &c.elsebranch {
                let new_stmt: Statement;
                (new_stmt, reg_map) = var_to_reg_stmt(s, reg_map);
                new_elsebranch.push(new_stmt);
            }
            let new_stmt = ConditionalStatement {
                condition: new_cond,
                ifbranch: new_ifbranch,
                dummy: Vec::new(),
                elsebranch: new_elsebranch,
                span: Span::new("", 0, 0).unwrap()
            };
            (Statement::Conditional(new_stmt), reg_map)
        }
        Statement::Iteration(_) => { panic!("Blocks should not contain iteration statements.") }
        Statement::WhileLoop(_) => { panic!("Blocks should not contain while loop statements.") }
        Statement::Definition(d) => {
            let mut new_lhs: Vec<TypedIdentifierOrAssignee> = Vec::new();
            for l in &d.lhs {
                match l {
                    TypedIdentifierOrAssignee::TypedIdentifier(tid) => {
                        let new_id_expr: IdentifierExpression;
                        (new_id_expr, reg_map) = var_to_reg_id_expr(&tid.identifier, reg_map);
                        new_lhs.push(TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier{
                            ty: tid.ty.clone(),
                            identifier: new_id_expr,
                            span: tid.span
                        }));
                    }
                    TypedIdentifierOrAssignee::Assignee(p) => {
                        let new_id_expr: IdentifierExpression;
                        (new_id_expr, reg_map) = var_to_reg_id_expr(&p.id, reg_map);
                        let mut new_accesses: Vec<AssigneeAccess> = Vec::new();
                        for aa in &p.accesses {
                            if let AssigneeAccess::Select(a) = aa {
                                if let RangeOrExpression::Expression(e) = &a.expression {
                                    let new_expr: Expression;
                                    (new_expr, reg_map) = var_to_reg_expr(&e, reg_map);
                                    new_accesses.push(AssigneeAccess::Select(ArrayAccess {
                                        expression: RangeOrExpression::Expression(new_expr),
                                        span: a.span
                                    }))
                                } else {
                                    panic!("Range access not supported.")
                                }
                            } else {
                                panic!("Unsupported membership access.")
                            }
                        }
                        new_lhs.push(TypedIdentifierOrAssignee::Assignee(Assignee{
                            id: new_id_expr,
                            accesses: new_accesses,
                            span: p.span
                        }));
                    }
                }
            }
            let new_expr: Expression;
            (new_expr, reg_map) = var_to_reg_expr(&d.expression, reg_map);
            let new_stmt = DefinitionStatement {
                lhs: new_lhs,
                expression: new_expr,
                span: d.span
            };
            (Statement::Definition(new_stmt), reg_map)
        }
        Statement::CondStore(_) => { panic!("Blocks should not contain conditional store statements.") }
    }
}

// Turn all variables in an expression to a register reference
// Whenever we meet a variable X, if reg_map contains X and scope_map[X] = Y, update X to %Y
// otherwise, update X to %<reg_size> and add X to reg_map
// Returns the new expression and new reg_map
fn var_to_reg_expr<'ast>(
    e: &Expression<'ast>, 
    mut reg_map: HashMap<String, usize>, 
) -> (Expression<'ast>, HashMap<String, usize>) {
    match e {
        Expression::Ternary(t) => {
            let new_first: Expression;
            let new_second: Expression;
            let new_third: Expression;
            (new_first, reg_map) = var_to_reg_expr(&t.first, reg_map);
            (new_second, reg_map) = var_to_reg_expr(&t.second, reg_map);
            (new_third, reg_map) = var_to_reg_expr(&t.third, reg_map);
            return (Expression::Ternary(TernaryExpression {
                first: Box::new(new_first),
                second: Box::new(new_second),
                third: Box::new(new_third),
                span: t.span
            }), reg_map);
        }
        Expression::Binary(b) => {
            let new_left: Expression;
            let new_right: Expression;
            (new_left, reg_map) = var_to_reg_expr(&b.left, reg_map);
            (new_right, reg_map) = var_to_reg_expr(&b.right, reg_map);
            return (Expression::Binary(BinaryExpression {
                op: b.op.clone(),
                left: Box::new(new_left),
                right: Box::new(new_right),
                span: b.span
            }), reg_map);
        }
        Expression::Unary(u) => {
            let new_expr: Expression;
            (new_expr, reg_map) = var_to_reg_expr(&u.expression, reg_map);
            return (Expression::Unary(UnaryExpression {
                op: u.op.clone(),
                expression: Box::new(new_expr),
                span: u.span
            }), reg_map);
        }
        Expression::Postfix(p) => {
            let mut new_accesses = Vec::new();
            for aa in &p.accesses {
                if let Access::Select(a) = aa {
                    if let RangeOrExpression::Expression(e) = &a.expression {
                        let new_expr: Expression;
                        (new_expr, reg_map) = var_to_reg_expr(&e, reg_map);
                        new_accesses.push(Access::Select(ArrayAccess {
                            expression: RangeOrExpression::Expression(new_expr),
                            span: a.span
                        }));
                    } else {
                        panic!("Range access not supported.")
                    }
                } else {
                    panic!("Unsupported membership access.")
                }
            }
            let new_id_expr: IdentifierExpression;
            (new_id_expr, reg_map) = var_to_reg_id_expr(&p.id, reg_map);
            return (Expression::Postfix(PostfixExpression {
                id: new_id_expr,
                accesses: new_accesses,
                span: p.span
            }), reg_map);
        }
        Expression::Identifier(i) => {
            let new_id_expr: IdentifierExpression;
            (new_id_expr, reg_map) = var_to_reg_id_expr(&i, reg_map);
            return (Expression::Identifier(new_id_expr), reg_map);
        }
        Expression::Literal(_) => {
            return (e.clone(), reg_map);
        }
        _ => {
            panic!("Unsupported Expression.");
        }
    };
}

fn var_to_reg_id_expr<'ast>(
    ie: &IdentifierExpression<'ast>, 
    mut reg_map: HashMap<String, usize>,
) -> (IdentifierExpression<'ast>, HashMap<String, usize>) {
    let var_name: String;
    (var_name, reg_map, _) = var_name_to_reg_id_expr::<0>(ie.value.to_string(), reg_map);
    (IdentifierExpression {
        value: var_name,
        span: ie.span
    }, reg_map)
}

// MODE: 0 - WITNESS, 1 - INPUT, 2 - OUTPUT
fn var_name_to_reg_id_expr<const MODE: usize>(
    var_name: String,
    mut reg_map: HashMap<String, usize>,
) -> (String, HashMap<String, usize>, usize) {
    let reg_size = reg_map.len();
    
    if !reg_map.contains_key(&var_name) {
        reg_map.insert(var_name.clone(), reg_size);
    }
    let reg_label = reg_map.get(&var_name).unwrap().clone();
    // Note: we cannot simply assign the variables %i1, this is because by string comparison, %10 < %2
    // However, WITNESSES DO NOT NEED TO FOLLOW THIS RULE
    match MODE {
        0 => (format!("%w{}", reg_label), reg_map, reg_label),
        1 => (format!("%i{:06}", reg_label), reg_map, reg_label),
        _ => (format!("%o{:06}", reg_label), reg_map, reg_label)
    }
}

// Convert a typed definition statement into assignee if LHS has been defined
fn tydef_to_assignee_stmt<'ast>(
    s: &Statement<'ast>,
    mut gen_set: HashSet<String>, 
) -> (Statement<'ast>, HashSet<String>) {
    match s {
        Statement::Return(_) => {
            panic!("Blocks should not contain return statements.");
        }
        Statement::Assertion(_) => (s.clone(), gen_set),
        Statement::Conditional(c) => {
            let cond = c.condition.clone();
            let mut new_ifbranch = Vec::new();
            for s in &c.ifbranch {
                let new_stmt: Statement;
                (new_stmt, gen_set) = tydef_to_assignee_stmt(s, gen_set);
                new_ifbranch.push(new_stmt);
            }
            let mut new_elsebranch = Vec::new();
            for s in &c.elsebranch {
                let new_stmt: Statement;
                (new_stmt, gen_set) = tydef_to_assignee_stmt(s, gen_set);
                new_elsebranch.push(new_stmt);
            }
            let new_stmt = ConditionalStatement {
                condition: cond,
                ifbranch: new_ifbranch,
                dummy: Vec::new(),
                elsebranch: new_elsebranch,
                span: Span::new("", 0, 0).unwrap()
            };
            (Statement::Conditional(new_stmt), gen_set)
        }
        Statement::Iteration(_) => { panic!("Blocks should not contain iteration statements.") }
        Statement::WhileLoop(_) => { panic!("Blocks should not contain while loop statements.") }
        Statement::Definition(d) => {
            let mut new_lhs: Vec<TypedIdentifierOrAssignee> = Vec::new();
            for l in &d.lhs {
                match l {
                    TypedIdentifierOrAssignee::TypedIdentifier(tid) => {
                        let v = tid.identifier.value.to_string();
                        if gen_set.contains(&v) {
                            new_lhs.push(TypedIdentifierOrAssignee::Assignee(Assignee {
                                id: IdentifierExpression {
                                    value: v,
                                    span: Span::new("", 0, 0).unwrap()
                                },
                                accesses: Vec::new(),
                                span: Span::new("", 0, 0).unwrap()
                            }));
                        } else {
                            new_lhs.push(l.clone());
                            gen_set.insert(v);
                        }
                    }
                    TypedIdentifierOrAssignee::Assignee(_) => { new_lhs.push(l.clone()); }
                }
            }
            // Reconstruct d as an assignee
            let s = Statement::Definition(DefinitionStatement {
                lhs: new_lhs,
                expression: d.expression.clone(),
                span: Span::new("", 0, 0).unwrap()
            });
            (s, gen_set)
        }
        Statement::CondStore(_) => { panic!("Blocks should not contain conditional store statements.") }
    }
}

// --
// END HELPER FUNCTION
// --

// Information regarding one variable for spilling
#[derive(Clone, Debug, PartialEq)]
struct VarSpillInfo {
    var_name: String,
    fn_name: String,
    scope: usize,
    version: usize
}

impl VarSpillInfo {
    fn new(var: String) -> VarSpillInfo {
        let var_segs = var.split('.').collect::<Vec<&str>>();
        let var_name = var_segs[0].to_string();
        let fn_name = var_segs[1].to_string();
        let scope: usize = var_segs[2].to_string().parse().unwrap();
        let version: usize = var_segs[3].to_string().parse().unwrap();
    
        VarSpillInfo {
            var_name,
            fn_name,
            scope,
            version
        }
    }

    // a.x is directly below a.y if y = x + 1
    fn directly_below(&self, other: &VarSpillInfo) -> bool {
        self.var_name == other.var_name && self.fn_name == other.fn_name && self.scope + 1 == other.scope
    }
}

impl<'ast> ZGen<'ast> {
    // --
    // BLOCK OPTIMIZATION
    // --

    // Returns: Blocks
    // Inputs are (variable, type) pairs
    pub fn optimize_block<const VERBOSE: bool>(
        &self,
        mut bls: Vec<Block<'ast>>,
        mut entry_bl: usize,
        inputs: Vec<(String, Ty)>
    ) -> (Vec<Block<'ast>>, usize) {
        println!("\n\n--\nOptimization:");
        // Construct CFG
        let (successor, predecessor, exit_bls, entry_bls_fn, successor_fn, predecessor_fn, exit_bls_fn) = 
            self.construct_flow_graph(&bls, entry_bl);
        if VERBOSE && CFG_VERBOSE {
            print_cfg(&successor, &predecessor, &exit_bls, &entry_bls_fn, &successor_fn, &predecessor_fn, &exit_bls_fn);
        }

        // Liveness
        bls = self.liveness_analysis(bls, &successor, &predecessor, &successor_fn, &predecessor_fn, &exit_bls, &exit_bls_fn);
        // DBE
        (bls, entry_bl, _) = self.dead_block_elimination(bls, entry_bl, predecessor);
        if VERBOSE {
            println!("\n\n--\nLiveness:");
            print_bls(&bls, &entry_bl);
        }

        // Reconstruct CFG
        let (successor, predecessor, exit_bls, entry_bls_fn, successor_fn, predecessor_fn, exit_bls_fn) = 
            self.construct_flow_graph(&bls, entry_bl);
        if VERBOSE && CFG_VERBOSE {
            print_cfg(&successor, &predecessor, &exit_bls, &entry_bls_fn, &successor_fn, &predecessor_fn, &exit_bls_fn);
        }

        // Set Input Output
        bls = self.set_input_output(bls, &successor, &predecessor, &successor_fn, &predecessor_fn, &entry_bl, &exit_bls, &exit_bls_fn, inputs.clone());
        if VERBOSE {
            println!("\n\n--\nSet Input Output before Spilling:");
            print_bls(&bls, &entry_bl);
        }

        // Resolve block merge
        bls = self.resolve_block_merge(bls, &successor, &successor_fn, &predecessor_fn, &exit_bls_fn);
        // Reconstruct CFG
        let (successor, predecessor, exit_bls, entry_bls_fn, successor_fn, predecessor_fn, exit_bls_fn) = 
        self.construct_flow_graph(&bls, entry_bl);
        if VERBOSE && CFG_VERBOSE {
            print_cfg(&successor, &predecessor, &exit_bls, &entry_bls_fn, &successor_fn, &predecessor_fn, &exit_bls_fn);
        }
        // DBE
        (bls, entry_bl, _) = self.dead_block_elimination(bls, entry_bl, predecessor);
        if VERBOSE {
            println!("\n\n--\nBlock Merge:");
            print_bls(&bls, &entry_bl);
        }

        // Reconstruct CFG
        let (successor, mut predecessor, exit_bls, entry_bls_fn, successor_fn, predecessor_fn, exit_bls_fn) = 
        self.construct_flow_graph(&bls, entry_bl);
        if VERBOSE && CFG_VERBOSE {
            print_cfg(&successor, &predecessor, &exit_bls, &entry_bls_fn, &successor_fn, &predecessor_fn, &exit_bls_fn);
        }

        // Spilling
        // Obtain io_size = maximum # of variables in a transition state that belong to the current function & have different names
        // Note that this value is not the final io_size as it does not include any reserved registers
        let tmp_io_size = self.get_max_io_size(&bls, &inputs);
        // Perform spilling
        let mut bls = self.resolve_spilling(bls, tmp_io_size, &predecessor, &successor, entry_bl, &entry_bls_fn, &predecessor_fn, &successor_fn);
        if VERBOSE {
            println!("\n\n--\nSpilling:");
            print_bls(&bls, &entry_bl);
        }

        // EBE
        (_, predecessor, bls) = self.empty_block_elimination(bls, exit_bls, successor, predecessor, &entry_bls_fn, &exit_bls_fn);
        // DBE
        (bls, entry_bl, _) = self.dead_block_elimination(bls, entry_bl, predecessor);
        if VERBOSE {
            println!("\n\n--\nEBE:");
            print_bls(&bls, &entry_bl);
        }

        // Construct CFG again after DBE
        let (successor, predecessor, exit_bls, _, successor_fn, predecessor_fn, exit_bls_fn) = 
            self.construct_flow_graph(&bls, entry_bl);
        if VERBOSE && CFG_VERBOSE {
            print_cfg(&successor, &predecessor, &exit_bls, &entry_bls_fn, &successor_fn, &predecessor_fn, &exit_bls_fn);
        }

        // Set I/O again after optimizations
        bls = self.set_input_output(bls, &successor, &predecessor, &successor_fn, &predecessor_fn, &entry_bl, &exit_bls, &exit_bls_fn, inputs.clone());
        if VERBOSE {
            println!("\n\n--\nSet Input Output after Spilling:");
            print_bls(&bls, &entry_bl);
        }
        (bls, entry_bl)
    }

    // Return value: successor, rp_successor, successor_fn, visited, next_bls
    fn flow_graph_transition<const IS_RP: bool>(
        &self,
        cur_bl: usize,
        next_bl: &NextBlock,
        rp_slot: usize,
        mut successor: Vec<HashSet<usize>>,
        mut rp_successor: Vec<HashSet<usize>>,
        mut successor_fn: Vec<HashSet<usize>>,
        mut visited: Vec<bool>,
        mut next_bls: VecDeque<usize>
    ) -> (Vec<HashSet<usize>>, Vec<HashSet<usize>>, Vec<HashSet<usize>>, Vec<bool>, VecDeque<usize>) {

        match next_bl {
            NextBlock::Label(tmp_bl) => {
                // If RP is set, only add RP to successor_fn of cur_bl
                if rp_slot == 0 || IS_RP {
                    successor_fn[cur_bl].insert(*tmp_bl);
                }
                
                // Add next_bl to successor of cur_bl if not RP
                if !IS_RP {
                    successor[cur_bl].insert(*tmp_bl);
                }
                
                let old_rp_successor = rp_successor[*tmp_bl].clone();
                // If rp_slot is not 0, append rp_slot to rp_successor of tmp_bl
                // unless we are dealing with the RP block.
                // If rp_slot is 0 or if we are dealing with the RP block,
                // let next_bl inherit rp_successor of cur_bl
                if rp_slot != 0 && !IS_RP {
                    // Function call
                    rp_successor[*tmp_bl].insert(rp_slot);
                } else {
                    // No function call
                    for i in rp_successor[cur_bl].clone().iter() {
                        rp_successor[*tmp_bl].insert(i.clone());
                    }     
                }

                // If next_bl is not visited or if rp_successor of tmp_bl changes,
                // append tmp_bl to next_bls
                if !visited[*tmp_bl] || rp_successor[*tmp_bl] != old_rp_successor {
                    let _ = std::mem::replace(&mut visited[*tmp_bl], true);
                    next_bls.push_back(*tmp_bl);
                }
            }
            NextBlock::Rp => {
                if rp_successor.len() == 0 {
                    panic!("Control flow graph construction fails: reaching end of function point but %RP not set!")
                }
                // Add everything in rp_successor of cur_bl to successor of cur_bl
                for i in rp_successor[cur_bl].iter() {
                    successor[cur_bl].insert(i.clone());
                }
                // Whatever that rp is should already be in next_bls
            }
        }
        return (successor, rp_successor, successor_fn, visited, next_bls);
    }

    // Construct a flow graph from a set of blocks
    // Return value:
    // ret[0]: map from block to all its successors (no need to use HashMap since every block should exists right now)
    // ret[1]: map from block to all its predecessors
    // ret[2]: list of all blocks that ends with ProgTerm
    // ret[3]: list of entry blocks of all reachable functions
    // ret[4]: map from block to all its successors, with function calls redirected to %RP and function return as temination
    // ret[5]: map from block to all its predecessors, with same tweak as ret[4]
    // ret[6]: list of all blocks that ends with ProgTerm or Rp
    // ret[7]: is this block part of the main function
    fn construct_flow_graph(
        &self,
        bls: &Vec<Block>,
        entry_bl: usize
    ) -> (Vec<HashSet<usize>>, Vec<HashSet<usize>>, HashSet<usize>, HashSet<usize>, Vec<HashSet<usize>>, Vec<HashSet<usize>>, HashSet<usize>) {
        let bl_size = bls.len();
        
        // list of all blocks that ends with ProgTerm
        let mut exit_bls: HashSet<usize> = HashSet::new();

        // list of all entry blocks to a function
        let mut entry_bl_fn: HashSet<usize> = HashSet::new();
        entry_bl_fn.insert(entry_bl);
        // list of all blocks that ends with ProgTerm or Rp
        let mut exit_bls_fn: HashSet<usize> = HashSet::new();
        
        // Start from entry_bl, do a BFS, add all blocks in its terminator to its successor
        // When we reach a function call (i.e., %RP is set), add %RP to the callee's rp_successor
        // Propagate rp_successor until we reach an rp() terminator, at that point, append rp_successor to successor
        // We don't care about blocks that won't be touched by BFS, they'll get eliminated anyways
        let mut successor: Vec<HashSet<usize>> = vec![HashSet::new(); bl_size];
        let mut rp_successor: Vec<HashSet<usize>> = vec![HashSet::new(); bl_size];
        let mut visited: Vec<bool> = vec![false; bl_size];
        // predecessor is just the inverse of successor
        let mut predecessor: Vec<HashSet<usize>> = vec![HashSet::new(); bl_size];

        // successor & predecessor within a function, ignoring function calls (which is redirected to %RP)
        let mut successor_fn: Vec<HashSet<usize>> = vec![HashSet::new(); bl_size];
        let mut predecessor_fn: Vec<HashSet<usize>> = vec![HashSet::new(); bl_size];

        let mut next_bls: VecDeque<usize> = VecDeque::new();
        let _ = std::mem::replace(&mut visited[entry_bl], true);
        next_bls.push_back(entry_bl);
        while !next_bls.is_empty() {
            let cur_bl = next_bls.pop_front().unwrap();

            // If we encounter any %RP = <counter>, record down <counter> to rp_slot
            // By definition, %RP cannot be 0
            // There shouldn't be multiple %RP's, but if there is, we only care about the last one
            let mut rp_slot = 0;
            
            for i in 0..bls[cur_bl].instructions.len() {
                let bc = bls[cur_bl].instructions[i].clone();
                if let Some(tmp_bl) = rp_find_val(bc) {
                    rp_slot = tmp_bl;
                }
            }

            // Process RP block
            if rp_slot != 0 {
                (successor, rp_successor, successor_fn, visited, next_bls) = 
                    self.flow_graph_transition::<true>(cur_bl, &NextBlock::Label(rp_slot), rp_slot, successor, rp_successor, successor_fn, visited, next_bls);
            }

            // Append everything in the terminator of cur_bl to next_bls
            // according to flow_graph_transition
            match bls[cur_bl].terminator.clone() {
                BlockTerminator::Transition(e) => {
                    let branches = bl_trans_find_val(&e);
                    for b in &branches {
                        (successor, rp_successor, successor_fn, visited, next_bls) = 
                            self.flow_graph_transition::<false>(cur_bl, b, rp_slot, successor, rp_successor, successor_fn, visited, next_bls);
                    }
                    // if %RP is set, the next block must be a function entrance
                    if rp_slot != 0 {
                        if branches.len() != 1 {
                            panic!("Blocks that invoke function calls cannot have branches.")
                        }
                        if let NextBlock::Label(l) = branches[0] {
                            entry_bl_fn.insert(l);
                        } else {
                            panic!("Blocks that invoke function calls cannot terminates to %RP block.")
                        }
                    }
                    // If block terminates to %RP, add it to exit_bls_fn
                    for b in branches {
                        if b == NextBlock::Rp {
                            exit_bls_fn.insert(cur_bl);
                        }
                    }
                }
                BlockTerminator::FuncCall(_) => { panic!("Blocks pending optimization should not have FuncCall as terminator.") }
                BlockTerminator::ProgTerm => { 
                    exit_bls.insert(cur_bl);
                    exit_bls_fn.insert(cur_bl);
                }
            }
        }

        for i in 0..bls.len() {
            for j in successor[i].iter() {
                predecessor[*j].insert(i);
            }
            for j in successor_fn[i].iter() {
                predecessor_fn[*j].insert(i);
            }
        }
        return (successor, predecessor, exit_bls, entry_bl_fn, successor_fn, predecessor_fn, exit_bls_fn);
    }

    // Standard Liveness Analysis
    // We do not analyze the liveness of reserved registers
    // DIRECTION: Backward
    // LATTICE:
    //   TOP: Variable does not exist in the set
    //   A variable in set indicates that it is alive
    // TRANSFER:
    //    GEN: If a variable is referenced, excluding PUSH into stack, add it into set
    //   KILL: If a variable is assigned, excluding POP from stack, remove it from the set
    //         PUSH and POPs do not affect the liveness of the variable.
    // MEET:
    //    Set Union

    // Liveness analysis should not affect CFG
    // Return new blocks and whether blocks have been altered
    fn liveness_analysis(
        &self,
        mut bls: Vec<Block<'ast>>,
        successor: &Vec<HashSet<usize>>,
        predecessor: &Vec<HashSet<usize>>,
        successor_fn: &Vec<HashSet<usize>>,
        predecessor_fn: &Vec<HashSet<usize>>,
        exit_bls: &HashSet<usize>,
        exit_bls_fn: &HashSet<usize>
    ) -> Vec<Block<'ast>> {

        let mut visited: Vec<bool> = vec![false; bls.len()];
        // MEET is union, so IN and OUT are Empty Set
        let mut bl_in: Vec<HashSet<String>> = vec![HashSet::new(); bls.len()];
        let mut bl_out: Vec<HashSet<String>> = vec![HashSet::new(); bls.len()];
        
        // Can this ever happen?
        if exit_bls.is_empty() { 
            panic!("The program has no exit block!");
        }
        
        // Start from exit block
        let mut next_bls: VecDeque<usize> = VecDeque::new();
        for eb in exit_bls {
            next_bls.push_back(*eb);
        }
        // Backward analysis!
        while !next_bls.is_empty() {
            let cur_bl = next_bls.pop_front().unwrap();

            // State is the union of all local successors AND
            // if cur_bl is a function return block, then all successors, AND
            // if cur_bl calls another function, then all parameters + reserved variables
            let mut state: HashSet<String> = HashSet::new();
            // local successors
            for s in &successor_fn[cur_bl] {
                state.extend(bl_in[*s].clone());
            }
            // function return block
            if exit_bls_fn.contains(&cur_bl) {
                for s in &successor[cur_bl] {
                    state.extend(bl_in[*s].clone());
                }
            }
            // function caller
            else {
                for s in &successor[cur_bl] {
                    let callee_name = &bls[*s].fn_name;
                    if callee_name != &bls[cur_bl].fn_name {
                        for i in &bl_in[*s].clone() {
                            if i.chars().next().unwrap() == '%' || &VarSpillInfo::new(i.to_string()).fn_name == callee_name {
                                state.insert(i.to_string());
                            }
                        }
                    }
                }
            }
            // program exit block
            if exit_bls.contains(&cur_bl) {
                state.insert("%RET".to_string());
            }

            // Only analyze if never visited before or OUT changes
            if !visited[cur_bl] || state != bl_out[cur_bl] {
                
                bl_out[cur_bl] = state.clone();
                visited[cur_bl] = true;

                // KILL and GEN within the terminator
                match &bls[cur_bl].terminator {
                    BlockTerminator::Transition(e) => { state.extend(expr_find_val(&e)); }
                    BlockTerminator::FuncCall(_) => { panic!("Blocks pending optimization should not have FuncCall as terminator.") }
                    BlockTerminator::ProgTerm => {}            
                }

                // KILL and GEN within the block
                for i in bls[cur_bl].instructions.iter().rev() {
                    match i {
                        // If there is a PUSH, then var is alive and %SP is alive
                        BlockContent::MemPush((var, _, _)) => {
                            state.insert(var.to_string());
                            state.insert("%SP".to_string());
                        }
                        // If there is a POP, then var is dead and %BP is alive
                        BlockContent::MemPop((var, _, _)) => {
                            state.remove(var);
                            state.insert("%BP".to_string());
                        }
                        // If there is an array initialization, then the array is dead but %AS is alive
                        BlockContent::ArrayInit((arr, _, _)) => {
                            if is_alive(&state, arr) {
                                state.remove(arr);
                                state.insert("%AS".to_string());
                            }
                        }
                        // If there is a store, then index, value, and %TS are alive if array is alive
                        BlockContent::Store((val_expr, _, arr, id_expr, _)) => {
                            if is_alive(&state, arr) {
                                let gen = expr_find_val(val_expr);
                                state = la_gen(state, &gen);
                                let gen = expr_find_val(id_expr);
                                state = la_gen(state, &gen);
                                state.insert("%TS".to_string());
                            }
                        }
                        // If val was alive, make array, index, and %TS alive
                        BlockContent::Load((val, _, arr, id_expr)) => {
                            if is_alive(&state, val) {
                                state.remove(val);
                                state.insert(arr.to_string());
                                let gen = expr_find_val(id_expr);
                                state = la_gen(state, &gen);
                                state.insert("%TS".to_string());
                            }
                        }
                        BlockContent::Branch(_) => { panic!("Liveness Analysis Failed: block should not contain branching statements!") }
                        BlockContent::Stmt(s) => {
                            let (kill, gen) = stmt_find_val(s);
                            // Mark gens alive only if not a definition or the defined variable is alive,
                            // Kill all defined variables
                            if kill.is_empty() || kill.iter().fold(false, |c, x| c || is_alive(&state, x)) {
                                state = la_kill(state, &kill);
                                state = la_gen(state, &gen);
                            }
                        }
                    }
                }
                bl_in[cur_bl] = state;

                // Block Transition
                for tmp_bl in &predecessor[cur_bl] {
                    next_bls.push_back(*tmp_bl);
                }
                for tmp_bl in &predecessor_fn[cur_bl]{
                    if !predecessor[cur_bl].contains(tmp_bl) {
                        next_bls.push_back(*tmp_bl);
                    }
                }
            }    
        }

        // Do this again, this time, eliminate the blocks
        for i in 0..bls.len() {
            visited[i] = false;
        }
        let mut next_bls: VecDeque<usize> = VecDeque::new();
        for eb in exit_bls {
            next_bls.push_back(*eb);
        }
        while !next_bls.is_empty() {
            let cur_bl = next_bls.pop_front().unwrap();

            // State is simply bl_out
            let mut state: HashSet<String> = bl_out[cur_bl].clone();

            // Only visit each block once
            if !visited[cur_bl] {

                visited[cur_bl] = true;
                let mut new_instructions = Vec::new();

                // KILL and GEN within the terminator
                match &bls[cur_bl].terminator {
                    BlockTerminator::Transition(e) => { state.extend(expr_find_val(&e)); }
                    BlockTerminator::FuncCall(_) => { panic!("Blocks pending optimization should not have FuncCall as terminator.") }
                    BlockTerminator::ProgTerm => {}            
                }

                // KILL and GEN within the block
                // XXX: Seems like wasting time?
                for i in bls[cur_bl].instructions.iter().rev() {
                    match i {
                        BlockContent::MemPush((var, _, _)) => {
                            // Keep all push statements, remove them in PMR
                            new_instructions.insert(0, i.clone());
                            state.insert(var.to_string());
                            state.insert("%SP".to_string());
                        }
                        BlockContent::MemPop((var, _, _)) => {
                            // Don't remove %BP, remove them in PMR
                            if is_alive(&state, var) || var == "%BP" {
                                new_instructions.insert(0, i.clone());
                            }
                            state.remove(var);
                            state.insert("%BP".to_string());
                        }
                        // If there is an array initialization, then the array is dead but %AS is alive
                        BlockContent::ArrayInit((arr, _, _)) => {
                            if is_alive(&state, arr) {
                                new_instructions.insert(0, i.clone());
                                state.remove(arr);
                                state.insert("%AS".to_string());
                            }
                        }
                        // If there is a store, then keep the statement if array is alive
                        BlockContent::Store((val_expr, _, arr, id_expr, _)) => {
                            if is_alive(&state, arr) {
                                new_instructions.insert(0, i.clone());
                                let gen = expr_find_val(val_expr);
                                state = la_gen(state, &gen);
                                let gen = expr_find_val(id_expr);
                                state = la_gen(state, &gen);
                                state.insert("%TS".to_string());
                            }
                        }
                        // If there is a store, then keep the statement if val is alive
                        BlockContent::Load((val, _, arr, id_expr)) => {
                            if is_alive(&state, val) {
                                new_instructions.insert(0, i.clone());
                                state.remove(val);
                                state.insert(arr.to_string());
                                let gen = expr_find_val(id_expr);
                                state = la_gen(state, &gen);
                                state.insert("%TS".to_string());
                            }
                        }
                        BlockContent::Branch(_) => { panic!("Liveness Analysis Failed: block should not contain branching statements!") }
                        BlockContent::Stmt(s) => {
                            let (kill, gen) = stmt_find_val(s);
                            // If it's not a definition or the defined variable is alive,
                            // mark the variable dead and append gen to state
                            // Otherwise remove the statement
                            if kill.is_empty() || kill.iter().fold(false, |c, x| c || is_alive(&state, x)) {
                                state = la_kill(state, &kill);
                                state = la_gen(state, &gen);
                                new_instructions.insert(0, i.clone());
                            }
                        }
                    }
                }

                bls[cur_bl].instructions = new_instructions;

                // Block Transition
                for tmp_bl in &predecessor[cur_bl] {
                    next_bls.push_back(*tmp_bl);
                }
                for tmp_bl in &predecessor_fn[cur_bl]{
                    if !predecessor[cur_bl].contains(tmp_bl) {
                        next_bls.push_back(*tmp_bl);
                    }
                }
            }    
        }

        return bls;
    }

    // For each block, set its input to be variables that are alive & defined at the entry point of the block and their type
    // Returns: bls
    // This pass consists of a liveness analysis and a reaching definition (for typing)
    fn set_input_output(
        &self,
        mut bls: Vec<Block<'ast>>,
        successor: &Vec<HashSet<usize>>,
        predecessor: &Vec<HashSet<usize>>,
        successor_fn: &Vec<HashSet<usize>>,
        predecessor_fn: &Vec<HashSet<usize>>,
        entry_bl: &usize,
        exit_bls: &HashSet<usize>,
        exit_bls_fn: &HashSet<usize>,
        inputs: Vec<(String, Ty)>
    ) -> Vec<Block<'ast>> {
        // Liveness
        let mut visited: Vec<bool> = vec![false; bls.len()];
        // MEET is union, so IN and OUT are Empty Set
        let mut bl_in: Vec<HashSet<String>> = vec![HashSet::new(); bls.len()];
        let mut bl_out: Vec<HashSet<String>> = vec![HashSet::new(); bls.len()];
        
        // Can this ever happen?
        if exit_bls.is_empty() { 
            panic!("The program has no exit block!");
        }
        
        // Start from exit block
        let mut next_bls: VecDeque<usize> = VecDeque::new();
        for eb in exit_bls {
            next_bls.push_back(*eb);
        }
        // Backward analysis!
        while !next_bls.is_empty() { 

            let cur_bl = next_bls.pop_front().unwrap();   

            // State is the union of all local successors AND
            // if cur_bl is a function return block, then all successors, AND
            // if cur_bl calls another function, then all parameters + reserved variables
            let mut state: HashSet<String> = HashSet::new();
            // local successors
            for s in &successor_fn[cur_bl] {
                state.extend(bl_in[*s].clone());
            }
            // function return block
            if exit_bls_fn.contains(&cur_bl) {
                for s in &successor[cur_bl] {
                    state.extend(bl_in[*s].clone());
                }
            }
            // function caller
            else {
                for s in &successor[cur_bl] {
                    let callee_name = &bls[*s].fn_name;
                    if callee_name != &bls[cur_bl].fn_name {
                        for i in &bl_in[*s].clone() {
                            if i.chars().next().unwrap() == '%' || &VarSpillInfo::new(i.to_string()).fn_name == callee_name {
                                state.insert(i.to_string());
                            }
                        }
                    }
                }
            }
            // program exit block
            if exit_bls.contains(&cur_bl) {
                state.insert("%RET".to_string());
            }

            // Only analyze if never visited before or OUT changes
            if !visited[cur_bl] || state != bl_out[cur_bl] {
                
                bl_out[cur_bl] = state.clone();
                visited[cur_bl] = true;
                
                // KILL and GEN within the terminator
                match &bls[cur_bl].terminator {
                    BlockTerminator::Transition(e) => { state.extend(expr_find_val(&e)); }
                    BlockTerminator::FuncCall(_) => { panic!("Blocks pending optimization should not have FuncCall as terminator.") }
                    BlockTerminator::ProgTerm => {}            
                }

                // KILL and GEN within the block
                // We assume that liveness analysis has been performed, don't reason about whether variables should actually be alive
                for i in bls[cur_bl].instructions.iter().rev() {
                    match i {
                        BlockContent::MemPush((var, _, _)) => {
                            state.insert(var.to_string());
                            state.insert("%SP".to_string());
                        }
                        BlockContent::MemPop((var, _, _)) => {
                            state.remove(&var.to_string());
                            state.insert("%BP".to_string());
                        }
                        // If there is an array init, then arr is dead and %AS is alive
                        BlockContent::ArrayInit((arr, _, _)) => {
                            state.remove(&arr.to_string());
                            state.insert("%AS".to_string());
                        }
                        // If there is a store, then %TS is alive
                        BlockContent::Store((val_expr, _, _, id_expr, _)) => {
                            let gen = expr_find_val(val_expr);
                            state.extend(gen);
                            let gen = expr_find_val(id_expr);
                            state.extend(gen);
                            state.insert("%TS".to_string());
                        }
                        // If there is a load, then arr and %TS is alive
                        BlockContent::Load((val, _, arr, id_expr)) => {
                            state.remove(val);
                            let gen = expr_find_val(id_expr);
                            state.extend(gen);
                            state.insert("%TS".to_string());
                            state.insert(arr.to_string());
                        }
                        BlockContent::Branch(_) => { panic!("Liveness Analysis Failed: block should not contain branching statements!") }
                        BlockContent::Stmt(s) => {
                            let (kill, gen) = stmt_find_val(&s);
                            for k in kill {
                                state.remove(&k.to_string());
                            }
                            state.extend(gen);
                        }
                    }
                }
                bl_in[cur_bl] = state;

                // Block Transition
                for tmp_bl in &predecessor[cur_bl] {
                    next_bls.push_back(*tmp_bl);
                }
                for tmp_bl in &predecessor_fn[cur_bl]{
                    if !predecessor[cur_bl].contains(tmp_bl) {
                        next_bls.push_back(*tmp_bl);
                    }
                }
            }    
        }

        let input_lst = bl_in;
        let output_lst = bl_out;

        // bl_in now consists of all the variables alive at the entry point of each block, now use a forward analysis
        // to find their types
        // Assume that there are no generic / dynamic types

        // Typing
        let mut visited: Vec<bool> = vec![false; bls.len()];
        // MEET is union, so IN and OUT are Empty Set
        let mut bl_in: Vec<HashMap<String, Ty>> = vec![HashMap::new(); bls.len()];
        let mut bl_out: Vec<HashMap<String, Ty>> = vec![HashMap::new(); bls.len()];
        
        // Start from entry block
        let mut next_bls: VecDeque<usize> = VecDeque::new();
        next_bls.push_back(*entry_bl);
        // Forward analysis!
        while !next_bls.is_empty() {
            let cur_bl = next_bls.pop_front().unwrap();

            // State is the union of all predecessors
            let mut state: HashMap<String, Ty> = HashMap::new();
            for s in &predecessor[cur_bl] {
                for (name, ty) in &bl_out[*s] {
                    if let Some(k) = state.get(name) {
                        if *ty != *k {
                            panic!("Dynamic and generic types not supported!")
                        }
                    }
                    if state.get(name) == None {
                        state.insert(name.to_string(), ty.clone());
                    }
                }
            }
            // If we are at entry block, state also includes *live* program parameters & %TS
            if cur_bl == *entry_bl {
                for (var, ty) in &inputs {
                    state.insert(var.clone(), ty.clone());
                }
            }

            // Only analyze if never visited before or OUT changes
            if !visited[cur_bl] || state != bl_in[cur_bl] {
                
                bl_in[cur_bl] = state.clone();
                visited[cur_bl] = true;

                // No KILL, GEN if we meet a typed definition
                // The only case we need to process is Typed Definition
                for i in bls[cur_bl].instructions.iter().rev() {
                    match i {
                        BlockContent::MemPush(_) => {}
                        BlockContent::MemPop((id, ty, _)) => {
                            state.insert(id.clone(), ty.clone());
                        }
                        BlockContent::ArrayInit((arr, _, _)) => {
                            state.insert(arr.clone(), Ty::Field);
                        }
                        BlockContent::Store(_) => {}
                        BlockContent::Load((val, ty, _, _)) => {
                            state.insert(val.clone(), ty.clone());
                        }
                        BlockContent::Branch(_) => { panic!("Liveness Analysis Failed: block should not contain branching statements!") }
                        BlockContent::Stmt(s) => {
                            if let Statement::Definition(ds) = s {
                                for d in &ds.lhs {
                                    if let TypedIdentifierOrAssignee::TypedIdentifier(p) = d {
                                        let name = p.identifier.value.to_string();
                                        let ty = type_to_ty(p.ty.clone());
                                        state.insert(name, ty.unwrap());
                                    }
                                }
                            }
                        }
                    }
                }
                bl_out[cur_bl] = state;

                // Terminator is just an expression so we don't need to worry about it

                // Block Transition
                for tmp_bl in &successor[cur_bl] {
                    next_bls.push_back(*tmp_bl);
                }
            }    
        }

        let ty_map_in = bl_in;
        let ty_map_out = bl_out;

        // Update input of all blocks
        // Note: block 0 takes function input and %BN as input
        for i in 0..bls.len() {
            bls[i].inputs = Vec::new();
            // Only variables that are alive & defined will become parts of inputs / outputs
            if i != 0 {
                for name in input_lst[i].iter().sorted() {
                    if let Some(ty) = ty_map_in[i].get(name) {
                        bls[i].inputs.push((name.to_string(), Some(ty.clone())));
                    }
                }
            }
            bls[i].outputs = Vec::new();
            for name in output_lst[i].iter().sorted() {
                if let Some(ty) = ty_map_out[i].get(name) {
                    bls[i].outputs.push((name.to_string(), Some(ty.clone())));
                }
            }
        }
        for (name, ty) in &inputs {
            bls[0].inputs.push((name.to_string(), Some(ty.clone())));
        }

        return bls;
    }

    // Count number of constraints for a block
    fn bl_count_num_cons(
        &self,
        bl: &Block<'ast>
    ) -> usize {
        let block_name = &format!("Pseudo_Block_{}", bl.name);
        self.circ_init_block(block_name);
        self.bl_to_circ::<true>(bl, block_name);

        let mut cs = Computations::new();
        cs.comps = self.circ.borrow().cir_ctx().cs.borrow_mut().clone();

        if let Some(c) = cs.comps.get(block_name) {
            let mut r1cs = to_r1cs(c, cfg());
    
            // Remove the last constraint because it is about the return value
            r1cs.constraints.pop();

            return r1cs.constraints.len();
        } else {
            panic!("Count num cons failed: block {} does not exist!", bl.name);
        }
    }

    // Handle block merges
    fn resolve_block_merge(
        &self,
        mut bls: Vec<Block<'ast>>,
        successor: &Vec<HashSet<usize>>,
        successor_fn: &Vec<HashSet<usize>>,
        predecessor_fn: &Vec<HashSet<usize>>,
        exit_bls_fn: &HashSet<usize>
    ) -> Vec<Block<'ast>> {
        // Obtain number of constraints for all blocks
        let mut bl_num_cons = Vec::new();
        for b in &bls {
            bl_num_cons.push(self.bl_count_num_cons(b));
        }
        // Reset self.circ
        self.circ.borrow_mut().reset(ZSharp::new());

        // Maximum # of constraints is max(MIN_BLOCK_SIZE, bl_num_cons.max().next_power_of_two())
        let max_num_cons = max(MIN_BLOCK_SIZE, bl_num_cons.iter().max().unwrap().next_power_of_two());
        
        // Backward analysis within each function: for each block, if there exists a potential merge component, record the size of constraints of that component
        let mut visited: Vec<bool> = vec![false; bls.len()];
        // count is the size of the component, set to 0 if a component does not exist
        let mut count_list = vec![0; bls.len()];
        // agg_count is the total size of the entire scope, used by the component calculation in the previous scope
        let mut agg_count_list = vec![0; bls.len()];
        // scope_state is a stack which, for every scope <= current scope, records the LABEL of the last block of that scope
        // Use 0 to indicate that such a block does not exist
        let mut scope_list = vec![Vec::new(); bls.len()];

        // Start from function exit block
        let mut next_bls: VecDeque<usize> = VecDeque::new();
        for eb in exit_bls_fn {
            next_bls.push_back(*eb);
        }
        // Backward analysis!
        while !next_bls.is_empty() {
            let cur_bl = next_bls.pop_front().unwrap();

            let cur_scope = bls[cur_bl].scope;
            // Compute scope_state using bm_join
            let mut scope_state: Vec<Option<usize>> = vec![None; cur_scope + 1];

            // if cur_bl does not call another function, then merge can be performed
            if successor_fn[cur_bl].len() == 0 || successor_fn[cur_bl] == successor[cur_bl] {
                for succ in &successor_fn[cur_bl] {
                    // if any successor is the head of a while loop, 
                    // or if any successor contains memory operations
                    // no merge can be performed
                    if bls[*succ].is_head_of_while_loop || bls[*succ].mem_op_by_ty.len() > 0 {
                        scope_state = vec![None; cur_scope + 1];
                        break;
                    }
                    // Only join if scope_list[succ] is not TOP
                    if scope_list[*succ].len() > 0 {
                        let succ_scope = bls[*succ].scope;
                        for i in 0..cur_scope + 1 {
                            // If scope < succ_scope, join scope_state of the successor with scope_state of the current block
                            if i < succ_scope {
                                let succ_state = scope_list[*succ][i];
                                scope_state[i] = bm_join(scope_state[i], succ_state);
                            }
                            // Set succ_scope of scope_state to succ
                            else if i == succ_scope {
                                scope_state[i] = bm_join(scope_state[i], *succ);
                            }
                            // If succ_scope < cur_scope, every remaining scope in scope_state is BOT
                            else {
                                scope_state[i] = Some(0);
                            }
                        }
                    }
                }
            }
            let scope_state: Vec<usize> = scope_state.iter().map(|i| if let Some(state) = i { *state } else { 0 }).collect();
            // Compute count && agg_count
            // Count is undefined if a component does not exist
            // Initialize agg_count to the number of constraints of itself
            let mut count_state = 0;
            let mut agg_count_state = bl_num_cons[cur_bl];
            if scope_state[cur_scope] != 0 {
                count_state += bl_num_cons[cur_bl];
                // Add all successors with higher scope than cur_scope
                for succ in &successor_fn[cur_bl] {
                    let succ_scope = bls[*succ].scope;
                    if succ_scope > cur_scope {
                        // Add num_iteration * count
                        count_state += bls[*succ].fn_num_exec_bound / bls[cur_bl].fn_num_exec_bound * agg_count_list[*succ];
                        agg_count_state += bls[*succ].fn_num_exec_bound / bls[cur_bl].fn_num_exec_bound * agg_count_list[*succ];
                    }
                }
                // Add count of scope_state[cur_scope]
                count_state += bl_num_cons[scope_state[cur_scope]];
                agg_count_state += agg_count_list[scope_state[cur_scope]];
            }

            if !visited[cur_bl] || scope_state != scope_list[cur_bl] || count_state != count_list[cur_bl] || agg_count_state != agg_count_list[cur_bl] {
                visited[cur_bl] = true;
                scope_list[cur_bl] = scope_state;
                count_list[cur_bl] = count_state;
                agg_count_list[cur_bl] = agg_count_state;

                for p in &predecessor_fn[cur_bl] {
                    next_bls.push_back(*p);
                }
            }
        }

        // Iterate through the blocks to perform merge
        // This is a partial backward analysis on the component we want to merge
        // We want to merge the largest component possible, which means it will start at the block with the lowest label
        // Repeat the merge process until there is nothing left to be merged
        let mut changed = true;
        while changed {
            changed = false;
            // DO NOT MERGE BLOCK 0!!!
            // This will be handled later by EBE
            for i in 1..bls.len() {
                if count_list[i] > 0 && count_list[i] < max_num_cons {
                    // Process a merge
                    let comp_head = i;
                    let comp_scope = bls[comp_head].scope;
                    let comp_tail = scope_list[comp_head][comp_scope];
                    // Backward analysis starting from comp_tail
                    // STATE is a list of instructions of all merged blocks of the current scope
                    let mut instr_list: Vec<Vec<BlockContent<'ast>>> = vec![Vec::new(); bls.len()];
                    let mut visited: Vec<bool> = vec![false; bls.len()];

                    // Start from comp_tail
                    let mut next_bls: VecDeque<usize> = VecDeque::new();
                    next_bls.push_back(comp_tail);

                    while !next_bls.is_empty() {
                        let cur_bl = next_bls.pop_front().unwrap();
                        let cur_scope = bls[cur_bl].scope;

                        // Instructions of cur_bl
                        let mut instr_state = Vec::new();
                        instr_state.extend(bls[cur_bl].instructions.clone());
                        // Instructions of successors & next block in scope, if not comp_tail
                        if cur_bl != comp_tail {                  
                            if let BlockTerminator::Transition(t) = &bls[cur_bl].terminator {
                                instr_state.extend(term_to_instr(&bls, t, &instr_list, cur_bl).0);
                            }
                            instr_state.extend(instr_list[scope_list[cur_bl][cur_scope]].clone());
                        }

                        if !visited[cur_bl] || instr_state != instr_list[cur_bl] {
                            visited[cur_bl] = true;
                            instr_list[cur_bl] = instr_state;
                            if cur_bl != comp_head {
                                for p in &predecessor_fn[cur_bl] {
                                    next_bls.push_back(*p);
                                }
                            }
                        }

                        // Clear count_list for all intermediate blocks within the component since they are now dead
                        if cur_bl != comp_head && cur_bl != comp_tail {
                            count_list[cur_bl] = 0;
                        }
                    }

                    // Recompute num_cons, scope, & count for comp_head & comp_tail
                    bl_num_cons[comp_head] = count_list[comp_head];
                    count_list[comp_head] = if count_list[comp_tail] == 0 { 0 } else { bl_num_cons[comp_head] + count_list[comp_tail] - bl_num_cons[comp_tail] };
                    scope_list[comp_head] = scope_list[comp_tail].clone();
                    count_list[comp_tail] = 0;

                    bls[comp_head].instructions = instr_list[comp_head].clone();
                    bls[comp_head].terminator = bls[comp_tail].terminator.clone();

                    changed = true;
                    break;
                }
            }
        }

        bls
    }

    // Obtain io_size = maximum # of variables in any transition state that are in scope
    fn get_max_io_size(&self, bls: &Vec<Block>, inputs: &Vec<(String, Ty)>) -> usize {
        let mut io_size = inputs.len();
        // Process block outputs
        for b in bls {
            let mut essential_vars = HashSet::new();
            for (v, _) in &b.outputs {
                // Skip all reserved registers
                if v.chars().next().unwrap() != '%' {
                    let v_spill = VarSpillInfo::new(v.clone());
                    if v_spill.fn_name == b.fn_name {
                        essential_vars.insert(v_spill.var_name);
                    }
                }
            }
            io_size = max(io_size, essential_vars.len());
        }
        io_size
    }

    // Perform spilling so all input / output state width <= io_size
    fn resolve_spilling(
        &self,
        mut bls: Vec<Block<'ast>>,
        io_size: usize,
        predecessor: &Vec<HashSet<usize>>,
        successor: &Vec<HashSet<usize>>,
        entry_bl: usize,
        entry_bls_fn: &HashSet<usize>,
        predecessor_fn: &Vec<HashSet<usize>>,
        successor_fn: &Vec<HashSet<usize>>,
    ) -> Vec<Block<'ast>> {
        // Number of spills required for every block
        let mut spill_size = vec![0];
        for i in 1..bls.len() {
            let b = &bls[i];
            // Compute the number of inputs excluding the reserved registers
            let mut input_count = 0;
            for (v, _) in &b.inputs {
                if v.chars().next().unwrap() != '%' {
                    input_count += 1;
                }
            }
            spill_size.push(if input_count > io_size { input_count - io_size } else { 0 });
        }

        // Forward Analysis to determine the effectiveness of spilling each candidate
        // Program state is consisted of two parts
        // STACK: every (shadower, candidate) pair in stack, as well as when to pop them out
        // Out-of-Scope(OOS): every *live* local variables that are out of scope to prevent duplicate pushes

        // GEN: Whenever a variable is defined or function is called
        //      If the variable or function shadows a variable in block output, and the variable is not out-of-scope, update STACK and OOS
        // KILL: Whenever a shadower is out of scope, update STACK and OOP
        
        // OOS is a set of all local variables out of scope
        let mut oos_in: Vec<HashSet<String>> = vec![HashSet::new(); bls.len()];
        let mut oos_out: Vec<HashSet<String>> = vec![HashSet::new(); bls.len()];
        // STACK is (shadower, candidate, pop_function, pop_scope).
        // When the current scope is (pop_function, pop_scope), need to pop the spill
        let mut stack_in: Vec<HashSet<(String, String, String, usize)>> = vec![HashSet::new(); bls.len()];
        let mut stack_out: Vec<HashSet<(String, String, String, usize)>> = vec![HashSet::new(); bls.len()];
        let mut visited = vec![false; bls.len()];
        let mut next_bls: VecDeque<usize> = VecDeque::new();
        next_bls.push_back(entry_bl);
        while !next_bls.is_empty() {
            let cur_bl = next_bls.pop_front().unwrap();
            
            // JOIN of OOS
            let mut oos = {
                let mut oos = HashSet::new();
                // oos only stores local variables, so only process local predecessors
                // there is no join, OOS of all predecessors should either be the same or empty
                for p in &predecessor_fn[cur_bl] {
                    if oos.len() == 0 {
                        oos = oos_out[*p].clone();
                    }
                    assert!(oos_out[*p].len() == 0 || oos == oos_out[*p]);
                }
                oos
            };

            // JOIN of STACK:
            let mut stack = {
                let mut stack = HashSet::new();
                // if a function entry block, union over all predecessors
                if predecessor_fn[cur_bl].len() == 0 {
                    for p in &predecessor[cur_bl] {
                        stack.extend(stack_out[*p].clone());
                    }
                }
                // otherwise, union over local predecessors
                // function calls should not affect the scope stack of the caller function
                else {
                    for p in &predecessor_fn[cur_bl] {
                        stack.extend(stack_out[*p].clone());
                    }
                }
                stack
            };

            // Iterate through the statements and process definition statements
            if !visited[cur_bl] || oos_in[cur_bl] != oos || stack_in[cur_bl] != stack {
                visited[cur_bl] = true;
                oos_in[cur_bl] = oos.clone();
                stack_in[cur_bl] = stack.clone();

                // Pop out scope changes due to function call
                for s in stack.clone() {
                    if bls[cur_bl].fn_name == s.2 && bls[cur_bl].scope <= s.3 {
                        stack.remove(&s);
                        oos.remove(&s.1);
                    }
                }

                // Check shadower declaration
                for i in &bls[cur_bl].instructions {
                    match i {
                        BlockContent::Stmt(stmt) => {
                            // GEN describes all newly defined variables
                            let (gen, _) = stmt_find_val(stmt);
                            for shadower in &gen {
                                let shadower_alive = bls[cur_bl].outputs.iter().fold(false, |a, b| a || &b.0 == shadower);
                                // Proceed if the shadower live till the end of the block
                                if shadower_alive && shadower.chars().next().unwrap() != '%' {
                                    let shadower_vsi = VarSpillInfo::new(shadower.to_string());
                                    // Iterate through outputs of cur_bl (live variables)
                                    for (candidate, _) in &bls[cur_bl].outputs {
                                        // Proceed if in scope
                                        if candidate.chars().next().unwrap() != '%' && !oos.contains(candidate) {
                                            // Proceed if there is shadowing
                                            if VarSpillInfo::new(candidate.to_string()).directly_below(&shadower_vsi) {
                                                // GEN
                                                oos.insert(candidate.to_string());
                                                // pop_scope is current scope - 1
                                                stack.insert((shadower.to_string(), candidate.to_string(), bls[cur_bl].fn_name.to_string(), bls[cur_bl].scope - 1));
                                            }
                                        }
                                    }
                                }
                            }
                        },
                        _ => {}
                    }
                }

                // First assert on CFG shape: all fn_successors can only have one scope other than the scope of cur_bl
                let mut succ_scope = bls[cur_bl].scope;
                for succ in &successor_fn[cur_bl] {
                    assert!(bls[*succ].scope == bls[cur_bl].scope || bls[*succ].scope == succ_scope || succ_scope == bls[cur_bl].scope);
                    if succ_scope != bls[*succ].scope { succ_scope = bls[*succ].scope };
                }
                // If there is a scope change in fn_successor, pop out all candidates that are no longer spilled
                if succ_scope < bls[cur_bl].scope {
                    for s in stack.clone() {
                        if bls[cur_bl].fn_name == s.2 && succ_scope <= s.3 {
                            stack.remove(&s);
                            oos.remove(&s.1);
                        }
                    }
                }

                // If there is a function call, push all live & in-scope candidates onto stack
                if successor_fn[cur_bl].len() != 0 && successor_fn[cur_bl] != successor[cur_bl] {
                    assert_eq!(successor[cur_bl].len(), 1);
                    assert_eq!(successor_fn[cur_bl].len(), 1);
                    let callee = Vec::from_iter(successor[cur_bl].clone())[0];
                    let callee_name = &bls[callee].fn_name;
                    let caller_name = &bls[cur_bl].fn_name;
                    // Iterate through outputs (live variables)
                    for (candidate, _) in &bls[cur_bl].outputs {
                        if candidate.chars().next().unwrap() != '%' {
                            // Only if in scope
                            if !oos.contains(candidate) {
                                if &VarSpillInfo::new(candidate.to_string()).fn_name == caller_name {
                                    // GEN
                                    oos.insert(candidate.to_string());
                                    // pop_scope is current scope
                                    stack.insert((callee_name.to_string(), candidate.to_string(), caller_name.to_string(), bls[cur_bl].scope));
                                }
                            }
                        }
                    }
                }
                
                oos_out[cur_bl] = oos.clone();
                stack_out[cur_bl] = stack.clone();
                for succ in &successor[cur_bl] {
                    next_bls.push_back(*succ);
                }
            }
        }
        // As long as any block has spill_size > 0, keep vote out the candidate that can reduce the most total_spill_size
        let mut total_spill_size = spill_size.iter().fold(0, |a, b| a + b);
        let mut spills: HashMap<String, BTreeSet<String>> = HashMap::new();
        while total_spill_size > 0 {
            // Compute vote score for each candidate, use BTreeMap to make ranking deterministic
            // Scores records all blocks where the spilling of the candidate can affect spill_size
            let mut scores: BTreeMap<(String, String, String, usize), Vec<usize>> = BTreeMap::new();
            for i in 1..bls.len() {
                // Only gain score if the block requires spilling
                if spill_size[i] > 0 {
                    for stack in &stack_in[i] {
                        let candidate = stack.clone();
                        if let Some(b) = scores.get(&candidate) {
                            scores.insert(candidate, [b.to_vec(), vec![i]].concat());
                        } else {
                            scores.insert(candidate, vec![i]);
                        }
                    }
                }
            }
            let mut scores = Vec::from_iter(scores);
            scores.sort_by(|(_, a), (_, b)| b.len().cmp(&a.len()));
            // Pick the #0 candidate
            let ((shadower, var, _, _), _) = &scores[0];
            // Add the candidate to spills
            let mut vars = if let Some(vars) = spills.get(shadower) { vars.clone() } else { BTreeSet::new() };
            vars.insert(var.to_string());
            spills.insert(shadower.to_string(), vars);
            // Remove the candidate from stack_in
            for b in &scores[0].1 {
                stack_in[*b].remove(&scores[0].0);
                // spill_size only decreases if var is alive & not shadowed by something else in the state
                let var_alive = bls[*b].inputs.iter().fold(false, |a, b| a || &b.0 == var);
                let spill_size_decrease = stack_in[*b].iter().fold(true, |a, b| a && &b.1 != var);
                if var_alive && spill_size_decrease {
                    spill_size[*b] -= 1;
                    total_spill_size -= 1;
                }
            }
        }
        let mut entry_bl_instructions = Vec::new();
        // If size of spills is not zero, need to add %BP and %SP to block 0
        if spills.len() > 0 {
            // Initialize %SP
            entry_bl_instructions.push(BlockContent::Stmt(bl_gen_init_stmt("%SP")));
            // Initialize %BP
            entry_bl_instructions.push(BlockContent::Stmt(bl_gen_init_stmt("%BP")));
        }
        // If %TS is alive, initialize %TS
        if bls[entry_bl].outputs.contains(&("%TS".to_string(), Some(Ty::Field))) {
            entry_bl_instructions.push(BlockContent::Stmt(bl_gen_init_stmt("%TS")));
        }
        // If %AS is alive, initialize %AS
        if bls[entry_bl].outputs.contains(&("%AS".to_string(), Some(Ty::Field))) {
            entry_bl_instructions.push(BlockContent::Stmt(bl_gen_init_stmt("%AS")));
        }
        bls[entry_bl].instructions = entry_bl_instructions;

        // Iterate through the blocks FUNCTION BY FUNCTION, add push and pop statements if variable is in SPILLS
        // STATE, GEN, KILL follows above
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
        // OOS: Out-of-Scope
        let mut oos_in: Vec<HashSet<String>> = vec![HashSet::new(); bls.len()];
        let mut oos_out: Vec<HashSet<String>> = vec![HashSet::new(); bls.len()];
        // STACK is a (ordered) list of variables in stack per stack frame
        let mut stack_in: Vec<Vec<Vec<(String, Ty)>>> = vec![Vec::new(); bls.len()];
        let mut stack_out: Vec<Vec<Vec<(String, Ty)>>> = vec![Vec::new(); bls.len()];
        let mut visited = vec![false; bls.len()];
        let mut next_bls: VecDeque<usize> = VecDeque::new();
        for e in entry_bls_fn {
            next_bls.push_back(*e);
        }
        while !next_bls.is_empty() {
            let cur_bl = next_bls.pop_front().unwrap();
            let cur_scope = bls[cur_bl].scope;

            // JOIN of OOS & STACK
            let (mut oos, mut stack) = {
                let mut oos = HashSet::new();
                let mut stack = Vec::new();
                // OOS of all predecessors should either be the same or empty
                // the first cur_scope + 1 entries of all predecessors should either be the same of empty
                // any other entries should always be empty
                for p in &predecessor_fn[cur_bl] {
                    if oos.len() == 0 {
                        oos = oos_out[*p].clone();
                    }
                    if stack.len() == 0 && stack_out[*p].len() != 0 {
                        // fill stack up to cur_scope
                        stack = (0..cur_scope + 1).map(|i| if stack_out[*p].len() > i { stack_out[*p][i].clone() } else { Vec::new() }).collect();
                    }

                    assert!(oos_out[*p].len() == 0 || oos == oos_out[*p]);
                    if stack_out[*p].len() != 0 {
                        for i in 0..stack_out[*p].len() {
                            if i <= cur_scope {
                                assert_eq!(stack[i], stack_out[*p][i]);
                            } else {
                                assert!(stack_out[*p][i].len() == 0);
                            }
                        }
                    }
                }
                // fill stack up to cur_scope
                stack.extend(vec![Vec::new(); cur_scope + 1 - stack.len()]);
                (oos, stack)
            };

            // No need to visit a block twice
            if !visited[cur_bl] {
                visited[cur_bl] = true;
                oos_in[cur_bl] = oos.clone();
                stack_in[cur_bl] = stack.clone();

                let mut new_instructions = Vec::new();
                let mut sp_offset = 0;

                // Handle function return scope change
                while stack.len() > bls[cur_bl].scope {
                    let mut sp_offset = stack[stack.len() - 1].len() - 1;
                    for (var, ty) in stack[stack.len() - 1].iter().rev() {
                        new_instructions.push(BlockContent::MemPop((var.to_string(), ty.clone(), sp_offset)));
                        sp_offset -= 1;
                        oos.remove(var);
                    }
                    stack.pop();
                }

                let cur_frame = bls[cur_bl].scope - 1;

                // Check shadower declaration
                // Ignore all memory instructions
                for i in &bls[cur_bl].instructions {
                    match i {
                        BlockContent::Stmt(stmt) => {
                            // GEN describes all newly defined variables
                            let (gen, _) = stmt_find_val(stmt);
                            for shadower in &gen {
                                let shadower_alive = bls[cur_bl].outputs.iter().fold(false, |a, b| a || &b.0 == shadower);
                                // Proceed if the shadower live till the end of the block
                                if shadower_alive && shadower.chars().next().unwrap() != '%' {
                                    // Check if any variables need to be spilled
                                    if let Some(vars) = spills.get(shadower) {
                                        for var in vars {
                                            if !oos.contains(var) {
                                                let var_type: Option<Ty> = bls[cur_bl].outputs.iter().fold(None, |a, b| if &b.0 == var { b.1.clone() } else { a });
                                                if let Some(var_ty) = var_type {
                                                    // GEN
                                                    oos.insert(var.to_string());

                                                    if sp_offset == 0 {
                                                        // %PHY[%SP + 0] = %BP
                                                        new_instructions.push(BlockContent::MemPush(("%BP".to_string(), Ty::Field, sp_offset)));
                                                        // %BP = %SP
                                                        new_instructions.push(BlockContent::Stmt(bp_update_stmt.clone()));
                                                        stack[cur_frame].push(("%BP".to_string(), Ty::Field));
                                                        sp_offset += 1;
                                                    }
                                                    // %PHY[%SP + ?] = Var
                                                    new_instructions.push(BlockContent::MemPush((var.to_string(), var_ty.clone(), sp_offset)));
                                                    stack[cur_frame].push((var.to_string(), var_ty.clone()));
                                                    sp_offset += 1;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            if !is_sp_push(&stmt) && !is_bp_update(&stmt) {
                                new_instructions.push(i.clone());
                            }
                        },
                        // Do not reason about memory operations
                        BlockContent::ArrayInit(_) => {
                            new_instructions.push(i.clone());
                        }
                        BlockContent::Store(_) => {
                            new_instructions.push(i.clone());
                        }
                        BlockContent::Load(_) => {
                            new_instructions.push(i.clone());
                        }
                        _ => {}
                    }
                }

                // If there is a scope change in fn_successor, pop out all candidates that are no longer spilled
                let mut succ_scope = 0;
                for succ in &successor_fn[cur_bl] {
                    if succ_scope < bls[*succ].scope { succ_scope = bls[*succ].scope };
                }
                if succ_scope < bls[cur_bl].scope {
                    while stack.len() > succ_scope {
                        let mut sp_offset = stack[stack.len() - 1].len() - 1;
                        for (var, ty) in stack[stack.len() - 1].iter().rev() {
                            new_instructions.push(BlockContent::MemPop((var.to_string(), ty.clone(), sp_offset)));
                            sp_offset -= 1;
                        }
                        stack.pop();
                    }
                }

                // If there is a function call, push all live & in-scope candidates onto stack
                if successor_fn[cur_bl].len() != 0 && successor_fn[cur_bl] != successor[cur_bl] {
                    let cur_frame = cur_frame + 1;
                    assert_eq!(successor[cur_bl].len(), 1);
                    assert_eq!(successor_fn[cur_bl].len(), 1);
                    stack.push(Vec::new());

                    // the last instruction is %RP = ?, which should appear after scope change
                    let rp_update_inst = new_instructions.pop().unwrap();

                    // %SP = %SP + ?
                    if sp_offset > 0 {
                        new_instructions.push(BlockContent::Stmt(bl_gen_increment_stmt("%SP", sp_offset)));   
                        sp_offset = 0;                         
                    }

                    let callee = Vec::from_iter(successor[cur_bl].clone())[0];
                    let callee_name = &bls[callee].fn_name;
                    let caller_name = &bls[cur_bl].fn_name;
                    // Check if any variables need to be spilled
                    if let Some(vars) = spills.get(callee_name) {
                        for var in vars {
                            if !oos.contains(var) {
                                let var_type: Option<Ty> = bls[cur_bl].outputs.iter().fold(None, |a, b| if &b.0 == var { b.1.clone() } else { a });
                                if let Some(var_ty) = var_type {
                                    // GEN
                                    oos.insert(var.to_string());

                                    if sp_offset == 0 {
                                        // %PHY[%SP + 0] = %BP
                                        new_instructions.push(BlockContent::MemPush(("%BP".to_string(), Ty::Field, sp_offset)));
                                        // %BP = %SP
                                        new_instructions.push(BlockContent::Stmt(bp_update_stmt.clone()));
                                        stack[cur_frame].push(("%BP".to_string(), Ty::Field));
                                        sp_offset += 1;
                                    }
                                    // %PHY[%SP + ?] = Var
                                    new_instructions.push(BlockContent::MemPush((var.to_string(), var_ty.clone(), sp_offset)));
                                    stack[cur_frame].push((var.to_string(), var_ty.clone()));
                                    sp_offset += 1;
                                }
                            }
                        }
                    }
                    // Also push in %RP if caller is not main
                    if caller_name != "main" {
                        if sp_offset == 0 {
                            // %PHY[%SP + 0] = %BP
                            new_instructions.push(BlockContent::MemPush(("%BP".to_string(), Ty::Field, sp_offset)));
                            // %BP = %SP
                            new_instructions.push(BlockContent::Stmt(bp_update_stmt.clone()));
                            stack[cur_frame].push(("%BP".to_string(), Ty::Field));
                            sp_offset += 1;
                        }
                        // %PHY[%SP + ?] = %RP
                        new_instructions.push(BlockContent::MemPush(("%RP".to_string(), Ty::Field, sp_offset)));
                        stack[cur_frame].push(("%RP".to_string(), Ty::Field));
                        sp_offset += 1;
                    }
                    // %RP = ?
                    new_instructions.push(rp_update_inst);
                }
                // %SP = %SP + ?
                if sp_offset > 0 {
                    new_instructions.push(BlockContent::Stmt(bl_gen_increment_stmt("%SP", sp_offset)));                        
                }

                bls[cur_bl].instructions = new_instructions;
                oos_out[cur_bl] = oos.clone();
                stack_out[cur_bl] = stack.clone();
                for succ in &successor_fn[cur_bl] {
                    next_bls.push_back(*succ);
                }
            }
        }
        bls
    }

    // EBE: Backward analysis
    // If a block is empty and its terminator is a coda (to another block or %RP)
    // replace all the reference to it in its predecessors with that terminator
    // If a block terminates with a branching and both branches to the same block, eliminate the branching
    // If a block only has one successor and that successor only has one predecessor, merge the two blocks
    //
    // We assume that something would happen after the function call, so we do not change the value of any %RP
    // This would not affect correctness. Worst case it might make DBE later inefficient.
    //
    // CFG will be DESTROYED after this! Only do it after all statement analyses.
    fn empty_block_elimination(
        &self,
        mut bls: Vec<Block<'ast>>,
        exit_bls: HashSet<usize>,
        mut successor: Vec<HashSet<usize>>,
        mut predecessor: Vec<HashSet<usize>>,
        entry_bls_fn: &HashSet<usize>,
        exit_bls_fn: &HashSet<usize>
    ) -> (Vec<HashSet<usize>>, Vec<HashSet<usize>>, Vec<Block<'ast>>) {

        let mut visited: Vec<bool> = Vec::new();
        for _ in 0..bls.len() {
            visited.push(false);
        }
        
        // Can this ever happen?
        if exit_bls.is_empty() {
            panic!("The program has no exit block!");
        }
        
        // Start from exit block
        let mut next_bls: VecDeque<usize> = VecDeque::new();
        for eb in exit_bls {
            next_bls.push_back(eb);
            visited[eb] = true;
        }
        // Backward analysis to isolate empty blocks
        while !next_bls.is_empty() {
            let cur_bl = next_bls.pop_front().unwrap();

            // If the block only has one predecessor and the predecessor only has one successor
            // And the transition does not involve function calls / returns, merge the two blocks
            if !entry_bls_fn.contains(&cur_bl) && predecessor[cur_bl].len() == 1 {
                let p = Vec::from_iter(predecessor[cur_bl].clone())[0];
                if !exit_bls_fn.contains(&p) && successor[p].len() == 1 {
                    // Append cur_bl to p
                    let succ = bls[cur_bl].clone();
                    bls[p].concat(succ);
                    // Update CFG
                    successor[p].remove(&cur_bl);
                    predecessor[cur_bl].remove(&p);
                    for i in successor[cur_bl].clone() {
                        successor[p].insert(i);
                        predecessor[i].insert(p);
                    }
                }
            }

            // Update the terminator of all predecessor
            for tmp_bl in predecessor[cur_bl].clone() {
                // The only cases we need to continue is
                // either we haven't processed the predecessor
                // or cur_bl is empty so predecessors will be changed
                if !visited[tmp_bl] || bls[cur_bl].instructions.len() == 0 {
                    visited[tmp_bl] = true;

                    if bls[cur_bl].instructions.len() == 0 {
                        if let BlockTerminator::Transition(cur_e) = &bls[cur_bl].terminator {
                            if let BlockTerminator::Transition(e) = &bls[tmp_bl].terminator {
                                // Replace terminator of the predecessors
                                let new_e = bl_trans_replace(e, cur_bl, cur_e);
                                bls[tmp_bl].terminator = BlockTerminator::Transition(new_e);

                                // Update CFG
                                successor[tmp_bl].remove(&cur_bl);
                                predecessor[cur_bl].remove(&tmp_bl);
                                for i in successor[cur_bl].clone() {
                                    successor[tmp_bl].insert(i);
                                    predecessor[i].insert(tmp_bl);
                                }
                            }
                        }
                    }
                    next_bls.push_back(tmp_bl);
                }
            }
        }
        return (successor, predecessor, bls);
    }

    // DBE: Remove all the dead blocks in the list
    // Rename all block labels so that they are still consecutive
    // Return value: bls, entry_bl, exit_bl, label_map
    fn dead_block_elimination(
        &self,
        bls: Vec<Block<'ast>>,
        entry_bl: usize,
        predecessor: Vec<HashSet<usize>>
    ) -> (Vec<Block<'ast>>, usize, HashMap<usize, usize>) {      
        let old_size = bls.len();
        
        // Initialize map from old label of blocks to new labels
        let mut label_map = HashMap::new();
        // Initialize a new list of blocks
        let mut new_bls = Vec::new();

        // Iterate through all blocks. If it does not have a predecessor, delete it and update next_bls
        let mut new_label = 0;
        for old_label in 0..old_size {
            label_map.insert(old_label, new_label);
            if old_label == 0 || !predecessor[old_label].is_empty() {
                // Change block name to match new_label
                let tmp_bl = Block::clone(new_label, &bls[old_label]);
                new_bls.push(tmp_bl);
                new_label += 1;
            }
        }
        let new_entry_bl = *label_map.get(&entry_bl).unwrap();
        let new_size = new_label;

        // Iterate through all new blocks again, update %RP and Block Terminator
        for cur_bl in 0..new_size {

            // If we encounter any %RP = <counter>, update <counter> to label_map[<counter>]
            for i in 0..new_bls[cur_bl].instructions.len() {
                let bc = new_bls[cur_bl].instructions[i].clone();
                if let Some(new_bc) = rp_replacement_stmt(bc, label_map.clone()) {
                    let _ = std::mem::replace(&mut new_bls[cur_bl].instructions[i], new_bc);
                }
            }
            
            // Update the terminator of each blocks using label_map
            if let BlockTerminator::Transition(e) = &new_bls[cur_bl].terminator {
                new_bls[cur_bl].terminator = BlockTerminator::Transition(bl_trans_map(e, &label_map))
            }
        }
        return (new_bls, new_entry_bl, label_map);
    }

    // --
    // BLOCK PREPROCESSING
    // --

    // Returns: Blocks, entry block, # of registers
    // Inputs are (variable, type) pairs
    //  MODE = 0 - Verification Mode, output registers are witnesses and checked using assertion
    //  MODE = 1 - Compute Mode, output registers are assigned and not checked
    pub fn process_block<const VERBOSE: bool, const MODE: usize>(
        &self,
        bls: Vec<Block<'ast>>,
        entry_bl: usize,
        inputs: Vec<(String, Ty)>
    ) -> (Vec<Block<'ast>>, usize, usize, usize, Vec<(Vec<usize>, Vec<usize>)>, Vec<(usize, usize)>, Vec<Vec<usize>>) {
        println!("\n\n--\nPost-Processing:");
        // Construct a new CFG for the program
        // Note that this is the CFG after DBE, and might be different from the previous CFG
        let (successor, predecessor, exit_bls, entry_bls_fn, successor_fn, predecessor_fn, exit_bls_fn) = self.construct_flow_graph(&bls, entry_bl);
        if VERBOSE && CFG_VERBOSE {
            print_cfg(&successor, &predecessor, &exit_bls, &entry_bls_fn, &successor_fn, &predecessor_fn, &exit_bls_fn);
        }

        /*
        // Perform topological sort on functions
        let sorted_fns = fn_top_sort(&bls, &successor, &successor_fn);
        if VERBOSE {
            print!("FN TOP SORT: {}", sorted_fns[0]);
            for i in 1..sorted_fns.len() {
                print!(" -> {}", sorted_fns[i]);
            }
            println!();
        }
        */

        // VtR
        let (bls, transition_map_list, io_size, witness_map, witness_size, live_io) = self.var_to_reg::<MODE>(bls, &predecessor, &successor, entry_bl, inputs);
        if VERBOSE {
            println!("\n\n--\nVar -> Reg:");
            println!("Var -> IO map:");
            for i in 0..transition_map_list.len() {
                println!("i = {}: {:?}", i, transition_map_list[i]);
            }
            println!("Var -> Witness map: {:?}", witness_map);
            println!("Live variables: ");
            for i in 0..live_io.len() {
                println!("  BLOCK {}: {:?}", i, live_io[i])
            }
        }

        // Convert Typed Defs back to Assignees
        let bls = self.tydef_to_assignee::<MODE>(bls);
        if VERBOSE {
            println!("\n\n--\nTydef -> Assignee:");
            print_bls(&bls, &entry_bl);
        }

        // Obtain # of scoping memory accesses per block
        let (num_mem_accesses, live_vm) = self.get_blocks_memory_info(&bls);

        print_bls(&bls, &entry_bl);
        (bls, entry_bl, io_size, witness_size, live_io, num_mem_accesses, live_vm)
    }

    // Convert all mentionings of variables to registers
    // Also convert array initializers to pointer definition
    // Registers are divided into three categories: inputs, outputs, and witnesses
    // size of inputs = size of outputs && 2 * (size of inputs + 1) = size of witnesses
    // However, we won't know the size of witnesses until circuit generation,
    // hence need to record inputs, outputs, and witnesses separately
    // Structure for input / output
    // reg  0   1   2   3   4   5   6   7   8   9
    //      V  BN  RET TS  AS  RP  SP  BP  i8  i8
    // Structure for witness
    // reg  0   1   2   3   4   5   6   7  ...
    //     RET TS  AS  RP  SP  BP  w6  w7
    //
    // When the io map and witness map is determined, update the block such that
    // 1. The first and last values of each variable in io should be assigned an io register
    // 2. All other variables and other values of io variables should be assigned a witness register
    // 3. If an io variable is marked "alive" at the block entrance, and is never referenced or changed,
    //    insert an "output == input" assertion
    //
    // Finally, write down labels of all live inputs and outputs, 
    // No control flow, iterate over blocks directly
    // Returns the new blocks, register map, and # of registers used
    //
    // var_to_reg takes in two modes:
    //  MODE = 0 - Verification Mode, output registers are witnesses and checked using assertion
    //  MODE = 1 - Compute Mode, output registers are assigned and not checked
    fn var_to_reg<const MODE: usize>(
        &self,
        mut bls: Vec<Block<'ast>>,
        predecessor: &Vec<HashSet<usize>>,
        successor: &Vec<HashSet<usize>>,
        entry_bl: usize,
        inputs: Vec<(String, Ty)>
    ) -> (Vec<Block<'ast>>, Vec<HashMap<String, usize>>, usize, HashMap<String, usize>, usize, Vec<(Vec<usize>, Vec<usize>)>) {    
        // reg_map is consisted of two Var -> Reg Maps: TRANSITION_MAP_LIST & WITNESS_MAP
        // TRANSITION_MAP_LIST is a list of maps corresponding to each transition state
        // Reserve registers 0 - 7 for %V, %BN, %RET, %TS, %AS, %RP, %SP, and %BP
        let mut transition_map_list = Vec::new();
        // MAX_IO_SIZE is the size of the largest maps among TRANSITION_MAP_LIST
        let mut max_io_size = 0;
        // BL_IN and BL_OUT records which transition state the inputs & outputs of each block is in
        // TRANSITION_MAP_LIST[BL_IN[X]] is the register map used by the inputs of block X
        let mut bl_in: Vec<Option<usize>> = vec![None; bls.len()];
        let mut bl_out: Vec<Option<usize>> = vec![None; bls.len()];

        // Process program inputs
        let input_map = {
            let mut io_map: HashMap<String, usize> = new_io_map();
            // inputs
            for (v, _) in &inputs {
                (_, io_map, _) = var_name_to_reg_id_expr::<1>(v.to_string(), io_map);
            }
            io_map
        };
        bl_in[entry_bl] = Some(0);
        max_io_size = max(max_io_size, input_map.len());
        transition_map_list.push(input_map);

        // Process all transition states
        for i in 0..bls.len() {
            // Only process block output states
            if bl_out[i] == None {
                let trans_size = transition_map_list.len();

                // Initialize register map
                let mut io_map = new_io_map();

                // Add all live variables to register map
                // As well as set bl_in and bl_out
                // Entry in next_bls is (block_id, should we update bl_out?)
                let mut next_bls: VecDeque<(usize, bool)> = VecDeque::new();
                next_bls.push_back((i, true));
                while next_bls.len() != 0 {
                    let (cur_bl, update_out) = next_bls.pop_front().unwrap();
                    if update_out {
                        if bl_out[cur_bl] == None {
                            // Add outputs to io_map
                            for (v, _) in &bls[cur_bl].outputs {
                                (_, io_map, _) = var_name_to_reg_id_expr::<2>(v.to_string(), io_map);
                            }
                            // Update bl_out
                            bl_out[cur_bl] = Some(trans_size);
                            // Add successors to next_bls
                            for succ_bl in &successor[cur_bl] {
                                if bl_in[*succ_bl] == None {
                                    next_bls.push_back((*succ_bl, false));
                                }
                            }
                        }
                    } else {
                        if bl_in[cur_bl] == None {
                            // Add inputs to io_map
                            for (v, _) in &bls[cur_bl].inputs {
                                (_, io_map, _) = var_name_to_reg_id_expr::<1>(v.to_string(), io_map);
                            }
                            // Update bl_in
                            bl_in[cur_bl] = Some(trans_size);
                            // Add predecessors to next_bls
                            for pred_bl in &predecessor[cur_bl] {
                                if bl_out[*pred_bl] == None {
                                    next_bls.push_back((*pred_bl, true));
                                }
                            }
                        }
                    }
                }

                // Insert io_map to transition_map_list
                max_io_size = max(max_io_size, io_map.len());
                transition_map_list.push(io_map);
            }
        }

        // Make sure all bl_in and bl_outs are defined
        for i in 0..bls.len() {
            assert!(bl_in[i] != None);
            assert!(bl_out[i] != None);
        }
        
        // --
        // WITNESS_MAP is one single map to describe all block witnesses
        // Reserve registers 0 - 5 for %RET, %TS, %AS, %RP, %SP, and %BP
        let mut witness_map: HashMap<String, usize> = new_witness_map();

        // Record down labels of all live inputs / outputs of each block
        let mut live_io: Vec<(Vec<usize>, Vec<usize>)> = Vec::new();

        // Expression for block number check
        let bn_id = Expression::Identifier(IdentifierExpression {
            value: format!("%i{:06}", 1),
            span: Span::new("", 0, 0).unwrap()
        });
        for i in 0..bls.len() {
            assert_eq!(i, bls[i].name);

            live_io.push((Vec::new(), Vec::new()));

            // Add block number check
            // We defer validity check until after R1CS is constructed for prover's convenience
            let mut new_inputs = Vec::new();
            new_inputs.push((format!("%i{:06}", 1), Some(Ty::Field)));
            live_io[i].0.push(1);

            let mut new_instr: Vec<BlockContent> = Vec::new();
            let block_num_check_expr = Expression::Binary(BinaryExpression {
                op: BinaryOperator::Eq,
                left: Box::new(bn_id.clone()),
                right: Box::new(Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                    value: DecimalNumber {
                        value: i.to_string(),
                        span: Span::new("", 0, 0).unwrap()
                    },
                    suffix: Some(DecimalSuffix::Field(FieldSuffix {
                        span: Span::new("", 0, 0).unwrap()
                    })),
                    span: Span::new("", 0, 0).unwrap()
                }))),
                span: Span::new("", 0, 0).unwrap()
            });
            let block_num_check_stmt = Statement::Assertion(AssertionStatement {
                expression: block_num_check_expr,
                message: None,
                span: Span::new("", 0, 0).unwrap()
            });
            new_instr.push(BlockContent::Stmt(block_num_check_stmt));

            // Map the inputs
            // Nothing in transition_map_list should change now
            let io_map = &transition_map_list[bl_in[i].unwrap()];
            for (name, ty) in &bls[i].inputs {
                let new_input_name: String;
                let live_input_label: usize;
                (new_input_name, _, live_input_label) = var_name_to_reg_id_expr::<1>(name.to_string(), io_map.clone());
                new_inputs.push((new_input_name.to_string(), ty.clone()));
                live_io[i].0.push(live_input_label);
                let new_witness_name: String;
                (new_witness_name, witness_map, _) = var_name_to_reg_id_expr::<0>(name.to_string(), witness_map);
                // For each input, assign a witness to its value
                let witness_assign_stmt = DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                        ty: ty_to_type(&ty.clone().unwrap()).unwrap(),
                        identifier: IdentifierExpression {
                            value: new_witness_name,
                            span: Span::new("", 0, 0).unwrap()
                        },
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    expression: Expression::Identifier(IdentifierExpression {
                        value: new_input_name,
                        span: Span::new("", 0, 0).unwrap()
                    }),
                    span: Span::new("", 0, 0).unwrap()
                };
                new_instr.push(BlockContent::Stmt(Statement::Definition(witness_assign_stmt)));
            }
            bls[i].inputs = new_inputs;

            // Map the instructions
            for s in &bls[i].instructions {
                match s {
                    BlockContent::MemPush((var, ty, offset)) => {
                        let new_var: String;
                        (new_var, witness_map, _) = var_name_to_reg_id_expr::<0>(var.to_string(), witness_map);
                        new_instr.push(BlockContent::MemPush((new_var, ty.clone(), *offset)));
                    }
                    BlockContent::MemPop((var, ty, offset)) => {
                        let new_var: String;
                        (new_var, witness_map, _) = var_name_to_reg_id_expr::<0>(var.to_string(), witness_map);
                        new_instr.push(BlockContent::MemPop((new_var, ty.clone(), *offset)));
                    }
                    BlockContent::ArrayInit((arr, _, size)) => {
                        let new_arr_name: String;
                        let new_alloc_size_name: String;
                        (new_arr_name, witness_map, _) = var_name_to_reg_id_expr::<0>(arr.to_string(), witness_map);
                        (new_alloc_size_name, witness_map, _) = var_name_to_reg_id_expr::<0>("%AS".to_string(), witness_map);

                        // Declare the array as a pointer (field), set to %AS
                        let pointer_init_stmt = Statement::Definition(DefinitionStatement {
                            lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                                ty: Type::Basic(BasicType::Field(FieldType {
                                    span: Span::new("", 0, 0).unwrap()
                                })),
                                identifier: IdentifierExpression {
                                    value: new_arr_name.to_string(),
                                    span: Span::new("", 0, 0).unwrap()
                                },
                                span: Span::new("", 0, 0).unwrap()
                            })],
                            expression: Expression::Identifier(IdentifierExpression {
                                value: new_alloc_size_name.to_string(),
                                span: Span::new("", 0, 0).unwrap()
                            }),
                            span: Span::new("", 0, 0).unwrap()
                        });
                        new_instr.push(BlockContent::Stmt(pointer_init_stmt));
                        // Increment %AS by size of array
                        new_instr.push(BlockContent::Stmt(bl_gen_increment_stmt(&new_alloc_size_name, *size)));
                    }
                    BlockContent::Store((val_expr, ty, arr, id_expr, init)) => {
                        let new_val_expr: Expression;
                        let new_id_expr: Expression;
                        let new_arr_name: String;
                        (new_val_expr, witness_map) = var_to_reg_expr(&val_expr, witness_map);
                        (new_id_expr, witness_map) = var_to_reg_expr(&id_expr, witness_map);
                        (new_arr_name, witness_map, _) = var_name_to_reg_id_expr::<0>(arr.to_string(), witness_map);
                        new_instr.push(BlockContent::Store((new_val_expr, ty.clone(), new_arr_name, new_id_expr, *init)))
                    }
                    BlockContent::Load((val, ty, arr, id_expr)) => {
                        let new_val: String;
                        let new_id_expr: Expression;
                        let new_arr_name: String;
                        (new_val, witness_map, _) = var_name_to_reg_id_expr::<0>(val.to_string(), witness_map);
                        (new_id_expr, witness_map) = var_to_reg_expr(&id_expr, witness_map);
                        (new_arr_name, witness_map, _) = var_name_to_reg_id_expr::<0>(arr.to_string(), witness_map);
                        new_instr.push(BlockContent::Load((new_val, ty.clone(), new_arr_name, new_id_expr)))
                    }
                    BlockContent::Branch(_) => { panic!("Liveness Analysis Failed: block should not contain branching statements!") }
                    BlockContent::Stmt(s) => {
                        let new_stmt: Statement;
                        (new_stmt, witness_map) = var_to_reg_stmt(&s, witness_map);
                        new_instr.push(BlockContent::Stmt(new_stmt));
                    }
                }
            }

            // Map the outputs
            // If in MODE 0, assert the %o variables
            // Otherwise, assign the %o variables
            let io_map = &transition_map_list[bl_out[i].unwrap()];
            let mut new_outputs = Vec::new();
            new_outputs.push((format!("%o{:06}", 1), Some(Ty::Field)));
            for (name, ty) in &bls[i].outputs {
                let new_output_name: String;
                let live_output_label: usize;
                (new_output_name, _, live_output_label) = var_name_to_reg_id_expr::<2>(name.to_string(), io_map.clone());
                new_outputs.push((new_output_name.to_string(), ty.clone()));
                live_io[i].1.push(live_output_label);
                let new_witness_name: String;
                (new_witness_name, witness_map, _) = var_name_to_reg_id_expr::<0>(name.to_string(), witness_map);

                if MODE == 0 {
                    // For each output, assert that it is equal to the corresponding witness
                    let output_check_stmt = AssertionStatement {
                        expression: Expression::Binary(BinaryExpression {
                            op: BinaryOperator::Eq,
                            left: Box::new(Expression::Identifier(IdentifierExpression {
                                value: new_output_name,
                                span: Span::new("", 0, 0).unwrap()
                            })),
                            right: Box::new(Expression::Identifier(IdentifierExpression {
                                value: new_witness_name,
                                span: Span::new("", 0, 0).unwrap()
                            })),
                            span: Span::new("", 0, 0).unwrap()
                        }),
                        message: None,
                        span: Span::new("", 0, 0).unwrap()
                    };
                    new_instr.push(BlockContent::Stmt(Statement::Assertion(output_check_stmt)));
                } else {
                    // For each output, assign it to the value of the corresponding witness
                    let output_assign_stmt = DefinitionStatement {
                        lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                            ty: ty_to_type(&ty.clone().unwrap()).unwrap(),
                            identifier: IdentifierExpression {
                                value: new_output_name,
                                span: Span::new("", 0, 0).unwrap()
                            },
                            span: Span::new("", 0, 0).unwrap()
                        })],
                        expression: Expression::Identifier(IdentifierExpression {
                            value: new_witness_name,
                            span: Span::new("", 0, 0).unwrap()
                        }),
                        span: Span::new("", 0, 0).unwrap()
                    };
                    new_instr.push(BlockContent::Stmt(Statement::Definition(output_assign_stmt)));
                }
            }
            bls[i].outputs = new_outputs;

            // Update terminator and convert it into an assertion statement
            let new_expr = {
                let new_expr: Expression;
                if let BlockTerminator::Transition(e) = &bls[i].terminator {
                    (new_expr, witness_map) = var_to_reg_expr(&e, witness_map);
                    bls[i].terminator = BlockTerminator::Transition(new_expr.clone());
                } else {
                    // If it is the end of the program, assign %BN to be bls.len()
                    new_expr = Expression::Literal(LiteralExpression::DecimalLiteral(DecimalLiteralExpression {
                        value: DecimalNumber {
                            value: bls.len().to_string(),
                            span: Span::new("", 0, 0).unwrap()
                        },
                        suffix: Some(DecimalSuffix::Field(FieldSuffix {
                            span: Span::new("", 0, 0).unwrap()
                        })),
                        span: Span::new("", 0, 0).unwrap()
                    }));
                };
                new_expr
            };
            if MODE == 0 {
                let output_block_check_stmt = AssertionStatement {
                    expression: Expression::Binary(BinaryExpression {
                        op: BinaryOperator::Eq,
                        left: Box::new(Expression::Identifier(IdentifierExpression {
                            value: format!("%o{:06}", 1),
                            span: Span::new("", 0, 0).unwrap()
                        })),
                        right: Box::new(new_expr.clone()),
                        span: Span::new("", 0, 0).unwrap()
                    }),
                    message: None,
                    span: Span::new("", 0, 0).unwrap()
                };
                new_instr.push(BlockContent::Stmt(Statement::Assertion(output_block_check_stmt)));
            } else {
                let output_block_assign_stmt = DefinitionStatement {
                    lhs: vec![TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier {
                        ty: Type::Basic(BasicType::Field(FieldType {
                            span: Span::new("", 0, 0).unwrap()
                        })),
                        identifier: IdentifierExpression {
                            value: format!("%o{:06}", 1),
                            span: Span::new("", 0, 0).unwrap()
                        },
                        span: Span::new("", 0, 0).unwrap()
                    })],
                    expression: new_expr.clone(),
                    span: Span::new("", 0, 0).unwrap()
                };
                new_instr.push(BlockContent::Stmt(Statement::Definition(output_block_assign_stmt)));
            }
            bls[i].instructions = new_instr;

            // Return is %oBN
            live_io[i].1.push(1);
            // Sort live_io
            live_io[i].0.sort();
            live_io[i].1.sort();
        }
        if max_io_size > 999999 {
            panic!("Register assignment failed: number of i/o variables cannot exceed 999999!")
        }
        let witness_size = witness_map.len();
        (bls, transition_map_list, max_io_size, witness_map, witness_size, live_io)
    }

    // Revert typed identifiers back to assignees to avoid scoping confusion when translating to IR
    // Forward (reaching definition) analysis within each block
    // Assumption: 1. every assignment is illegal; 2. every variable only exists in one scope
    //
    // tydef_to_assignee takes in two modes:
    //  MODE = 0 - Verification Mode, output registers are witnesses and checked using assertion
    //  MODE = 1 - Compute Mode, output registers are assigned and not checked
    fn tydef_to_assignee<const MODE: usize>(
        &self,
        mut bls: Vec<Block<'ast>>,
    ) -> Vec<Block<'ast>> {
        for i in 0..bls.len() {
            // gen_set - all defined variables
            let mut gen_set = HashSet::new();
            let mut new_instr = Vec::new();
            // Process inputs
            for (name, _) in &bls[i].inputs {
                gen_set.insert(name.to_string());
            }
            // Process outputs if we are in verification mode
            if MODE == 0 {
                for (name, _) in &bls[i].inputs {
                    gen_set.insert(name.to_string());
                }
            }
            // Process instructions
            for i in &bls[i].instructions {
                match i {
                    BlockContent::Stmt(s) => {
                        let new_s: Statement;
                        (new_s, gen_set) = tydef_to_assignee_stmt(s, gen_set);
                        new_instr.push(BlockContent::Stmt(new_s));
                    }
                    _ => { new_instr.push(i.clone()); }
                }
            }
            bls[i].instructions = new_instr;
        }
        bls
    }

    // Construct a view of memory from the blocks.
    // Converts array initializers to pointer definition
    // Returns:
    // 0. # of (physical (scoping) memory, virtual memory accesses) accesses for each block
    // 1. Liveness of each virtual memory variable
    //    * We need all variables present for permutation check, but some are not referenced in the constraints and will be killed in R1CS
    //    * For every _live_ virtual memory variable, record its overall ordering in all virtual memory variables 
    fn get_blocks_memory_info(
        &self,
        bls: &Vec<Block>,
    ) -> (Vec<(usize, usize)>, Vec<Vec<usize>>) {
        // Number of memory accesses per block
        let mut num_mem_accesses = Vec::new();
        // Map of each _live_ vm variables to its overall ordering
        let mut live_vm_list = Vec::new();
        for b in bls {
            let mut phy_mem_accesses_count = 0;
            let mut vir_mem_accesses_count = 0;
            // List of bools of whether each vm variable is alive, useful for branch merge
            let mut vm_liveness: Vec<bool> = Vec::new();
            for i in &b.instructions {
                match i {
                    BlockContent::MemPop(_) => {
                        phy_mem_accesses_count += 1;
                    }
                    BlockContent::MemPush(_) => {
                        phy_mem_accesses_count += 1;
                    }
                    BlockContent::ArrayInit(_) => {}
                    BlockContent::Load(_) => {
                        vir_mem_accesses_count += 1;
                        //                      addr  data  ls    ts
                        vm_liveness.extend(vec![true, true, true, true]);
                    }
                    // Store includes init, invalidate, & store
                    BlockContent::Store(_) => {
                        vir_mem_accesses_count += 1;
                        //                      addr  data  ls    ts
                        vm_liveness.extend(vec![true, true, true, true]);
                    }
                    /*
                    BlockContent::Load(_) => {
                        vir_mem_accesses_count += 1;
                        //                      phy_addr  vir_addr  data      ls        ts
                        vm_liveness.extend(vec![false,    true,     true,     true,     true]);
                    }
                    // Store includes init, invalidate, & store
                    BlockContent::Store((_, _, _, _, init)) => {
                        if *init {
                            vir_mem_accesses_count += 1;
                            //                      phy_addr  vir_addr  data      ls        ts
                            vm_liveness.extend(vec![true,     true,     true,     true,     true]);
                        } else {
                            vir_mem_accesses_count += 3;
                            //                      phy_addr  vir_addr  data      ls        ts
                            vm_liveness.extend(vec![true,     true,     false,    true,     true,    // retrieval
                                                    true,     true,     false,    true,     true,    // invalidation
                                                    true,     true,     true,     true,     true,]); // allocation
                        }
                    }
                    */
                    BlockContent::Branch(_) => { panic!("Liveness Analysis Failed: block should not contain branching statements!") }
                    BlockContent::Stmt(_) => {}
                }
            }
            num_mem_accesses.push((phy_mem_accesses_count, vir_mem_accesses_count));
            let mut live_vm = Vec::new();
            for i in 0..vm_liveness.len() {
                if vm_liveness[i] {
                    live_vm.push(i);
                }
            }
            live_vm_list.push(live_vm);
        }
        (num_mem_accesses, live_vm_list)
    }

    // Bound the total # of block executions & the total # of memory accesses
    // We do so through a DP algorithm starting from the exit block
    fn _get_blocks_static_bound(
        &self,
        bls: &Vec<Block>,
        num_mem_accesses: &Vec<usize>,
        successor: &Vec<HashSet<usize>>,
        entry_bl: usize,
        exit_bls_fn: &HashSet<usize>,
        successor_fn: &Vec<HashSet<usize>>,
        predecessor_fn: &Vec<HashSet<usize>>,
        sorted_fns: &Vec<String>
    ) -> (usize, usize) {
        // Static bound on number of block executions & memory accesses
        let (total_num_proofs_bound, total_num_mem_accesses_bound) = {
            // Eliminate all loops
            let mut predecessor_fn_no_loop = predecessor_fn.clone();
            let mut successor_fn_no_loop = successor_fn.clone();
            // Note: cannot use a recursive DFS to eliminate backedges, because depending on traverse route, backedges might not be the same as loops
            // Instead, for every block, remove any successor with smaller block label
            for i in 0..bls.len() {
                for j in predecessor_fn_no_loop[i].clone() {
                    if j >= i {
                        predecessor_fn_no_loop[i].remove(&j);
                    }
                }
                for j in successor_fn_no_loop[i].clone() {
                    if j <= i {
                        successor_fn_no_loop[i].remove(&j);
                    }
                }
            }

            // Starting from the front-most function in top sort, analyze all blocks within the function
            let mut total_num_proofs = vec![0; bls.len()];
            let mut total_num_mem_accesses = vec![0; bls.len()];
            for f_name in sorted_fns.iter().rev() {
                // A DP algorithm to find total_num_proofs_bound & total_num_mem_accesses_bound
                // Note that we have eliminated all loops
                // For each block, record the maximum number of block executions from the block to the end of the function
                // And the maximum number of memory accesses
                // Start from exit block
                let mut next_bls: VecDeque<usize> = VecDeque::new();
                for eb in exit_bls_fn {
                    if &bls[*eb].fn_name == f_name {
                        next_bls.push_back(*eb);
                    }
                }
                while !next_bls.is_empty() {
                    let cur_bl = next_bls.pop_front().unwrap();

                    let mut max_successor_num_proofs = bls[cur_bl].fn_num_exec_bound;
                    let mut max_successor_num_mem_accesses = bls[cur_bl].fn_num_exec_bound * num_mem_accesses[cur_bl];

                    // if cur_bl is the exit block of a function, do not reason about successors
                    if successor_fn[cur_bl].len() == 0 {} 
                    // if cur_bl is a caller of a function, need to process both the function head block and the return block
                    else if successor_fn[cur_bl] != successor[cur_bl] {
                        assert_eq!(successor[cur_bl].len(), 1);
                        assert_eq!(successor_fn[cur_bl].len(), 1);
                        let func_header = Vec::from_iter(successor[cur_bl].clone())[0];
                        let return_bl = Vec::from_iter(successor_fn[cur_bl].clone())[0];
                        assert!(total_num_proofs[func_header] != 0);
                        max_successor_num_proofs += bls[cur_bl].fn_num_exec_bound * total_num_proofs[func_header] + total_num_proofs[return_bl];
                        max_successor_num_mem_accesses += bls[cur_bl].fn_num_exec_bound * total_num_mem_accesses[func_header] + total_num_mem_accesses[return_bl];
                    }
                    // otherwise, process all the successors
                    else {
                        for succ in &successor_fn_no_loop[cur_bl] {
                            // num_proofs
                            let succ_num_proofs = total_num_proofs[*succ] + bls[cur_bl].fn_num_exec_bound;
                            if max_successor_num_proofs < succ_num_proofs {
                                max_successor_num_proofs = succ_num_proofs;
                            }
                            // num_mem_accesses
                            let succ_num_mem_accesses = total_num_mem_accesses[*succ] + bls[cur_bl].fn_num_exec_bound * num_mem_accesses[cur_bl];
                            if max_successor_num_mem_accesses < succ_num_mem_accesses {
                                max_successor_num_mem_accesses = succ_num_mem_accesses;
                            }
                        }
                    }

                    // If any value changes, process all non-loop predecessors
                    if max_successor_num_proofs != total_num_proofs[cur_bl] || max_successor_num_mem_accesses != total_num_mem_accesses[cur_bl] {
                        for pred in &predecessor_fn_no_loop[cur_bl] {
                            if !next_bls.contains(pred) {
                                next_bls.push_back(*pred);
                            }
                        }
                    }
                    // Update values
                    if max_successor_num_proofs != total_num_proofs[cur_bl] {
                        total_num_proofs[cur_bl] = max_successor_num_proofs;
                    }
                    if max_successor_num_mem_accesses != total_num_mem_accesses[cur_bl] {
                        total_num_mem_accesses[cur_bl] = max_successor_num_mem_accesses;
                    }
                }
            }
            (total_num_proofs[entry_bl], total_num_mem_accesses[entry_bl])
        };

        (total_num_proofs_bound, total_num_mem_accesses_bound)
    }
}