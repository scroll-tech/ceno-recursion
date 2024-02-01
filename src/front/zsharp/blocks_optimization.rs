// Multiple problems with liveness analysis:
// A declaration is dead, but assignments are alive
// PUSH is not equivalent to a change in scope. Instead of popping out the last state,
// PUSH should result in the union of the last two states.

use std::collections::VecDeque;
use zokrates_pest_ast::*;
use crate::front::zsharp::blocks::*;
use std::collections::HashMap;
use std::collections::HashSet;
use crate::front::zsharp::Ty;
use itertools::Itertools;
use std::cmp::max;

fn type_to_ty(t: Type) -> Result<Ty, String> {
    /*
    fn lift(t: BasicOrStructType) -> Type {
        match t {
            BasicOrStructType::Basic(b) => Type::Basic(b.clone()),
            BasicOrStructType::Struct(b) => Type::Struct(b.clone()),
        }
    }
    */
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

// Returns: Blocks
// Inputs are (variable, type) pairs
pub fn optimize_block<const VERBOSE: bool>(
    mut bls: Vec<Block>,
    mut entry_bl: usize,
    inputs: Vec<(String, Ty)>
) -> (Vec<Block>, usize) {
    // Construct CFG
    let (successor, mut predecessor, exit_bls, entry_bls_fn, successor_fn, predecessor_fn, exit_bls_fn) = 
        construct_flow_graph(&bls, entry_bl);
    if VERBOSE {
        print_cfg(&successor, &predecessor, &exit_bls, &entry_bls_fn, &successor_fn, &predecessor_fn, &exit_bls_fn);
    }
    println!("\n\n--\nOptimization:");
    
    // Compute number of execution bound for each block
    bls = compute_num_exec_bound(bls, &predecessor, &successor_fn, &entry_bls_fn);

    // Liveness & PMR
    // As long as altered is true, we need to keep doing liveness and PMR
    let mut altered = true;
    while altered {
        (bls, altered) = liveness_analysis(bls, &successor, &predecessor, &exit_bls);
        if altered {
            (bls, altered) = phy_mem_rearrange(bls, &predecessor_fn, &successor_fn, &exit_bls_fn);
        }
    }
    if VERBOSE {
        println!("\n\n--\nLiveness & PMR:");
        print_bls(&bls, &entry_bl);
    }

    // Set Input
    // Putting this here because EBE and DBE destroys CFG
    bls = set_input_output(bls, &successor, &predecessor, &entry_bl, &exit_bls, inputs.clone());
    if VERBOSE {
        println!("\n\n--\nSet Input Output:");
        print_bls(&bls, &entry_bl);
    }

    // EBE
    (_, predecessor, bls) = empty_block_elimination(bls, exit_bls, successor, predecessor);
    if VERBOSE {
        println!("\n\n--\nEBE:");
        print_bls(&bls, &entry_bl);
    }

    // DBE
    (bls, entry_bl, _) = dead_block_elimination(bls, entry_bl, predecessor);
    if VERBOSE {
        println!("\n\n--\nDBE:");
        print_bls(&bls, &entry_bl);
    }
    (bls, entry_bl)
}

// Returns: Blocks, entry block, # of registers
// Inputs are (variable, type) pairs
pub fn process_block<const VERBOSE: bool, const MODE: usize>(
    bls: Vec<Block>,
    entry_bl: usize,
    inputs: Vec<(String, Ty)>
) -> (Vec<Block>, usize, usize, usize, Vec<(Vec<usize>, Vec<usize>)>) {
    // VtR
    let (bls, transition_map_list, io_size, witness_map, witness_size, live_io) = var_to_reg::<MODE>(bls, entry_bl, inputs);
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
    print_bls(&bls, &entry_bl);
    (bls, entry_bl, io_size, witness_size, live_io)
}

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

// Return value: successor, rp_successor, successor_fn, visited, next_bls
fn flow_graph_transition<const IS_RP: bool>(
    cur_bl: &usize,
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
                successor_fn[*cur_bl].insert(*tmp_bl);
            }
            
            // Add next_bl to successor of cur_bl if not RP
            if !IS_RP {
                successor[*cur_bl].insert(*tmp_bl);
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
                for i in rp_successor[*cur_bl].clone().iter() {
                    rp_successor[*tmp_bl].insert(*i);
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
            for i in rp_successor[*cur_bl].iter() {
                successor[*cur_bl].insert(*i);
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

// NOTE: This is placed before EBE, so no block ends with branching will have Rp in one or more blocks
//       Similarly, function entry blocks should only be reachable from function calls
fn construct_flow_graph(
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
    // When we reach a function call (i.e., %RP is set), add value of %RP to the callee's rp_successor
    // Propagate rp_successor until we reach an rp() terminator, at that point, append rp_successor to successor
    // We don't care about blocks that won't be touched by BFS, they'll get eliminated anyways
    let mut successor: Vec<HashSet<usize>> = Vec::new();
    let mut rp_successor: Vec<HashSet<usize>> = Vec::new();
    let mut visited: Vec<bool> = Vec::new();
    // predecessor is just the inverse of successor
    let mut predecessor: Vec<HashSet<usize>> = Vec::new();

    // successor & predecessor within a function, ignoring function calls (which is redirected to %RP)
    let mut successor_fn: Vec<HashSet<usize>> = Vec::new();
    let mut predecessor_fn: Vec<HashSet<usize>> = Vec::new();

    for _ in 0..bl_size {
        successor.push(HashSet::new());
        rp_successor.push(HashSet::new());
        visited.push(false);
        predecessor.push(HashSet::new());
        successor_fn.push(HashSet::new());
        predecessor_fn.push(HashSet::new());
    }

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
                flow_graph_transition::<true>(&cur_bl, &NextBlock::Label(rp_slot), rp_slot, successor, rp_successor, successor_fn, visited, next_bls);
        }

        // Append everything in the terminator of cur_bl to next_bls
        // according to flow_graph_transition
        match bls[cur_bl].terminator.clone() {
            BlockTerminator::Transition(e) => {
                let branches = bl_trans_find_val(&e);
                for b in &branches {
                    (successor, rp_successor, successor_fn, visited, next_bls) = 
                        flow_graph_transition::<false>(&cur_bl, b, rp_slot, successor, rp_successor, successor_fn, visited, next_bls);
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

// Given CFG, compute the upper bound on number of executions of each block within the program
fn compute_num_exec_bound<'ast>(
    mut bls: Vec<Block<'ast>>,
    predecessor: &Vec<HashSet<usize>>,
    successor_fn: &Vec<HashSet<usize>>,
    entry_bls_fn: &HashSet<usize>
) -> Vec<Block<'ast>> {
    let mut changed = true;
    while changed {
        changed = false;

        // For every function entrance, use its callers to determine the # of executions of the function
        for i in entry_bls_fn {
            let b = &bls[*i];
            let mut num_func_exec = 0;
            for p in &predecessor[*i] {
                num_func_exec += bls[*p].prog_num_exec_bound;
            }
            if num_func_exec == 0 { num_func_exec = 1 };
            // If there are more execs to the function than expected, update prog_num_exec_bound for all blocks of the function
            if b.prog_num_exec_bound != num_func_exec * b.func_num_exec_bound {
                changed = true;

                let mut next_bls: VecDeque<usize> = VecDeque::new();
                next_bls.push_back(*i);
                while !next_bls.is_empty() {
                    let cur_bl = next_bls.pop_front().unwrap();
                    bls[cur_bl].prog_num_exec_bound = num_func_exec * bls[cur_bl].func_num_exec_bound;
                    for j in &successor_fn[cur_bl] {
                        if bls[*j].prog_num_exec_bound != num_func_exec * bls[*j].func_num_exec_bound {
                            next_bls.push_back(*j);
                        }
                    }
                }
            }
        }
    }
    bls
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
        Statement::Iteration(_) => {
            panic!("Blocks should not contain iteration statements.")
        }
        Statement::Conditional(_) => {
            panic!("Blocks should not contain conditional statements.")
        }
        Statement::CondStore(_) => { panic!("Blocks should not contain conditional store statements.") }
    }
}

// Standard Liveness Analysis
// We do not analyze the liveness of %BP, %SP, %RP, %RET, or %ARG
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

// MEET of liveness_analysis
fn la_meet(
    first: &HashSet<String>,
    second: &HashSet<String>
) -> HashSet<String> {
    let mut third = first.clone();
    third.extend(second.clone());
    third
}

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

// Liveness analysis should not affect CFG
// Return new blocks and whether blocks have been altered
fn liveness_analysis<'ast>(
    mut bls: Vec<Block<'ast>>,
    successor: &Vec<HashSet<usize>>,
    predecessor: &Vec<HashSet<usize>>,
    exit_bls: &HashSet<usize>
) -> (Vec<Block<'ast>>, bool) {

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

        // State is the Union of all successors
        let mut state: HashSet<String> = HashSet::new();
        for s in &successor[cur_bl] {
            state = la_meet(&state, &bl_in[*s]);
        }
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
                    BlockContent::Stmt(s) => {
                        let (kill, gen) = stmt_find_val(s);
                        state = la_kill(state, &kill);
                        state = la_gen(state, &gen);
                    }
                }
            }
            bl_in[cur_bl] = state;

            // Block Transition
            for tmp_bl in predecessor[cur_bl].clone() {
                next_bls.push_back(tmp_bl);
            }
        }    
    }

    // Do this again, this time, eliminate the blocks
    let mut altered = false;
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
                        } else {
                            altered = true;
                        }
                        state.remove(var);
                        state.insert("%BP".to_string());
                    }
                    BlockContent::Stmt(s) => {
                        let (kill, gen) = stmt_find_val(s);
                        // If it's not a definition or the defined variable is alive,
                        // mark the variable dead and append gen to state
                        // Otherwise remove the statement
                        if kill.is_empty() || kill.iter().fold(false, |c, x| c || is_alive(&state, x)) {
                            state = la_kill(state, &kill);
                            state = la_gen(state, &gen);
                            new_instructions.insert(0, i.clone());
                        } else {
                            altered = true;
                        }
                    }
                }
            }

            bls[cur_bl].instructions = new_instructions;

            // Block Transition
            for tmp_bl in predecessor[cur_bl].clone() {
                next_bls.push_back(tmp_bl);
            }
        }    
    }

    return (bls, altered);
}

// PMR is consisted of a liveness analysis on memory stack entries
// Liveness analysis on the stack (LAS)
// DIRECTION: Backward
// LATTICE:
//   TOP: An empty list
//   Otherwise, a list of list that records whether each stack frame of every scope is alive.
//     The last list indicates the current stack frame. Note that a stack frame might have size 0.
//   BOTTOM: None
// TRANSFER:
//    GEN: If a variable is popped from the stack:
//         - If it is %BP, initialize a new scope
//         - Mark the stack frame at the offset to be alive
//   KILL: If a variable is pushed onto the stack:
//         - If it is %BP, pop out the current scope

// Given a statement, decide if it is of form %SP = %SP + x
fn pmr_is_push(s: &Statement) -> bool {
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
fn pmr_is_bp_update(s: &Statement) -> bool {
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

fn pmr_join(
    first: Vec<Vec<bool>>,
    second: &Vec<Vec<bool>>
) -> Vec<Vec<bool>> {
    // If any of them is TOP, return the other one
    if first.len() == 0 {
        return second.clone();
    }
    if second.len() == 0 {
        return first;
    }
    // Reject the join if they do not have the same scope
    if first.len() != second.len() {
        panic!("PMR join fail: cannot join two states with different scopes!")
    }
    let mut third = first.clone();
    for i in 0..third.len() {
        for j in 0..second[i].len() {
            if j >= third[i].len() {
                third[i].push(second[i][j]);
            } else {
                third[i][j] = third[i][j] || second[i][j];
            }
        }
    }
    third
}

// Given all stack frames of a scope, how many live entries are in the stack?
fn pmr_stack_frame_count(frame_list: &Vec<bool>) -> usize {
    let count = frame_list.iter().fold(0, |a, b| if *b {a + 1} else {a});
    if count == 1 {0} else {count}
}

// Return new blocks and whether blocks have been altered
fn phy_mem_rearrange<'ast>(
    mut bls: Vec<Block<'ast>>,
    predecessor_fn: &Vec<HashSet<usize>>,
    successor_fn: &Vec<HashSet<usize>>,
    exit_bls_fn: &HashSet<usize>
) -> (Vec<Block<'ast>>, bool) {
    let mut visited: Vec<bool> = Vec::new();
    let mut bl_in: Vec<Vec<Vec<bool>>> = Vec::new();
    let mut bl_out: Vec<Vec<Vec<bool>>> = Vec::new();
    for _ in 0..bls.len() {
        visited.push(false);
        bl_in.push(Vec::new());
        bl_out.push(Vec::new());
    }

    // LIVENESS ANALYSIS
    // This shouldn't happen
    if exit_bls_fn.is_empty() { 
        panic!("The program has no exit block!");
    }
    // Start from exit block
    let mut next_bls: VecDeque<usize> = VecDeque::new();
    for eb in exit_bls_fn {
        next_bls.push_back(*eb);
    }
    // Backward analysis!
    while !next_bls.is_empty() {
        let cur_bl = next_bls.pop_front().unwrap();

        // State is the Union of all successors
        let mut state = Vec::new();
        for s in &successor_fn[cur_bl] {
            state = pmr_join(state, &bl_in[*s]);
        }

        // Only analyze if never visited before or OUT changes
        if !visited[cur_bl] || state != bl_out[cur_bl] {
            bl_out[cur_bl] = state.clone();
            visited[cur_bl] = true;

            // GEN within the block
            for i in bls[cur_bl].instructions.iter().rev() {
                match i {
                    BlockContent::MemPop((var, _, offset)) => {
                        // If we encounter a %BP, push in a new scope
                        if var == "%BP" {
                            state.push(vec![true]);
                        }
                        // Otherwise, set entry OFFSET of the last scope to be TRUE, pad state with FALSE if necessary
                        else {
                            let sp = state.len() - 1;
                            for _ in state[sp].len()..*offset {
                                state[sp].push(false);
                            }
                            state[sp].push(true);
                        }
                    }
                    BlockContent::MemPush((var, _, _)) => {
                        // If we encounter a %BP, pop out the last scope
                        if var == "%BP" {
                            state.pop();
                        }
                    }
                    _ => {}
                }
            }

            bl_in[cur_bl] = state;

            // Block Transition
            for tmp_bl in predecessor_fn[cur_bl].clone() {
                next_bls.push_back(tmp_bl);
            }
        }
    }

    // Use bl_out to derive bl_out_size, which records the number of live stack frames within each scope
    let bl_out_size: Vec<Vec<usize>> = bl_out.iter().map(
        |i| i.iter().map(
            |j| pmr_stack_frame_count(j)
        ).collect()
    ).collect();
    for i in 0..bls.len() {
        visited[i] = false;
    }

    // Start from exit block
    let mut next_bls: VecDeque<usize> = VecDeque::new();
    for eb in exit_bls_fn {
        next_bls.push_back(*eb);
    }
    let mut altered = false;
    // One final backward analysis, visit every block once
    while !next_bls.is_empty() {
        let cur_bl = next_bls.pop_front().unwrap();

        // Only analyze if never visited before
        if !visited[cur_bl] {
            visited[cur_bl] = true;
            // State is bl_out
            // State_size is bl_out_size
            let mut state = bl_out[cur_bl].clone();
            let mut state_size = bl_out_size[cur_bl].clone();
            // Push in new instructions
            let mut new_instructions = Vec::new();

            // GEN within the block
            for i in bls[cur_bl].instructions.iter().rev() {
                let sp = state.len() - 1;
                match i {
                    BlockContent::MemPop((var, ty, offset)) => {
                        if var == "%BP" {
                            state.push(vec![true]);
                            state_size.push(0);
                            // Delay popping %BP until we see the first non-BP pop
                        }
                        else {
                            for _ in state[sp].len()..*offset {
                                state[sp].push(false);
                            }
                            state[sp].push(true);
                            // If this is the first pop of the scope pop out %BP first
                            if state_size[sp] == 0 {
                                new_instructions.insert(0, BlockContent::MemPop(("%BP".to_string(), Ty::Field, 0)));
                                state_size[sp] += 1;
                            }
                            new_instructions.insert(0, BlockContent::MemPop((var.to_string(), ty.clone(), state_size[sp])));
                            state_size[sp] += 1;
                        }
                    }
                    BlockContent::MemPush((var, ty, offset)) => {
                        if var == "%BP" {
                            // Only include the push %BP statement if anything else is pushed onto the stack
                            // In that case, state_size[sp] should be 1
                            assert!(state_size[sp] <= 1);
                            if state_size[sp] == 1 {
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
                                new_instructions.insert(0, BlockContent::Stmt(bp_update_stmt));
                                // %PHY[%SP + 0] = %BP
                                new_instructions.insert(0, BlockContent::MemPush(("%BP".to_string(), Ty::Field, 0)));
                            } else {
                                altered = true;
                            }
                            state.pop();
                            state_size.pop();
                        } else {
                            // Use state to determine whether stack entry is alive
                            if *offset < state[sp].len() && state[sp][*offset] {
                                state_size[sp] -= 1;
                                new_instructions.insert(0, BlockContent::MemPush((var.to_string(), ty.clone(), state_size[sp])));
                            } else {
                                altered = true;
                            }
                        }
                    }
                    BlockContent::Stmt(s) => {
                        // %SP = %SP + X
                        if pmr_is_push(&s) {
                            if state_size[sp] != 0 {
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
                                                value: state_size[sp].to_string(),
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
                                new_instructions.insert(0, BlockContent::Stmt(sp_update_stmt));                                 
                            } else {
                                altered = true;
                            }
                        } else {
                            if !pmr_is_bp_update(&s) {
                                new_instructions.insert(0, i.clone());
                            } else {
                                altered = true;
                            }
                        }
                    }
                }
            }
            bls[cur_bl].instructions = new_instructions;

            // Block Transition
            for tmp_bl in predecessor_fn[cur_bl].clone() {
                next_bls.push_back(tmp_bl);
            }
        }
    }
    
    return (bls, altered);
}

// EBE: Backward analysis
// If a block is empty and its terminator is a coda (to another block or %RP)
// replace all the reference to it in its predecessors with that terminator
// If a block terminates with a branching and both branches to the same block, eliminate the branching

// We assume that something would happen after the function call, so we do not change the value of any %RP
// This would not affect correctness. Worst case it might make DBE later inefficient.

// CFG will be DESTROYED after this! Only do it after all statement analyses.
fn empty_block_elimination(
    mut bls: Vec<Block>,
    exit_bls: HashSet<usize>,
    mut successor: Vec<HashSet<usize>>,
    mut predecessor: Vec<HashSet<usize>>
) -> (Vec<HashSet<usize>>, Vec<HashSet<usize>>, Vec<Block>) {

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
        let _ = std::mem::replace(&mut visited[eb], true);
    }
    // Backward analysis!
    while !next_bls.is_empty() {
        let cur_bl = next_bls.pop_front().unwrap();

        // Update the terminator of all predecessor
        for tmp_bl in predecessor[cur_bl].clone() {
            // The only cases we need to continue is
            // either we haven't processed the predecessor
            // or cur_bl is empty so predecessors will be changed
            if !visited[tmp_bl] || bls[cur_bl].instructions.len() == 0 {
                let _ = std::mem::replace(&mut visited[tmp_bl], true);
                
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
    bls: Vec<Block>,
    entry_bl: usize,
    predecessor: Vec<HashSet<usize>>
) -> (Vec<Block>, usize, HashMap<usize, usize>) {      
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

// For each block, set its input to be variables that are alive at the entry point of the block and their type
// Returns: bls
// This pass consists of a liveness analysis and a reaching definition (for typing)
fn set_input_output<'bl>(
    mut bls: Vec<Block<'bl>>,
    successor: &Vec<HashSet<usize>>,
    predecessor: &Vec<HashSet<usize>>,
    entry_bl: &usize,
    exit_bls: &HashSet<usize>,
    inputs: Vec<(String, Ty)>
) -> Vec<Block<'bl>> {
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

        // State is the union of all successors
        let mut state: HashSet<String> = HashSet::new();
        // Add %oRET to output of every exit blocks
        if exit_bls.contains(&cur_bl) {
            state.insert("%RET".to_string());
        }
        for s in &successor[cur_bl] {
            state.extend(bl_in[*s].clone());
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
            // We assume that liveness analysis has been performed, don't reason about usefulness of variables
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
            for tmp_bl in predecessor[cur_bl].clone() {
                next_bls.push_back(tmp_bl);
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
        // If we are at entry block, state also includes *live* program parameters
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
                    BlockContent::MemPop(_) => {}
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
            for tmp_bl in successor[cur_bl].clone() {
                next_bls.push_back(tmp_bl);
            }
        }    
    }

    let ty_map_in = bl_in;
    let ty_map_out = bl_out;

    // Update input of all blocks
    // Note: block 0 takes function input and %BN as input
    for i in 0..bls.len() {
        // For this primitive implementation, take every register up to reg_size as input
        // Something fishy is going on if inputs or outputs have been defined
        assert!(bls[i].inputs.len() == 0);
        if i != 0 {
            for name in input_lst[i].iter().sorted() {
                bls[i].inputs.push((name.to_string(), Some(ty_map_in[i].get(name).unwrap().clone())));
            }
        }
        assert!(bls[i].outputs.len() == 0);
        for name in output_lst[i].iter().sorted() {
            bls[i].outputs.push((name.to_string(), Some(ty_map_out[i].get(name).unwrap().clone())));
        }
    }
    for (name, ty) in &inputs {
        bls[0].inputs.push((name.to_string(), Some(ty.clone())));
    }

    return bls;
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
    str_name: String,
    mut reg_map: HashMap<String, usize>,
) -> (String, HashMap<String, usize>, usize) {
    let reg_size = reg_map.len();
    
    // Strip the scoping "@x" from the variable name
    let var_name = str_name.split('@').collect::<Vec<&str>>()[0].to_string();

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

// Convert all mentionings of variables to registers
// Registers are divided into three categories: inputs, outputs, and witnesses
// size of inputs = size of outputs && 2 * (size of inputs + 1) = size of witnesses
// However, we won't know the size of witnesses until circuit generation,
// hence need to record inputs, outputs, and witnesses separately
// Structure for input / output
// reg  0   1   2   3   4   5   6   7  ...
//      V  BN  RP  SP  BP  RET i6  i7
// Structure for witness
// reg  0   1   2   3   4   5   6   7  ...
//     w0  w1  w2  w3  w4  w5  w6  w7
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
    mut bls: Vec<Block>,
    entry_bl: usize,
    inputs: Vec<(String, Ty)>
) -> (Vec<Block>, Vec<HashMap<String, usize>>, usize, HashMap<String, usize>, usize, Vec<(Vec<usize>, Vec<usize>)>) {
    // Construct a new CFG for the program
    // Note that this is the CFG after DBE, and might be different from the previous CFG
    let (successor, predecessor, _, _, _, _, _) = 
        construct_flow_graph(&bls, entry_bl);
    
    // reg_map is consisted of two Var -> Reg Maps: TRANSITION_MAP_LIST & WITNESS_MAP
    // TRANSITION_MAP_LIST is a list of maps corresponding to each transition state
    // Reserve registers 0 - 5 for %V, %NB, %RP, %SP, %BP, and %RET
    let mut transition_map_list = Vec::new();
    // MAX_IO_SIZE is the size of the largest maps among TRANSITION_MAP_LIST
    let mut max_io_size = 0;
    // BL_IN and BL_OUT records which transition state the inputs & outputs of each block is in
    // TRANSITION_MAP_LIST[BL_IN[X]] is the register map used by the inputs of block X
    let mut bl_in: Vec<Option<usize>> = vec![None; bls.len()];
    let mut bl_out: Vec<Option<usize>> = vec![None; bls.len()];

    // Process program inputs
    let input_map = {
        let mut io_map: HashMap<String, usize> = HashMap::new();
        // Reserved registers
        (_, io_map, _) = var_name_to_reg_id_expr::<1>("%V".to_string(), io_map);
        (_, io_map, _) = var_name_to_reg_id_expr::<1>("%NB".to_string(), io_map);
        (_, io_map, _) = var_name_to_reg_id_expr::<1>("%RP".to_string(), io_map);
        (_, io_map, _) = var_name_to_reg_id_expr::<1>("%SP".to_string(), io_map);
        (_, io_map, _) = var_name_to_reg_id_expr::<1>("%BP".to_string(), io_map);
        (_, io_map, _) = var_name_to_reg_id_expr::<1>("%RET".to_string(), io_map);
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
            let mut io_map = {
                let mut io_map: HashMap<String, usize> = HashMap::new();
                // Reserved registers
                (_, io_map, _) = var_name_to_reg_id_expr::<1>("%V".to_string(), io_map);
                (_, io_map, _) = var_name_to_reg_id_expr::<1>("%NB".to_string(), io_map);
                (_, io_map, _) = var_name_to_reg_id_expr::<1>("%RP".to_string(), io_map);
                (_, io_map, _) = var_name_to_reg_id_expr::<1>("%SP".to_string(), io_map);
                (_, io_map, _) = var_name_to_reg_id_expr::<1>("%BP".to_string(), io_map);
                (_, io_map, _) = var_name_to_reg_id_expr::<1>("%RET".to_string(), io_map);
                io_map
            };

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
    // Reserve registers 0 - 3 for %RP, %SP, %BP, and %RET
    let mut witness_map: HashMap<String, usize> = HashMap::new();
    (_, witness_map, _) = var_name_to_reg_id_expr::<0>("%RP".to_string(), witness_map);
    (_, witness_map, _) = var_name_to_reg_id_expr::<0>("%SP".to_string(), witness_map);
    (_, witness_map, _) = var_name_to_reg_id_expr::<0>("%BP".to_string(), witness_map);
    (_, witness_map, _) = var_name_to_reg_id_expr::<0>("%RET".to_string(), witness_map);


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
                    let var_name: String;
                    (var_name, witness_map, _) = var_name_to_reg_id_expr::<0>(var.to_string(), witness_map);
                    new_instr.push(BlockContent::MemPush((var_name, ty.clone(), *offset)));
                }
                BlockContent::MemPop((var, ty, offset)) => {
                    let var_name: String;
                    (var_name, witness_map, _) = var_name_to_reg_id_expr::<0>(var.to_string(), witness_map);
                    new_instr.push(BlockContent::MemPop((var_name, ty.clone(), *offset)));
                }
                BlockContent::Stmt(Statement::Return(_)) => {
                    panic!("Blocks should not contain return statements.");
                }
                BlockContent::Stmt(Statement::Assertion(a)) => {
                    let new_expr: Expression;
                    (new_expr, witness_map) = var_to_reg_expr(&a.expression, witness_map);
                    let new_stmt = AssertionStatement {
                        expression: new_expr,
                        message: a.message.clone(),
                        span: a.span
                    };
                    new_instr.push(BlockContent::Stmt(Statement::Assertion(new_stmt)));
                }
                BlockContent::Stmt(Statement::Iteration(_)) => {
                    panic!("Blocks should not contain iteration statements.")
                }
                BlockContent::Stmt(Statement::Conditional(_)) => {
                    panic!("Blocks should not contain if / else statements.")
                }
                BlockContent::Stmt(Statement::Definition(d)) => {
                    let mut new_lhs: Vec<TypedIdentifierOrAssignee> = Vec::new();
                    for l in &d.lhs {
                        match l {
                            TypedIdentifierOrAssignee::TypedIdentifier(tid) => {
                                let new_id_expr: IdentifierExpression;
                                (new_id_expr, witness_map) = var_to_reg_id_expr(&tid.identifier, witness_map);
                                new_lhs.push(TypedIdentifierOrAssignee::TypedIdentifier(TypedIdentifier{
                                    ty: tid.ty.clone(),
                                    identifier: new_id_expr,
                                    span: tid.span
                                }));
                            }
                            TypedIdentifierOrAssignee::Assignee(p) => {
                                let new_id_expr: IdentifierExpression;
                                (new_id_expr, witness_map) = var_to_reg_id_expr(&p.id, witness_map);
                                let mut new_accesses: Vec<AssigneeAccess> = Vec::new();
                                for aa in &p.accesses {
                                    if let AssigneeAccess::Select(a) = aa {
                                        if let RangeOrExpression::Expression(e) = &a.expression {
                                            let new_expr: Expression;
                                            (new_expr, witness_map) = var_to_reg_expr(&e, witness_map);
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
                    (new_expr, witness_map) = var_to_reg_expr(&d.expression, witness_map);
                    let new_stmt = DefinitionStatement {
                        lhs: new_lhs,
                        expression: new_expr,
                        span: d.span
                    };
                    new_instr.push(BlockContent::Stmt(Statement::Definition(new_stmt)));
                }
                BlockContent::Stmt(Statement::CondStore(_)) => { panic!("Blocks should not contain conditional store statements.") }
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
