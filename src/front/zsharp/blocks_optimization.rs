use std::collections::VecDeque;
use zokrates_pest_ast::*;
use crate::front::zsharp::blocks::*;
use crate::front::zsharp::pretty::*;
use std::collections::HashMap;
use std::collections::HashSet;

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

pub fn optimize_block(
    mut bls: Vec<Block>,
    mut entry_bl: usize
) -> (Vec<Block>, usize) {
    let (successor, mut predecessor, exit_bls, entry_bls_fn, successor_fn, predecessor_fn, exit_bls_fn) = 
        construct_flow_graph(&bls, entry_bl);
    print_cfg(&successor, &predecessor, &exit_bls, &entry_bls_fn, &successor_fn, &predecessor_fn, &exit_bls_fn);
    println!("\n\n--\nOptimization:");
    bls = liveness_analysis(bls, &successor_fn, &predecessor_fn, &exit_bls_fn);
    println!("\n\n--\nLiveness:");
    println!("Entry block: {entry_bl}");      
    for b in &bls {
        b.pretty();
        println!("");
    }
    (_, predecessor, bls) = empty_block_elimination(bls, exit_bls, successor, predecessor);
    println!("\n\n--\nEBE:");
    println!("Entry block: {entry_bl}");      
    for b in &bls {
        b.pretty();
        println!("");
    }
    (bls, entry_bl) = dead_block_elimination(bls, entry_bl, predecessor);
    println!("\n\n--\nDBE:");
    println!("Entry block: {entry_bl}");      
    for b in &bls {
        b.pretty();
        println!("");
    }
    return (bls, entry_bl);
} 

// If bc is a statement of form %RP = val,
// return val
fn rp_find_val(bc: BlockContent) -> Option<usize> {
    // We can ignore memory for now
    // The only case currently is %RP on the left & constant on the right
    if let BlockContent::Stmt(Statement::Definition(d)) = bc {
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
        if let TypedIdentifierOrAssignee::Assignee(a) = &d.lhs[0] {
            if a.id.value == "%RP".to_string() {
                if let Expression::Literal(LiteralExpression::DecimalLiteral(dle)) = &d.expression {
                    let tmp_bl: usize = dle.value.value.trim().parse().unwrap();
                    if let Some(new_bl) = val_map.get(&tmp_bl) {
                        let new_rp_stmt = Statement::Definition(DefinitionStatement {
                            lhs: vec![TypedIdentifierOrAssignee::Assignee(Assignee {
                                id: IdentifierExpression {
                                    value: "%RP".to_string(),
                                    span: Span::new("", 0, 0).unwrap()
                                },
                                accesses: Vec::new(),
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
                return vec![NextBlock::Rp()]
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
        NextBlock::Rp() => {
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
    // list of all blocks that ends with ProgTerm or Rp()
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
                    if b == NextBlock::Rp() {
                        exit_bls_fn.insert(cur_bl);
                    }
                }
            }
            BlockTerminator::FuncCall(_) => { panic!("Blocks pending optimization should not have FuncCall as terminator.") }
            BlockTerminator::ProgTerm() => { 
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
    }
}

// The analysis skips function calls (go straight from func call block to return block)
// Since we don't have SSA, liveness analysis is a lot more complicated
// The following analysis is based on the assumption that every PUSH of a variable will
// be accompanied by a POP sometime later before the program terminates (and there are finite many of them)
// We do not analyze the liveness of %BP, %SP, %RP, %RET, or %ARG
// DIRECTION: Backward
// LATTICE:
//   TOP: Variable does not exist in the set
//   Otherwise, a variable state is defined as a list of bits, corresponding to its liveness in each stack frame
//     e.g. [0, 1, 0, 0, 1]: live at current scope (last bit), live at stack frame 1, dead at stack frame 0, 2, 3
//   BOT: Does not exist (I think?)
// TRANSFER:
//    GEN: If a variable is referenced, excluding PUSH to stack,
//         - if it is TOP, set the state to [1] (live at current scope, not appearing in stack)
//         - otherwise, update the last bit of its state to 1 (live at current scope, unchanged in stack)
//   KILL: If a variable is assigned, excluding POP from stack,
//         - if it is TOP or if the last bit of its state is 0, remove the statement
//         - if it is TOP, set the state to [0] (dead at current scope, not appearing in stack)
//         - if it is not TOP, update the last bit of its state to 0 (dead at current scope, unchanged in stack)
//    POP: If a variable is popped out from the stack,
//         - if it is TOP or if the last bit of its state is 0, remove the statement
//         - if it is TOP, set the state to [0, 0] (dead at new scope, dead in stack, 
//               we are doing backward analysis, so POP corresponds to extension of the state) 
//         - otherwise, set the last bit to 0 and extend the state by another 0
//   PUSH: If a variable is pushed onto stack,
//         - remove the last bit of the variable state (again, we are doing things backwards)
//         - the new state should not be TOP if each PUSH has a corresponding POP
//         - if the last bit of the new state is 0, remove the statement
//               (need to deal with holes in physical memory later)
// MEET:
//    TOP meets anything else is always the other things
//    If two variable states have the same length, their MEET is the pairwise union of the two lists
//    If two variable states have different length, their MEET is undefined. This should never happen because
//    you can only enter (or exit) a block from the same scope. 

// MEET of liveness_analysis
fn la_meet(
    first: &HashMap<String, Vec<bool>>,
    second: &HashMap<String, Vec<bool>>
) -> HashMap<String, Vec<bool>> {
    let mut third = first.clone();
    for (var, state_sec) in second.iter() {
        if let Some(state_fst) = third.get(var) {
            if state_fst.len() != state_sec.len() {
                panic!("Liveness analysis MEET fails: variable {} has different scoping:\nFirst state is {:?}\nSecond state is {:?}\n", var, state_fst, state_sec)
            } else {
                third.insert(var.to_string(), (0..state_fst.len()).map(|x| state_fst[x] || state_sec[x]).collect::<Vec<_>>());
            }
        } else {
            third.insert(var.to_string(), (*state_sec.clone()).to_vec());
        }
    }
    third
}

// GEN all variables in gen
fn la_gen(
    mut state: HashMap<String, Vec<bool>>,
    gen: &HashSet<String>
) -> HashMap<String, Vec<bool>> {
    // Add all gens to state
    for v in gen {
        match state.get(v) {
            None => { state.insert(v.to_string(), vec![true]); }
            Some(_) => {
                let mut v_state: Vec<bool> = (*state.get(v).unwrap().clone()).to_vec();
                v_state.pop();
                v_state.push(true);
                state.insert(v.to_string(), v_state);
            }                                    
        }
    }
    state
}

// KILL all variables in kill
fn la_kill(
    mut state: HashMap<String, Vec<bool>>,
    kill: &HashSet<String>
) -> HashMap<String, Vec<bool>> {
    // Remove all kills to state
    for v in kill {
        match state.get(v) {
            None => { state.insert(v.to_string(), vec![false]); }
            Some(_) => {
                let mut v_state: Vec<bool> = (*state.get(v).unwrap().clone()).to_vec();
                v_state.pop();
                v_state.push(false);
                state.insert(v.to_string(), v_state);
            }                                    
        }
    }
    state
}

// Liveness analysis should not affect CFG
fn liveness_analysis<'ast>(
    mut bls: Vec<Block<'ast>>,
    successor_fn: &Vec<HashSet<usize>>,
    predecessor_fn: &Vec<HashSet<usize>>,
    exit_bls_fn: &HashSet<usize>
) -> Vec<Block<'ast>> {

    let mut visited: Vec<bool> = Vec::new();
    // MEET is union, so IN and OUT are Empty Set
    let mut bl_in: Vec<HashMap<String, Vec<bool>>> = Vec::new();
    let mut bl_out: Vec<HashMap<String, Vec<bool>>> = Vec::new();
    for _ in 0..bls.len() {
        visited.push(false);
        bl_in.push(HashMap::new());
        bl_out.push(HashMap::new());
    }
    
    // Can this ever happen?
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

        // State is the Union of all successors AND the exit condition
        let mut state: HashMap<String, Vec<bool>> = HashMap::new();
        for s in &successor_fn[cur_bl] {
            println!("{}", s);
            state = la_meet(&state, &bl_in[*s]);
        }
        println!();
        match &bls[cur_bl].terminator {
            BlockTerminator::Transition(e) => { state = la_gen(state, &expr_find_val(e)); }
            BlockTerminator::FuncCall(_) => { panic!("Blocks pending optimization should not have FuncCall as terminator.") }
            BlockTerminator::ProgTerm() => {}            
        }

        // Only analyze if never visited before or OUT changes
        if !visited[cur_bl] || state != bl_out[cur_bl] {
            
            bl_out[cur_bl] = state.clone();
            let _ = std::mem::replace(&mut visited[cur_bl], true);
            let mut new_instructions = Vec::new();

            // KILL and GEN within the block
            for i in bls[cur_bl].instructions.iter().rev() {
                match i {
                    BlockContent::MemPush((var, _)) => {
                        let mut v_state: Vec<bool> = (*state.get(var).unwrap().clone()).to_vec();
                        v_state.pop();
                        state.insert(var.to_string(), v_state);
                        new_instructions.insert(0, i.clone());
                    }
                    BlockContent::MemPop((var, _)) => {
                        if (state.get(var) != None && state.get(var).unwrap()[state.get(var).unwrap().len() - 1]) || var.chars().next().unwrap() == '%' {
                            new_instructions.insert(0, i.clone());
                        }
                        match state.get(var) {
                            None => { state.insert(var.to_string(), vec![false, false]); }
                            Some(_) => {
                                let mut v_state: Vec<bool> = (*state.get(var).unwrap().clone()).to_vec();
                                v_state.push(false);
                                state.insert(var.to_string(), v_state);
                            }
                        }
                    }
                    BlockContent::Stmt(s) => {
                        let (kill, gen) = stmt_find_val(s);
                        if kill.len() > 1 {
                            panic!("Assignment to multiple variables not supported");
                        }
                        // If it's not a definition or the defined variable is alive,
                        // or if it involves register value (%RP, %BP, %SP, %RET, %ARG)
                        // mark the variable dead and append gen to state
                        // Otherwise remove the statement
                        let mut contains_reg = kill.iter().fold(false, |c, x| c || x.chars().next().unwrap() == '%');
                        contains_reg = gen.iter().fold(contains_reg, |c, x| c || x.chars().next().unwrap() == '%');
                        
                        if kill.is_empty() || kill.iter().fold(false, |c, x| c || state.get(x) != None) || contains_reg {
                            // Remove kill from state
                            state = la_kill(state, &kill);

                            // Add all gens to state
                            state = la_gen(state, &gen);
                            new_instructions.insert(0, i.clone());
                        }
                    }
                }
            }

            bls[cur_bl].instructions = new_instructions;
            bl_in[cur_bl] = state;

            // Block Transition
            for tmp_bl in predecessor_fn[cur_bl].clone() {
                next_bls.push_back(tmp_bl);
            }
        }    
    }
    return bls;
}

// Backward analysis
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

// Remove all the dead blocks in the list
// Rename all block labels so that they are still consecutive
// Return value: bls, entry_bl, exit_bl
fn dead_block_elimination(
    bls: Vec<Block>,
    entry_bl: usize,
    predecessor: Vec<HashSet<usize>>
) -> (Vec<Block>, usize) {      
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
            let tmp_bl = Block {
                name: new_label,
                // No need to store statements if we are at the exit block
                instructions: bls[old_label].instructions.clone(),
                terminator: bls[old_label].terminator.clone()
            };
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
    return (new_bls, new_entry_bl);
}