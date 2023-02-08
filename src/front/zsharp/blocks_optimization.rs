use std::collections::VecDeque;
use zokrates_pest_ast::*;
use crate::front::zsharp::blocks::*;

// Remove all the dead blocks in the list
// Rename all block labels so that they are still consecutive
// Return value: bls, entry_bl, exit_bl
pub fn dead_block_elimination(
    bls: Vec<Block>,
    entry_bl: usize, 
) -> (Vec<Block>, usize) {      
    let old_size = bls.len();
    
    // Visited: have we ever visited the block in the following DFS?
    let mut visited: Vec<bool> = Vec::new();
    for _ in 0..old_size {
        visited.push(false);
    }

    // DFS through all blocks starting from entry_bl
    // Use next_bls to record all the nodes that we will visit next
    // Whenever we encounter `%RP = <const>` we need to visit that block as well,
    // however, we don't need to do anything if a block terminates with rp() (i.e. end of function call)
    let mut next_bls: VecDeque<usize> = VecDeque::new();
    let _ = std::mem::replace(&mut visited[entry_bl], true);
    next_bls.push_back(entry_bl);
    while !next_bls.is_empty() {
        let cur_bl = next_bls.pop_front().unwrap();
        
        // If we encounter any %RP = <counter>, append <counter> to next_bls
        for bc in &bls[cur_bl].instructions {
            // We can ignore memory for now
            // The only case currently is %RP on the left & constant on the right
            if let BlockContent::Stmt(Statement::Definition(d)) = bc {
                if let TypedIdentifierOrAssignee::Assignee(a) = &d.lhs[0] {
                    if a.id.value == "%RP".to_string() {
                        if let Expression::Literal(LiteralExpression::DecimalLiteral(dle)) = &d.expression {
                            let tmp_bl: usize = dle.value.value.trim().parse().expect("Dead Block Elimination failed: %RP is assigned to a non-constant value");
                            if !visited[tmp_bl] {
                                let _ = std::mem::replace(&mut visited[tmp_bl], true);
                                next_bls.push_back(tmp_bl);
                            }
                        } else {
                            panic!("Dead Block Elimination failed: %RP is assigned to a non-constant value")
                        }
                    }
                }
            }
        }
        
        // Append everything in the terminator of cur_bl to next_bls
        // if they have not been visited before
        match bls[cur_bl].terminator.clone() {
            BlockTerminator::Transition(t) => {
                if let NextBlock::Label(tmp_bl) = t.tblock {
                    if !visited[tmp_bl] {
                        let _ = std::mem::replace(&mut visited[tmp_bl], true);
                        next_bls.push_back(tmp_bl);
                    }
                }
                if let NextBlock::Label(tmp_bl) = t.fblock {
                    if !visited[tmp_bl] {
                        let _ = std::mem::replace(&mut visited[tmp_bl], true);
                        next_bls.push_back(tmp_bl);
                    }
                }
            }
            BlockTerminator::Coda(n) => {
                if let NextBlock::Label(tmp_bl) = n {
                    if !visited[tmp_bl] {
                        let _ = std::mem::replace(&mut visited[tmp_bl], true);
                        next_bls.push_back(tmp_bl);
                    }
                }
            }
            BlockTerminator::FuncCall(_) => { panic!("Blocks pending optimization should not have FuncCall as terminator.") }
            BlockTerminator::ProgTerm() => {}
        }
    }

    // Initialize map from old label of blocks to new labels
    let mut label_map = Vec::new();
    // Initialize a new list of blocks
    let mut new_bls = Vec::new();

    // Iterate through all blocks. If it was never visited, delete it and update next_bls
    let mut new_label = 0;
    for old_label in 0..old_size {
        label_map.push(new_label);
        if visited[old_label] {
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
    let new_entry_bl = label_map[entry_bl];
    let new_size = new_label;

    // Iterate through all new blocks again, update %RP and Block Terminator
    for cur_bl in 0..new_size {

        // If we encounter any %RP = <counter>, update <counter> to label_map[<counter>]
        for i in 0..new_bls[cur_bl].instructions.len() {
            let bc = new_bls[cur_bl].instructions[i].clone();
            if let BlockContent::Stmt(Statement::Definition(d)) = bc {
                if let TypedIdentifierOrAssignee::Assignee(a) = &d.lhs[0] {
                    if a.id.value == "%RP".to_string() {
                        if let Expression::Literal(LiteralExpression::DecimalLiteral(dle)) = &d.expression {
                            let tmp_bl: usize = dle.value.value.trim().parse().unwrap();
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
                                        value: label_map[tmp_bl].to_string(),
                                        span: Span::new("", 0, 0).unwrap()
                                    },
                                    suffix: Some(DecimalSuffix::Field(FieldSuffix {
                                        span: Span::new("", 0, 0).unwrap()
                                    })),
                                    span: Span::new("", 0, 0).unwrap()
                                })),
                                span: Span::new("", 0, 0).unwrap()
                            });
                            let _ = std::mem::replace(&mut new_bls[cur_bl].instructions[i], BlockContent::Stmt(new_rp_stmt));
                        }
                    }
                }
            }
        }
        
        // Append everything in the terminator of cur_bl to next_bls
        // if they have not been visited before
        let mut new_term: BlockTerminator;
        match new_bls[cur_bl].terminator.clone() {
            BlockTerminator::Transition(t) => {
                let mut new_trans = BlockTransition {
                    cond: t.cond.clone(),
                    tblock: NextBlock::Rp(),
                    fblock: NextBlock::Rp()
                };
                if let NextBlock::Label(tmp_bl) = t.tblock {
                    new_trans.tblock = NextBlock::Label(label_map[tmp_bl]);
                }
                if let NextBlock::Label(tmp_bl) = t.fblock {
                    new_trans.fblock = NextBlock::Label(label_map[tmp_bl]);
                }
                new_term = BlockTerminator::Transition(new_trans);
            }
            BlockTerminator::Coda(n) => {
                new_term = BlockTerminator::Coda(NextBlock::Rp());
                if let NextBlock::Label(tmp_bl) = n {
                    new_term = BlockTerminator::Coda(NextBlock::Label(label_map[tmp_bl]));
                }
            }
            BlockTerminator::FuncCall(_) => { new_term = bls[cur_bl].terminator.clone(); }
            BlockTerminator::ProgTerm() => { new_term = bls[cur_bl].terminator.clone(); }
        }
        new_bls[cur_bl].terminator = new_term;
    }
    return (new_bls, new_entry_bl)
}