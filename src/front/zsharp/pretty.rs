use zokrates_pest_ast::*;
use crate::front::zsharp::blocks::BlockContent;

pub fn pretty_block_content(indent: usize, bc: &BlockContent) {
    for _ in 0..indent * 4 {
        print!(" ");
    }
    match bc {
        BlockContent::MemPush((val, ty, offset)) => { println!("%PHY[%SP + {offset}] = {} <{ty}>", pretty_name(val)) }
        BlockContent::MemPop((val, ty, offset)) => { println!("{ty} {} = %PHY[%BP + {offset}]", pretty_name(val)) }
        BlockContent::ArrayInit((arr, ty, size)) => { println!("{ty}[{size}] {arr}") }
        BlockContent::Store((val, ty, arr, id, init)) => { 
            print!("{arr}["); 
            pretty_expr::<false>(&id); print!("] = "); 
            pretty_expr::<false>(&val); 
            print!(" <{ty}>");
            if *init { print!(", init"); }
            println!(); 
        }
        BlockContent::Load((val, ty, arr, id)) => { print!("{ty} {} = {arr}[", pretty_name(val)); pretty_expr::<false>(&id); println!("]"); }
        BlockContent::DummyLoad() => { println!("Dummy Load"); }
        BlockContent::Branch((cond, if_insts, else_insts)) => { 
            print!("if ");
            pretty_expr::<false>(cond);
            println!(":");
            for i in if_insts {
                pretty_block_content(indent + 1, i);
            }
            if else_insts.len() > 0 {
                for _ in 0..indent * 4 {
                    print!(" ");
                }
                println!("else:");
                for i in else_insts {
                    pretty_block_content(indent + 1, i);
                }
            }
         }
        BlockContent::Stmt(s) => { pretty_stmt(0, &s); }
    }
}

pub fn pretty_stmt(indent: usize, s: &Statement) {
    for _ in 0..indent * 4 {
        print!(" ");
    }
    match s {
        Statement::Return(r) => { pretty_ret_stmt(r); }
        Statement::Definition(d) => { pretty_def_stmt(d); }
        Statement::Assertion(a) => { pretty_ass_stmt(a); }
        Statement::Iteration(i) => { pretty_ite_stmt(indent, i); }
        Statement::WhileLoop(w) => { pretty_while_stmt(indent, w); }
        Statement::Conditional(c) => { pretty_cond_stmt(indent, c); }
        Statement::CondStore(_) => { panic!("Conditional store statements not supported.") }
    }
}

fn pretty_ret_stmt(r: &ReturnStatement) {
    print!("return ");
    pretty_expr::<false>(&r.expressions[0]);
    for e in &r.expressions[1..] {
        print!(", ");
        pretty_expr::<false>(e);
    }
    println!("");
}

fn pretty_def_stmt(d: &DefinitionStatement) {
    match &d.lhs[0] {
        TypedIdentifierOrAssignee::Assignee(a) => {
            pretty_ident_expr(&a.id);
            if a.accesses.len() > 0 {
                if let AssigneeAccess::Select(s) = &a.accesses[0] {
                    pretty_arrayaccess(s);
                }
            }
        }
        TypedIdentifierOrAssignee::TypedIdentifier(ti) => pretty_typed_ident(&ti)
    }
    for l in &d.lhs[1..] {
        print!(", ");
        match l {
            TypedIdentifierOrAssignee::Assignee(a) => { pretty_ident_expr(&a.id); }
            TypedIdentifierOrAssignee::TypedIdentifier(ti) => { pretty_typed_ident(&ti); }
        }        
    }
    print!(" = ");
    pretty_expr::<false>(&d.expression);
    println!("");
}

fn pretty_ass_stmt(a: &AssertionStatement) {
    print!("assert ");
    pretty_expr::<false>(&a.expression);
    println!("");
}

fn pretty_ite_stmt(indent: usize, i: &IterationStatement) {
    print!("for ");
    pretty_type(&i.ty);
    print!(" ");
    pretty_ident_expr(&i.index);
    print!(" in ");
    pretty_expr::<false>(&i.from);
    print!(" .. ");
    pretty_expr::<false>(&i.to);
    println!(":");
    for s in &i.statements {
        pretty_stmt(indent + 1, &s);
    }
}

fn pretty_while_stmt(indent: usize, w: &WhileLoopStatement) {
    print!("while ");
    pretty_expr::<false>(&w.condition);
    println!(":");
    for s in &w.statements {
        pretty_stmt(indent + 1, &s);
    }
}

fn pretty_cond_stmt(indent: usize, c: &ConditionalStatement) {
    print!("if ");
    pretty_expr::<false>(&c.condition);
    println!(":");
    for s in &c.ifbranch {
        pretty_stmt(indent + 1, &s);
    }
    for _ in 0..indent * 4 {
        print!(" ");
    }
    println!("else:");
    for s in &c.elsebranch {
        pretty_stmt(indent + 1, &s);
    }
}

fn pretty_typed_ident(ti: &TypedIdentifier) {
    pretty_type(&ti.ty);
    print!(" ");
    pretty_ident_expr(&ti.identifier);
}

fn pretty_type(ty: &Type) {
    match ty {
        Type::Basic(BasicType::Field(_)) => { print!("field"); }
        Type::Basic(BasicType::Boolean(_)) => { print!("bool"); }
        Type::Basic(BasicType::U8(_)) => { print!("u8"); }
        Type::Basic(BasicType::U16(_)) => { print!("u16"); }
        Type::Basic(BasicType::U32(_)) => { print!("u32"); }
        Type::Basic(BasicType::U64(_)) => { print!("u64"); }
        Type::Struct(_) => { print!("struct"); }
        Type::Array(_) => { print!("array"); }
    }
}

pub fn pretty_expr<const IS_BLK: bool>(e: &Expression) {
    match e {
        Expression::Ternary(t) => {
            if IS_BLK {
                print!("\n    ");
            }
            pretty_expr::<false>(&t.first);
            print!(" ? ");
            pretty_expr::<IS_BLK>(&t.second);
            print!(" : ");
            pretty_expr::<IS_BLK>(&t.third);
        }
        Expression::Binary(b) => {
            pretty_expr::<IS_BLK>(&b.left);
            print!(" {} ", get_bin_op(&b.op));
            pretty_expr::<IS_BLK>(&b.right);
        }
        Expression::Unary(u) => {
            print!("{}", get_un_op(&u.op));
            pretty_expr::<IS_BLK>(&u.expression);
        }
        Expression::Postfix(p) => {
            pretty_ident_expr(&p.id);
            if p.accesses.len() > 0 {
                if let Access::Select(s) = &p.accesses[0] {
                    pretty_arrayaccess(s);
                }
            }
        }
        Expression::Identifier(i) => {
            if IS_BLK {
                print!("-> ")
            }
            pretty_ident_expr(i);
        }
        Expression::Literal(l) => {
            if IS_BLK {
                print!("-> ")
            }
            pretty_literal::<IS_BLK>(l);
        }
        _ => {
            panic!("Pretty print for expression yet to be implemented.");
        }
    }
}

fn pretty_ident_expr(i: &IdentifierExpression) {
    print!("{}", pretty_name(&i.value));
}

// Structure for input / output
// reg  0   1   2   3   4   5   6   7   8  ...
//      V  BN  RET TS  AS  RP  SP  BP  i8
// Structure for witness
// reg  0   1   2   3   4   5   6   7  ...
//     RET TS  AS  RP  SP  BP  w6  w7
pub fn pretty_name(name: &str) -> String {
    // Strip the 0s from the name
    let mut name = name.to_string();
    while name.len() > 3 && name.chars().collect::<Vec<char>>()[2] == '0' { name.remove(2); }
    match name.as_str() {
        "%i0" => "%0(V)",
        "%i1" => "%i1(BN)",
        "%i2" => "%i2(RET)",
        "%i3" => "%i3(TS)",
        "%i4" => "%i4(AS)",
        "%i5" => "%i5(RP)",
        "%i6" => "%i6(SP)",
        "%i7" => "%i7(BP)",
        "%o1" => "%o1(BN)",
        "%o2" => "%o2(RET)",
        "%o3" => "%o3(TS)",
        "%o4" => "%o4(AS)",
        "%o5" => "%o5(RP)",
        "%o6" => "%o6(SP)",
        "%o7" => "%o7(BP)",
        "%w0" => "%w0(RET)",
        "%w1" => "%w1(TS)",
        "%w2" => "%w2(AS)",
        "%w3" => "%w3(RP)",
        "%w4" => "%w4(SP)",
        "%w5" => "%w5(BP)",
        _ => name.as_str()
    }.to_string()
}

fn get_un_op(op: &UnaryOperator) -> &str {
    match op {
        UnaryOperator::Pos(_) => "+",
        UnaryOperator::Neg(_) => "-",
        UnaryOperator::Not(_) => "!",
        UnaryOperator::Strict(_) => "#"
    }
}

fn get_bin_op(op: &BinaryOperator) -> &str {
    match op {
        BinaryOperator::BitXor => { "^" }
        BinaryOperator::BitAnd => { "&" }
        BinaryOperator::BitOr => { "|" }
        BinaryOperator::RightShift => { ">>" }
        BinaryOperator::LeftShift => { "<<" }
        BinaryOperator::Or => { "||" }
        BinaryOperator::And => { "&&" }
        BinaryOperator::Add => { "+" }
        BinaryOperator::Sub => { "-" }
        BinaryOperator::Mul => { "*" }
        BinaryOperator::Div => { "/" }
        BinaryOperator::Rem => { "%" }
        BinaryOperator::Eq => { "==" }
        BinaryOperator::NotEq => { "!=" }
        BinaryOperator::Lt => { "<" }
        BinaryOperator::Gt => { ">" }
        BinaryOperator::Lte => { "<=" }
        BinaryOperator::Gte => { ">=" }
        BinaryOperator::Pow => { "**" }
    }
}

fn pretty_literal<const IS_BLK: bool>(l: &LiteralExpression) {
    match l {
        LiteralExpression::DecimalLiteral(d) => {
            print!("{}", d.value.value);
            if !IS_BLK {
                match d.suffix {
                    Some(DecimalSuffix::U8(_)) => { print!(" <U8>") }
                    Some(DecimalSuffix::U16(_)) => { print!(" <U16>") }
                    Some(DecimalSuffix::U32(_)) => { print!(" <U32>") }
                    Some(DecimalSuffix::U64(_)) => { print!(" <U64>") }
                    Some(DecimalSuffix::Field(_)) => { print!(" <Field>") }
                    _ => { print!(" <Undef>") }
                }
            }
        }
        LiteralExpression::BooleanLiteral(b) => {
            print!("{}", b.value)
        }
        LiteralExpression::HexLiteral(h) => {
            match &h.value {
                HexNumberExpression::U8(u) => { print!("{} <U8>", u.value) }
                HexNumberExpression::U16(u) => { print!("{} <U16>", u.value) }
                HexNumberExpression::U32(u) => { print!("{} <U32>", u.value) }
                HexNumberExpression::U64(u) => { print!("{} <U64>", u.value) }
            }
        }
    }
}

fn pretty_arrayaccess(a: &ArrayAccess) {
    print!("[");
    match &a.expression {
        RangeOrExpression::Expression(e) => pretty_expr::<false>(&e),
        _ => print!("range")
    }
    print!("]");
}