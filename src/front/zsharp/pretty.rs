use zokrates_pest_ast as ast;

pub fn pretty_stmt(indent: usize, s: &ast::Statement) {
    for _ in 0..indent * 4 {
        print!(" ");
    }
    match s {
        ast::Statement::Return(r) => { pretty_ret_stmt(r); }
        ast::Statement::Definition(d) => { pretty_def_stmt(d); }
        ast::Statement::Assertion(a) => { pretty_ass_stmt(a); }
        ast::Statement::Iteration(i) => { pretty_ite_stmt(indent, i); }
    }
}

fn pretty_ret_stmt(r: &ast::ReturnStatement) {
    print!("return ");
    pretty_expr(&r.expressions[0]);
    for e in &r.expressions[1..] {
        print!(", ");
        pretty_expr(e);
    }
    println!("");
}

fn pretty_def_stmt(d: &ast::DefinitionStatement) {
    match &d.lhs[0] {
        ast::TypedIdentifierOrAssignee::Assignee(a) => { pretty_ident_expr(&a.id); }
        ast::TypedIdentifierOrAssignee::TypedIdentifier(ti) => pretty_typed_ident(&ti)
    }
    for l in &d.lhs[1..] {
        print!(", ");
        match l {
            ast::TypedIdentifierOrAssignee::Assignee(a) => { pretty_ident_expr(&a.id); }
            ast::TypedIdentifierOrAssignee::TypedIdentifier(ti) => { pretty_typed_ident(&ti); }
        }        
    }
    print!(" = ");
    pretty_expr(&d.expression);
    println!("");
}

fn pretty_ass_stmt(a: &ast::AssertionStatement) {
    print!("assert ");
    pretty_expr(&a.expression);
    println!("");
}

fn pretty_ite_stmt(indent: usize, i: &ast::IterationStatement) {
    print!("for ");
    pretty_type(&i.ty);
    print!(" ");
    pretty_ident_expr(&i.index);
    print!(" in ");
    pretty_expr(&i.from);
    print!(" .. ");
    pretty_expr(&i.to);
    println!(":");
    for s in &i.statements {
        pretty_stmt(indent + 1, &s);
    }
}

fn pretty_typed_ident(ti: &ast::TypedIdentifier) {
    pretty_type(&ti.ty);
    print!(" ");
    pretty_ident_expr(&ti.identifier);
}

fn pretty_type(ty: &ast::Type) {
    match ty {
        ast::Type::Basic(ast::BasicType::Field(_)) => { print!("field"); }
        ast::Type::Basic(ast::BasicType::Boolean(_)) => { print!("bool"); }
        ast::Type::Basic(ast::BasicType::U8(_)) => { print!("u8"); }
        ast::Type::Basic(ast::BasicType::U16(_)) => { print!("u16"); }
        ast::Type::Basic(ast::BasicType::U32(_)) => { print!("u32"); }
        ast::Type::Basic(ast::BasicType::U64(_)) => { print!("u64"); }
        ast::Type::Struct(_) => { print!("struct"); }
        ast::Type::Array(_) => { print!("array"); }
    }
}

pub fn pretty_expr(e: &ast::Expression) {
    match e {
        ast::Expression::Ternary(t) => { 
            pretty_expr(&t.first);
            print!(" ? ");
            pretty_expr(&t.second);
            print!(" : ");
            pretty_expr(&t.third);
        }
        ast::Expression::Binary(b) => {
            pretty_expr(&b.left);
            print!(" {} ", get_bin_op(&b.op));
            pretty_expr(&b.right);
        }
        ast::Expression::Unary(u) => {
            print!("{}", get_un_op(&u.op));
            pretty_expr(&u.expression);
        }
        ast::Expression::Identifier(i) => { pretty_ident_expr(i); }
        ast::Expression::Literal(l) => { pretty_literal(l); }
        _ => {
            panic!("Pretty print for expression yet to be implemented.");
        }
    }
}

fn pretty_ident_expr(i: &ast::IdentifierExpression) {
    print!("{}", i.value);
}

fn get_un_op(op: &ast::UnaryOperator) -> String {
    panic!("Pretty print for unary operators has yet to be implemented.");
}

fn get_bin_op(op: &ast::BinaryOperator) -> &str {
    match op {
        ast::BinaryOperator::BitXor => { "^" }
        ast::BinaryOperator::BitAnd => { "&" }
        ast::BinaryOperator::BitOr => { "|" }
        ast::BinaryOperator::RightShift => { ">>" }
        ast::BinaryOperator::LeftShift => { "<<" }
        ast::BinaryOperator::Or => { "||" }
        ast::BinaryOperator::And => { "&&" }
        ast::BinaryOperator::Add => { "+" }
        ast::BinaryOperator::Sub => { "-" }
        ast::BinaryOperator::Mul => { "*" }
        ast::BinaryOperator::Div => { "/" }
        ast::BinaryOperator::Rem => { "%" }
        ast::BinaryOperator::Eq => { "==" }
        ast::BinaryOperator::NotEq => { "!=" }
        ast::BinaryOperator::Lt => { "<" }
        ast::BinaryOperator::Gt => { ">" }
        ast::BinaryOperator::Lte => { "<=" }
        ast::BinaryOperator::Gte => { ">=" }
        ast::BinaryOperator::Pow => { "**" }
    }
}

fn pretty_literal(l: &ast::LiteralExpression) {
    match l {
        ast::LiteralExpression::DecimalLiteral(d) => {
            print!("{}", d.value.span.as_str())
        }
        ast::LiteralExpression::BooleanLiteral(b) => {
            print!("{}", b.value)
        }
        ast::LiteralExpression::HexLiteral(h) => {
            match &h.value {
                ast::HexNumberExpression::U8(u) => { print!("{}", u.value) }
                ast::HexNumberExpression::U16(u) => { print!("{}", u.value) }
                ast::HexNumberExpression::U32(u) => { print!("{}", u.value) }
                ast::HexNumberExpression::U64(u) => { print!("{}", u.value) }
            }
        }
    }
}