//! Operator UniqDeriGcd
//!
//! Given an array of (root, cond) tuples (root is a field element, cond is a boolean),
//! define f(X) = prod_i (cond_i ? X - root_i : 1)
//!
//! Compute f'(X) and s,t s.t. fs + f't = 1. Return an array of coefficients for s and one for t
//! (as a tuple).

use crate::ir::term::{ty::*, *};

/// Type-check [super::ExtOp::UniqDeriGcd].
pub fn check(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    if let &[pairs] = arg_sorts {
        let (key, value, size) = ty::array_or(pairs, "UniqDeriGcd pairs")?;
        let f = pf_or(key, "UniqDeriGcd pairs: indices must be field")?;
        let value_tup = ty::tuple_or(value, "UniqDeriGcd entries: value must be a tuple")?;
        if let &[root, cond] = &value_tup {
            eq_or(f, root, "UniqDeriGcd pairs: first element must be a field")?;
            eq_or(
                cond,
                &Sort::Bool,
                "UniqDeriGcd pairs: second element must be a bool",
            )?;
            let box_f = Box::new(f.clone());
            let arr = Sort::Array(box_f.clone(), box_f, size);
            Ok(Sort::Tuple(Box::new([arr.clone(), arr])))
        } else {
            // non-pair entries value
            Err(TypeErrorReason::Custom(
                "UniqDeriGcd: pairs value must be a pair".into(),
            ))
        }
    } else {
        // wrong arg count
        Err(TypeErrorReason::ExpectedArgs(2, arg_sorts.len()))
    }
}

/// Evaluate [super::ExtOp::UniqDeriGcd].
pub fn eval(_args: &[&Value]) -> Value {
    panic!("Cannot evalute Op::UniqDeriGcd without 'poly' feature")
}
