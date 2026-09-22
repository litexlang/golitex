//! Match `x - 1` surfaces used by natural-predecessor builtins.

use crate::new_pipeline::ast::obj::{Number, Obj, Sub, ArithmeticOperator, Literal};

// `obj` is exactly `base - 1` (normalized decimal one).
pub(crate) fn match_sub_one<'a>(obj: &'a Obj) -> Option<&'a Obj> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })) = obj else {
        return None;
    };
    if !is_number_value(right.as_ref(), "1") {
        return None;
    }
    Some(left.as_ref())
}

pub(crate) fn is_number_value(obj: &Obj, value: &str) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number {
            normalized_value,
        })) if normalized_value == value
    )
}
