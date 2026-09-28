use crate::new_pipeline::ast::obj::{Literal, Obj};
use crate::new_pipeline::rational_expression::exact_rational::evaluate_obj_to_exact_rational_obj_for_eval;
use crate::new_pipeline::rational_expression::evaluate_obj_to_normalized_decimal_number;
use crate::new_pipeline::rational_expression::ClosedNumericExpr;

// Residual must already classify as ClosedNumericExpr.
// Prefer exact rational (keeps fractions); else normalized decimal Number.
// Example: `1/2` → `1/2`; `abs(-3)` → `3`.
pub fn evaluate_closed_numeric_obj(obj: &Obj) -> Option<Obj> {
    if ClosedNumericExpr::try_from_obj(obj).is_none() {
        return None;
    }
    if let Some(exact) = evaluate_obj_to_exact_rational_obj_for_eval(obj) {
        return Some(exact);
    }
    evaluate_obj_to_normalized_decimal_number(obj).map(|number| Obj::Literal(Literal::Number(number)))
}
