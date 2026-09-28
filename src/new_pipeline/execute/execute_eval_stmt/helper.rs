use crate::new_pipeline::ast::obj::{Literal, Obj};
use crate::new_pipeline::rational_expression::exact_rational::evaluate_obj_to_exact_rational_obj_for_eval;
use crate::new_pipeline::rational_expression::evaluate_obj_to_normalized_decimal_number;

// Prefer exact rational (keeps fractions); fall back to closed decimal.
// Example: `1/2` → `1/2`; `2!` → `2`.
pub fn evaluate_obj_for_eval_stmt(obj: &Obj) -> Option<Obj> {
    if let Some(exact) = evaluate_obj_to_exact_rational_obj_for_eval(obj) {
        return Some(exact);
    }
    evaluate_obj_to_normalized_decimal_number(obj).map(|number| Obj::Literal(Literal::Number(number)))
}
