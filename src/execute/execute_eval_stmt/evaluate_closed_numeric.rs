use crate::ast::obj::{Literal, Obj};
use crate::rational_expression::exact_rational::evaluate_obj_to_exact_rational_obj_for_eval;
use crate::rational_expression::evaluate_obj_to_normalized_decimal_number;
use crate::rational_expression::ClosedNumericExpr;

// Residual must already classify as ClosedNumericExpr.
// Prefer exact rational (keeps fractions); else normalized decimal Number.
// Simple: `1/2` → `1/2`; `abs(-3)` → `3`.
// Complex nested: examples/.../eval_closed_numeric_complex.lit
//   e.g. `eval gcd(54, (-24)) + 3! * sqrt(4)`, `eval a + b * c` after closed `have`.
pub fn evaluate_closed_numeric_obj(obj: &Obj) -> Option<Obj> {
    if ClosedNumericExpr::try_from_obj(obj).is_none() {
        return None;
    }
    if let Some(exact) = evaluate_obj_to_exact_rational_obj_for_eval(obj) {
        return Some(exact);
    }
    if let Some(radical) = crate::rational_expression::exact_radical::ExactRadical::from_obj(obj) {
        return Some(radical.to_obj());
    }
    evaluate_obj_to_normalized_decimal_number(obj).map(|number| Obj::Literal(Literal::Number(number)))
}
