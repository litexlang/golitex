use crate::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::ast::obj::{
    Add, ArithmeticOperator, Div, Literal, Mul, Number, Obj, Sub,
};
use crate::rational_expression::evaluate_obj_to_normalized_decimal_number;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{
    InferEqualFactSimpleLinearSolvedValueResult, StoreFactAndInferResult,
};

impl Runtime {
    // When: stored equality has shape `x ± c = d`, `c ± x = d`, `x * c = d`,
    // `c * x = d`, `x / c = d`, or `c / x = d` with c,d closed numeric and x not.
    // Infers: the unique solved value `x = ...` as a closed numeric equality.
    // Example: store `x + 4 = 2` ⇒ infer `x = -2`.
    // Non-example: `x^2 = 4` has two real roots and is not solved here.
    pub(super) fn infer_equal_fact_simple_linear_solved_value(
        &mut self,
        equal_fact: &EqualFact,
    ) -> RuntimeResult<Option<InferEqualFactSimpleLinearSolvedValueResult>> {
        let Some((unknown, value)) = simple_linear_solved_unknown_and_value(equal_fact) else {
            return Ok(None);
        };
        if unknown.ir() == value.ir() {
            return Ok(None);
        }
        let solved = AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: unknown,
            right: value,
            line_file: equal_fact.line_file.clone(),
        });
        let Some(stored) =
            self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(solved))?
        else {
            return Ok(None);
        };
        Ok(Some(InferEqualFactSimpleLinearSolvedValueResult {
            derived: vec![stored],
        }))
    }
}

fn simple_linear_solved_unknown_and_value(equal_fact: &EqualFact) -> Option<(Obj, Obj)> {
    try_solve_linear_side(&equal_fact.left, &equal_fact.right)
        .or_else(|| try_solve_linear_side(&equal_fact.right, &equal_fact.left))
}

fn try_solve_linear_side(expr: &Obj, other: &Obj) -> Option<(Obj, Obj)> {
    let other_value = evaluate_obj_to_normalized_decimal_number(other)?;
    let other_lit = number_obj(other_value);
    match expr {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) => {
            if let Some(unknown) = unknown_with_closed(left.as_ref(), right.as_ref()) {
                // unknown + c = other ⇒ unknown = other - c
                return solved_sub(&other_lit, right.as_ref()).map(|v| (unknown, v));
            }
            if let Some(unknown) = unknown_with_closed(right.as_ref(), left.as_ref()) {
                // c + unknown = other ⇒ unknown = other - c
                return solved_sub(&other_lit, left.as_ref()).map(|v| (unknown, v));
            }
            None
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })) => {
            if let Some(unknown) = unknown_with_closed(left.as_ref(), right.as_ref()) {
                // unknown - c = other ⇒ unknown = other + c
                return solved_add(&other_lit, right.as_ref()).map(|v| (unknown, v));
            }
            if let Some(unknown) = unknown_with_closed(right.as_ref(), left.as_ref()) {
                // c - unknown = other ⇒ unknown = c - other
                return solved_sub(left.as_ref(), &other_lit).map(|v| (unknown, v));
            }
            None
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) => {
            if let Some(unknown) = unknown_with_closed(left.as_ref(), right.as_ref()) {
                // unknown * c = other ⇒ unknown = other / c
                return solved_div(&other_lit, right.as_ref()).map(|v| (unknown, v));
            }
            if let Some(unknown) = unknown_with_closed(right.as_ref(), left.as_ref()) {
                // c * unknown = other ⇒ unknown = other / c
                return solved_div(&other_lit, left.as_ref()).map(|v| (unknown, v));
            }
            None
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Div(Div { left, right })) => {
            if let Some(unknown) = unknown_with_closed(left.as_ref(), right.as_ref()) {
                // unknown / c = other ⇒ unknown = other * c
                return solved_mul(&other_lit, right.as_ref()).map(|v| (unknown, v));
            }
            if let Some(unknown) = unknown_with_closed(right.as_ref(), left.as_ref()) {
                // c / unknown = other ⇒ unknown = c / other
                return solved_div(left.as_ref(), &other_lit).map(|v| (unknown, v));
            }
            None
        }
        _ => None,
    }
}

// unknown is not closed numeric; closed_part is closed numeric.
fn unknown_with_closed(unknown: &Obj, closed_part: &Obj) -> Option<Obj> {
    if evaluate_obj_to_normalized_decimal_number(unknown).is_some() {
        return None;
    }
    if evaluate_obj_to_normalized_decimal_number(closed_part).is_none() {
        return None;
    }
    Some(unknown.clone())
}

fn number_obj(n: Number) -> Obj {
    Obj::Literal(Literal::Number(n))
}

fn solved_add(left: &Obj, right: &Obj) -> Option<Obj> {
    let expr = Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: Box::new(left.clone()),
        right: Box::new(right.clone()),
    }));
    evaluate_obj_to_normalized_decimal_number(&expr).map(number_obj)
}

fn solved_sub(left: &Obj, right: &Obj) -> Option<Obj> {
    let expr = Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
        left: Box::new(left.clone()),
        right: Box::new(right.clone()),
    }));
    evaluate_obj_to_normalized_decimal_number(&expr).map(number_obj)
}

fn solved_mul(left: &Obj, right: &Obj) -> Option<Obj> {
    let expr = Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
        left: Box::new(left.clone()),
        right: Box::new(right.clone()),
    }));
    evaluate_obj_to_normalized_decimal_number(&expr).map(number_obj)
}

fn solved_div(left: &Obj, right: &Obj) -> Option<Obj> {
    let expr = Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
        left: Box::new(left.clone()),
        right: Box::new(right.clone()),
    }));
    evaluate_obj_to_normalized_decimal_number(&expr).map(number_obj)
}
