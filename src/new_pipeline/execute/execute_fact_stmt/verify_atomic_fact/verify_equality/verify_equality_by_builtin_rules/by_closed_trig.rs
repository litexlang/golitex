//! Closed trigonometric special values and Pythagorean identity.
//!
//! One matcher ↔ one dedicated proof struct.

use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::{
    Add, ArithmeticOperator, Cos, Cot, Literal, Number, Obj, Pow, Sin, Tan, TrigOperator,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::objs_equal_by_rational_expression_evaluation;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

use super::by_inverse_trig::{half_pi, pi_obj, zero_obj};

// Builtin SinOfZero: sin(0) = 0.
pub struct SinOfZeroBuiltinRuleProof {}

// Builtin CosOfZero: cos(0) = 1.
pub struct CosOfZeroBuiltinRuleProof {}

// Builtin TanOfZero: tan(0) = 0.
pub struct TanOfZeroBuiltinRuleProof {}

// Builtin SinOfHalfPi: sin(pi / 2) = 1.
pub struct SinOfHalfPiBuiltinRuleProof {}

// Builtin CosOfPi: cos(pi) = -1.
pub struct CosOfPiBuiltinRuleProof {}

// Builtin SinOfPi: sin(pi) = 0.
pub struct SinOfPiBuiltinRuleProof {}

// Builtin CotOfHalfPi: cot(pi / 2) = 0.
pub struct CotOfHalfPiBuiltinRuleProof {}

// Builtin PythagoreanIdentity: sin(x)^2 + cos(x)^2 = 1.
// Example: have x R; sin(x)^2 + cos(x)^2 = 1.
pub struct PythagoreanIdentityBuiltinRuleProof {}

pub enum ClosedTrigEqualityBuiltinRuleProof {
    SinOfZero(SinOfZeroBuiltinRuleProof),
    CosOfZero(CosOfZeroBuiltinRuleProof),
    TanOfZero(TanOfZeroBuiltinRuleProof),
    SinOfHalfPi(SinOfHalfPiBuiltinRuleProof),
    CosOfPi(CosOfPiBuiltinRuleProof),
    SinOfPi(SinOfPiBuiltinRuleProof),
    CotOfHalfPi(CotOfHalfPiBuiltinRuleProof),
    PythagoreanIdentity(PythagoreanIdentityBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_closed_trig(
        &mut self,
        fact: &EqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<ClosedTrigEqualityBuiltinRuleProof>> {
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if sin_of_zero_shape(left, right) {
                return Ok(Some(ClosedTrigEqualityBuiltinRuleProof::SinOfZero(
                    SinOfZeroBuiltinRuleProof {},
                )));
            }
            if cos_of_zero_shape(left, right) {
                return Ok(Some(ClosedTrigEqualityBuiltinRuleProof::CosOfZero(
                    CosOfZeroBuiltinRuleProof {},
                )));
            }
            if tan_of_zero_shape(left, right) {
                return Ok(Some(ClosedTrigEqualityBuiltinRuleProof::TanOfZero(
                    TanOfZeroBuiltinRuleProof {},
                )));
            }
            if sin_of_half_pi_shape(left, right) {
                return Ok(Some(ClosedTrigEqualityBuiltinRuleProof::SinOfHalfPi(
                    SinOfHalfPiBuiltinRuleProof {},
                )));
            }
            if cos_of_pi_shape(left, right) {
                return Ok(Some(ClosedTrigEqualityBuiltinRuleProof::CosOfPi(
                    CosOfPiBuiltinRuleProof {},
                )));
            }
            if sin_of_pi_shape(left, right) {
                return Ok(Some(ClosedTrigEqualityBuiltinRuleProof::SinOfPi(
                    SinOfPiBuiltinRuleProof {},
                )));
            }
            if cot_of_half_pi_shape(left, right) {
                return Ok(Some(ClosedTrigEqualityBuiltinRuleProof::CotOfHalfPi(
                    CotOfHalfPiBuiltinRuleProof {},
                )));
            }
            if pythagorean_identity_shape(left, right) {
                return Ok(Some(
                    ClosedTrigEqualityBuiltinRuleProof::PythagoreanIdentity(
                        PythagoreanIdentityBuiltinRuleProof {},
                    ),
                ));
            }
        }
        Ok(None)
    }
}

fn is_zero(obj: &Obj) -> bool {
    objs_equal_by_rational_expression_evaluation(obj, &zero_obj())
}

fn is_one(obj: &Obj) -> bool {
    objs_equal_by_rational_expression_evaluation(
        obj,
        &Obj::Literal(Literal::Number(Number {
            normalized_value: "1".to_string(),
        })),
    )
}

fn is_neg_one(obj: &Obj) -> bool {
    objs_equal_by_rational_expression_evaluation(
        obj,
        &Obj::Literal(Literal::Number(Number {
            normalized_value: "-1".to_string(),
        })),
    )
}

fn is_pi(obj: &Obj) -> bool {
    matches!(obj, Obj::Literal(Literal::Pi(_)))
        || objs_equal_by_rational_expression_evaluation(obj, &pi_obj())
}

fn is_half_pi(obj: &Obj) -> bool {
    objs_equal_by_rational_expression_evaluation(obj, &half_pi())
}

fn sin_of_zero_shape(left: &Obj, right: &Obj) -> bool {
    matches!(
        left,
        Obj::TrigOperator(TrigOperator::Sin(Sin { arg })) if is_zero(arg.as_ref())
    ) && is_zero(right)
}

fn cos_of_zero_shape(left: &Obj, right: &Obj) -> bool {
    matches!(
        left,
        Obj::TrigOperator(TrigOperator::Cos(Cos { arg })) if is_zero(arg.as_ref())
    ) && is_one(right)
}

fn tan_of_zero_shape(left: &Obj, right: &Obj) -> bool {
    matches!(
        left,
        Obj::TrigOperator(TrigOperator::Tan(Tan { arg })) if is_zero(arg.as_ref())
    ) && is_zero(right)
}

fn sin_of_half_pi_shape(left: &Obj, right: &Obj) -> bool {
    matches!(
        left,
        Obj::TrigOperator(TrigOperator::Sin(Sin { arg })) if is_half_pi(arg.as_ref())
    ) && is_one(right)
}

fn cos_of_pi_shape(left: &Obj, right: &Obj) -> bool {
    matches!(
        left,
        Obj::TrigOperator(TrigOperator::Cos(Cos { arg })) if is_pi(arg.as_ref())
    ) && is_neg_one(right)
}

fn sin_of_pi_shape(left: &Obj, right: &Obj) -> bool {
    matches!(
        left,
        Obj::TrigOperator(TrigOperator::Sin(Sin { arg })) if is_pi(arg.as_ref())
    ) && is_zero(right)
}

fn cot_of_half_pi_shape(left: &Obj, right: &Obj) -> bool {
    matches!(
        left,
        Obj::TrigOperator(TrigOperator::Cot(Cot { arg })) if is_half_pi(arg.as_ref())
    ) && is_zero(right)
}

fn square_of_trig(obj: &Obj) -> Option<(&Obj, bool)> {
    // sin(x)^2 or cos(x)^2 as Pow(_, 2)
    let Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base, exponent })) = obj else {
        return None;
    };
    if !is_number_two(exponent.as_ref()) {
        return None;
    }
    match base.as_ref() {
        Obj::TrigOperator(TrigOperator::Sin(Sin { arg })) => Some((arg.as_ref(), true)),
        Obj::TrigOperator(TrigOperator::Cos(Cos { arg })) => Some((arg.as_ref(), false)),
        _ => None,
    }
}

fn is_number_two(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "2"
    )
}

fn pythagorean_identity_shape(sum_side: &Obj, one_side: &Obj) -> bool {
    if !is_one(one_side) {
        return false;
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) = sum_side else {
        return false;
    };
    let Some((arg_l, is_sin_l)) = square_of_trig(left.as_ref()) else {
        return false;
    };
    let Some((arg_r, is_sin_r)) = square_of_trig(right.as_ref()) else {
        return false;
    };
    if arg_l.ir() != arg_r.ir() {
        return false;
    }
    is_sin_l != is_sin_r
}