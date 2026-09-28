//! Prove flipped order vs 0 after multiplying by (-1).
//!
//! B1 boundary: order flip spelling is verify-time only (not eager infer).
//!
//! When known `x < 0` / `x <= 0`, prove `(-1)*x >= 0`.
//! When known `x > 0`, prove `(-1)*x < 0`.
//! When known `x >= 0` / `x > 0`, prove `(-1)*x <= 0`.

use crate::new_pipeline::ast::fact::{GreaterEqualFact, LessEqualFact, LessFact};
use crate::new_pipeline::ast::obj::{ArithmeticOperator, Literal, Mul, Number, Obj};
use crate::new_pipeline::runtime::{FactId, Runtime};

// Builtin: `(-1)*x >= 0` from known `x < 0` or `x <= 0`.
// Example: trust a < 0; (-1) * a >= 0.
pub struct OrderFlipMulMinusOneToGreaterEqualBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

// Builtin: `(-1)*x < 0` from known `x > 0`.
// Example: trust a > 0; (-1) * a < 0.
pub struct OrderFlipMulMinusOneToLessBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

// Builtin: `(-1)*x <= 0` from known `x >= 0` or `x > 0`.
// Example: trust a >= 0; (-1) * a <= 0.
pub struct OrderFlipMulMinusOneToLessEqualBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

impl Runtime {
    pub(crate) fn try_order_flip_mul_minus_one_to_greater_equal(
        &self,
        fact: &GreaterEqualFact,
    ) -> Option<OrderFlipMulMinusOneToGreaterEqualBuiltinRuleProof> {
        let x = peel_mul_by_literal_neg_one(self, &fact.left)?;
        if !is_literal_zero(&fact.right) {
            return None;
        }
        let zero = literal_zero();
        let cite_fact_id = self
            .known_less_fact_id(&x, &zero)
            .or_else(|| self.known_less_equal_fact_id(&x, &zero))?;
        Some(OrderFlipMulMinusOneToGreaterEqualBuiltinRuleProof { cite_fact_id })
    }

    pub(crate) fn try_order_flip_mul_minus_one_to_less(
        &self,
        fact: &LessFact,
    ) -> Option<OrderFlipMulMinusOneToLessBuiltinRuleProof> {
        let x = peel_mul_by_literal_neg_one(self, &fact.left)?;
        if !is_literal_zero(&fact.right) {
            return None;
        }
        let zero = literal_zero();
        let cite_fact_id = self.known_greater_fact_id(&x, &zero)?;
        Some(OrderFlipMulMinusOneToLessBuiltinRuleProof { cite_fact_id })
    }

    pub(crate) fn try_order_flip_mul_minus_one_to_less_equal(
        &self,
        fact: &LessEqualFact,
    ) -> Option<OrderFlipMulMinusOneToLessEqualBuiltinRuleProof> {
        let x = peel_mul_by_literal_neg_one(self, &fact.left)?;
        if !is_literal_zero(&fact.right) {
            return None;
        }
        let zero = literal_zero();
        let cite_fact_id = self
            .known_greater_equal_fact_id(&x, &zero)
            .or_else(|| self.known_greater_fact_id(&x, &zero))?;
        Some(OrderFlipMulMinusOneToLessEqualBuiltinRuleProof { cite_fact_id })
    }
}

fn peel_mul_by_literal_neg_one(runtime: &Runtime, obj: &Obj) -> Option<Obj> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) = obj else {
        return None;
    };
    if is_literal_neg_one(runtime, left.as_ref()) {
        return Some(right.as_ref().clone());
    }
    if is_literal_neg_one(runtime, right.as_ref()) {
        return Some(left.as_ref().clone());
    }
    None
}

fn is_literal_neg_one(runtime: &Runtime, obj: &Obj) -> bool {
    runtime
        .resolve_obj_to_normalized_number(obj)
        .map(|n| n == "-1")
        .unwrap_or(false)
}

fn is_literal_zero(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "0"
    )
}

fn literal_zero() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "0".to_string(),
    }))
}
