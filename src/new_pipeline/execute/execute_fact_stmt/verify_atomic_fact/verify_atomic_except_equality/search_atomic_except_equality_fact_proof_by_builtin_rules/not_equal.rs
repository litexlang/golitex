use crate::new_pipeline::ast::fact::{Fact, NotEqualFact};
use crate::new_pipeline::ast::obj::{Cos, Number, Obj, Sin, Literal, SetFormer, TrigOperator};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_inverse_trig::{
    half_pi, negative_half_pi, pi_obj, zero_obj,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::{
    evaluate_obj_to_normalized_decimal_number, objs_equal_by_rational_expression_evaluation,
};
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};

// Builtin rules for `!=` facts (zero-premise routes).
pub enum NotEqualFactSearchProofByBuiltinRule {
    // Closed decimal evaluation yields unequal normals.
    // Mathematical property: if both sides evaluate to normalized decimals
    // `L` and `R` with `L != R`, then the objects are unequal.
    // Examples: `1 != 0`, `1 + 1 != 3`.
    ClosedDecimal(ClosedDecimalNotEqualBuiltinRuleProof),
    // Not-equal symmetry: prove `a != b` from a proved `b != a`.
    // Example: known `0 != x` proves `x != 0`.
    NotEqualSymmetry(NotEqualSymmetryBuiltinRuleProof),
    // List sets of different lengths are unequal.
    // Example: prove `{1} != {1, 2}`.
    ListSetDifferentLength(ListSetDifferentLengthBuiltinRuleProof),
    // Strict order implies inequality.
    // Mathematical property: `a > b` or `a < b` ⇒ `a != b`.
    // Example: known `x > 0` proves `x != 0`.
    FromKnownStrictOrder(FromKnownStrictOrderBuiltinRuleProof),
    // Cosine is nonzero on the open principal tangent interval.
    // Mathematical property: `-pi/2 < y < pi/2` ⇒ `cos(y) != 0`.
    // Example: after those bounds, prove `cos(y) != 0` for `tan(y)` WD.
    CosNonzeroOnOpenHalfPi(CosNonzeroOnOpenHalfPiBuiltinRuleProof),
    // Sine is nonzero on the open principal cotangent interval.
    // Mathematical property: `0 < y < pi` ⇒ `sin(y) != 0`.
    // Example: after those bounds, prove `sin(y) != 0` for `cot(y)` WD.
    SinNonzeroOnOpenPi(SinNonzeroOnOpenPiBuiltinRuleProof),
}

pub struct ClosedDecimalNotEqualBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

pub struct NotEqualSymmetryBuiltinRuleProof {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}

pub struct ListSetDifferentLengthBuiltinRuleProof {}

pub struct FromKnownStrictOrderBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

pub struct CosNonzeroOnOpenHalfPiBuiltinRuleProof {}
pub struct SinNonzeroOnOpenPiBuiltinRuleProof {}

impl Runtime {
    // Builtin not-equal: closed decimal, known strict order, trig nonzero, then list-set length.
    pub fn search_not_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotEqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        if let (Some(left), Some(right)) = (
            evaluate_obj_to_normalized_decimal_number(&fact.left),
            evaluate_obj_to_normalized_decimal_number(&fact.right),
        ) {
            if left.normalized_value != right.normalized_value {
                return Ok(Some(NotEqualFactSearchProofByBuiltinRule::ClosedDecimal(
                    ClosedDecimalNotEqualBuiltinRuleProof {
                        left_normal: left.normalized_value,
                        right_normal: right.normalized_value,
                    },
                )));
            }
        }
        if let Some(cite_fact_id) = self
            .known_greater_fact_id(&fact.left, &fact.right)
            .or_else(|| self.known_less_fact_id(&fact.left, &fact.right))
        {
            return Ok(Some(
                NotEqualFactSearchProofByBuiltinRule::FromKnownStrictOrder(
                    FromKnownStrictOrderBuiltinRuleProof { cite_fact_id },
                ),
            ));
        }
        if let Some(proof) = self.cos_nonzero_on_open_half_pi_proof(fact) {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.sin_nonzero_on_open_pi_proof(fact) {
            return Ok(Some(proof));
        }
        if let (Obj::SetFormer(SetFormer::ListSet(left)), Obj::SetFormer(SetFormer::ListSet(right))) = (&fact.left, &fact.right) {
            if left.list.len() != right.list.len() {
                return Ok(Some(
                    NotEqualFactSearchProofByBuiltinRule::ListSetDifferentLength(
                        ListSetDifferentLengthBuiltinRuleProof {},
                    ),
                ));
            }
        }
        Ok(None)
    }

    fn cos_nonzero_on_open_half_pi_proof(
        &self,
        fact: &NotEqualFact,
    ) -> Option<NotEqualFactSearchProofByBuiltinRule> {
        let arg = cos_arg_against_zero(fact)?;
        let lower = negative_half_pi();
        let upper = half_pi();
        if self.known_less_fact_id(&lower, arg).is_none() {
            return None;
        }
        if self.known_less_fact_id(arg, &upper).is_none() {
            return None;
        }
        Some(NotEqualFactSearchProofByBuiltinRule::CosNonzeroOnOpenHalfPi(
            CosNonzeroOnOpenHalfPiBuiltinRuleProof {},
        ))
    }

    fn sin_nonzero_on_open_pi_proof(
        &self,
        fact: &NotEqualFact,
    ) -> Option<NotEqualFactSearchProofByBuiltinRule> {
        let arg = sin_arg_against_zero(fact)?;
        let lower = zero_obj();
        let upper = pi_obj();
        if self.known_less_fact_id(&lower, arg).is_none() {
            return None;
        }
        if self.known_less_fact_id(arg, &upper).is_none() {
            return None;
        }
        Some(NotEqualFactSearchProofByBuiltinRule::SinNonzeroOnOpenPi(
            SinNonzeroOnOpenPiBuiltinRuleProof {},
        ))
    }
}

fn cos_arg_against_zero(fact: &NotEqualFact) -> Option<&Obj> {
    match (&fact.left, &fact.right) {
        (Obj::TrigOperator(TrigOperator::Cos(Cos { arg })), right) if is_zero_obj(right) => Some(arg.as_ref()),
        (left, Obj::TrigOperator(TrigOperator::Cos(Cos { arg }))) if is_zero_obj(left) => Some(arg.as_ref()),
        _ => None,
    }
}

fn sin_arg_against_zero(fact: &NotEqualFact) -> Option<&Obj> {
    match (&fact.left, &fact.right) {
        (Obj::TrigOperator(TrigOperator::Sin(Sin { arg })), right) if is_zero_obj(right) => Some(arg.as_ref()),
        (left, Obj::TrigOperator(TrigOperator::Sin(Sin { arg }))) if is_zero_obj(left) => Some(arg.as_ref()),
        _ => None,
    }
}

fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number {
            normalized_value,
        })) if normalized_value == "0"
    ) || objs_equal_by_rational_expression_evaluation(obj, &zero_obj())
}
