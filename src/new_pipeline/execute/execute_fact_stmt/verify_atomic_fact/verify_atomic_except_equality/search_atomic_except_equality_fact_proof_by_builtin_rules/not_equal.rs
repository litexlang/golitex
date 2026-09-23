use crate::new_pipeline::ast::fact::{AtomicFact, Fact, NotEqualFact};
use crate::new_pipeline::ast::obj::{
    Abs, ArithmeticOperator, Cos, Literal, Number, Obj, SetFormer, Sin, Sub, TrigOperator,
};
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
    // Absolute value is nonzero when the argument is nonzero.
    // Mathematical property: `x != 0` ⇒ `abs(x) != 0`.
    // Example: known `x != 0` proves `abs(x) != 0`.
    AbsNonzeroFromArg(AbsNonzeroFromArgBuiltinRuleProof),
    // Difference is nonzero when the operands are unequal.
    // Mathematical property: `a != b` ⇒ `a - b != 0`.
    // Example: known `x != y` proves `x - y != 0`.
    DiffNonzeroFromInequality(DiffNonzeroFromInequalityBuiltinRuleProof),
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

pub struct AbsNonzeroFromArgBuiltinRuleProof {
    pub arg_nonzero_proof: VerifyFactResult,
}

pub struct DiffNonzeroFromInequalityBuiltinRuleProof {
    pub operands_unequal_proof: VerifyFactResult,
}

impl Runtime {
    // Builtin search for `a != b`.
    // B0: closed decimal + known strict order. A: match Obj shapes. B1: none.
    // Example: prove `1 != 0`, `x != 0` from `x > 0`, `{1} != {1, 2}`, `cos(y) != 0`.
    pub fn search_not_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        // B0 — non-shape
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

        // A — shape
        match (&fact.left, &fact.right) {
            (
                Obj::SetFormer(SetFormer::ListSet(left)),
                Obj::SetFormer(SetFormer::ListSet(right)),
            ) if left.list.len() != right.list.len() => {
                return Ok(Some(
                    NotEqualFactSearchProofByBuiltinRule::ListSetDifferentLength(
                        ListSetDifferentLengthBuiltinRuleProof {},
                    ),
                ));
            }

            (Obj::TrigOperator(TrigOperator::Cos(Cos { arg })), right)
                if is_zero_obj(right) =>
            {
                if let Some(proof) = self.cos_nonzero_on_open_half_pi_for_arg(arg.as_ref()) {
                    return Ok(Some(proof));
                }
            }
            (left, Obj::TrigOperator(TrigOperator::Cos(Cos { arg })))
                if is_zero_obj(left) =>
            {
                if let Some(proof) = self.cos_nonzero_on_open_half_pi_for_arg(arg.as_ref()) {
                    return Ok(Some(proof));
                }
            }

            (Obj::TrigOperator(TrigOperator::Sin(Sin { arg })), right)
                if is_zero_obj(right) =>
            {
                if let Some(proof) = self.sin_nonzero_on_open_pi_for_arg(arg.as_ref()) {
                    return Ok(Some(proof));
                }
            }
            (left, Obj::TrigOperator(TrigOperator::Sin(Sin { arg })))
                if is_zero_obj(left) =>
            {
                if let Some(proof) = self.sin_nonzero_on_open_pi_for_arg(arg.as_ref()) {
                    return Ok(Some(proof));
                }
            }

            // `abs(x) != 0` from `x != 0`
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })),
                right,
            ) if is_zero_obj(right) => {
                if let Some(proof) =
                    self.abs_nonzero_from_arg_proof(arg.as_ref(), verify_state.clone())?
                {
                    return Ok(Some(proof));
                }
            }
            (
                left,
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })),
            ) if is_zero_obj(left) => {
                if let Some(proof) =
                    self.abs_nonzero_from_arg_proof(arg.as_ref(), verify_state.clone())?
                {
                    return Ok(Some(proof));
                }
            }

            // `a - b != 0` from `a != b`
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })),
                zero,
            ) if is_zero_obj(zero) => {
                if let Some(proof) = self.diff_nonzero_from_inequality_proof(
                    left.as_ref(),
                    right.as_ref(),
                    verify_state.clone(),
                )? {
                    return Ok(Some(proof));
                }
            }
            (
                zero,
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })),
            ) if is_zero_obj(zero) => {
                if let Some(proof) = self.diff_nonzero_from_inequality_proof(
                    left.as_ref(),
                    right.as_ref(),
                    verify_state,
                )? {
                    return Ok(Some(proof));
                }
            }

            _ => {}
        }

        Ok(None)
    }

    fn abs_nonzero_from_arg_proof(
        &mut self,
        arg: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        let goal = Fact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: arg.clone(),
            right: zero_obj(),
            line_file: None,
        }));
        let arg_nonzero_proof = self.verify_fact(&goal, verify_state)?;
        if arg_nonzero_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(NotEqualFactSearchProofByBuiltinRule::AbsNonzeroFromArg(
            AbsNonzeroFromArgBuiltinRuleProof { arg_nonzero_proof },
        )))
    }

    fn diff_nonzero_from_inequality_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        let goal = Fact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        }));
        let operands_unequal_proof = self.verify_fact(&goal, verify_state)?;
        if operands_unequal_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            NotEqualFactSearchProofByBuiltinRule::DiffNonzeroFromInequality(
                DiffNonzeroFromInequalityBuiltinRuleProof {
                    operands_unequal_proof,
                },
            ),
        ))
    }

    fn cos_nonzero_on_open_half_pi_for_arg(
        &self,
        arg: &Obj,
    ) -> Option<NotEqualFactSearchProofByBuiltinRule> {
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

    fn sin_nonzero_on_open_pi_for_arg(
        &self,
        arg: &Obj,
    ) -> Option<NotEqualFactSearchProofByBuiltinRule> {
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

fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number {
            normalized_value,
        })) if normalized_value == "0"
    ) || objs_equal_by_rational_expression_evaluation(obj, &zero_obj())
}
