use crate::new_pipeline::ast::fact::{AtomicFact, Fact, LessFact};
use crate::new_pipeline::ast::obj::{Add, ArithmeticOperator, Mul, Obj, Sub, TrigOperator};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::{is_zero_obj, zero_obj};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::predecessor_helpers::is_number_value;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::trig_bounds::{
    match_arccot_principal_lower, match_arccot_principal_upper, match_arctan_principal_lower,
    match_arctan_principal_upper,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::{
    compare_closed_objs_by_normalized_decimal, NumberCompareResult,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin rules for `a < b`.
pub enum LessFactSearchProofByBuiltinRule {
    // Closed numeric comparison by evaluation.
    // Mathematical property: if both sides evaluate to decimals L, R with L < R,
    // then `left < right`.
    // Examples: `1 < 2`, `1 + 1 < 5`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
    // Subtract-one is strictly below the minuend.
    // Mathematical property: for any object `x`, `x - 1 < x`.
    // Example: prove `n - 1 < n` (used by inductive recursive domain checks).
    SubtractOneLess(SubtractOneLessBuiltinRuleProof),
    // Arctan principal lower bound: `-pi/2 < arctan(x)`.
    // Example: prove `-pi / 2 < arctan(x)`.
    ArctanPrincipalLowerBound(ArctanPrincipalLowerBoundBuiltinRuleProof),
    // Arctan principal upper bound: `arctan(x) < pi/2`.
    // Example: prove `arctan(x) < pi / 2`.
    ArctanPrincipalUpperBound(ArctanPrincipalUpperBoundBuiltinRuleProof),
    // Arccot principal lower bound: `0 < arccot(x)` (range (0, pi)).
    // Example: prove `0 < arccot(x)`.
    ArccotPrincipalLowerBound(ArccotPrincipalLowerBoundBuiltinRuleProof),
    // Arccot principal upper bound: `arccot(x) < pi`.
    // Example: prove `arccot(x) < pi`.
    ArccotPrincipalUpperBound(ArccotPrincipalUpperBoundBuiltinRuleProof),
    // Sum of positives: `0 < a` and `0 < b` ⇒ `0 < a + b`.
    // Example: known `0 < x`, `0 < y` prove `0 < x + y`.
    SumBothPositive(SumBothPositiveBuiltinRuleProof),
    // Mixed sum positivity (left strict): `0 < a` and `0 <= b` ⇒ `0 < a + b`.
    // Example: known `0 < x`, `0 <= y` prove `0 < x + y`.
    SumLeftStrictRightNonnegative(SumLeftStrictRightNonnegativeBuiltinRuleProof),
    // Mixed sum positivity (right strict): `0 <= a` and `0 < b` ⇒ `0 < a + b`.
    SumLeftNonnegativeRightStrict(SumLeftNonnegativeRightStrictBuiltinRuleProof),
    // Product of positives: `0 < a` and `0 < b` ⇒ `0 < a * b`.
    // Example: known `0 < x`, `0 < y` prove `0 < x * y`.
    ProductBothPositive(ProductBothPositiveBuiltinRuleProof),
}

// Payload: both evaluated normals with left_normal < right_normal.
pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

// Payload: the minuend `x` in the goal `x - 1 < x`.
pub struct SubtractOneLessBuiltinRuleProof {
    pub minuend: Obj,
}

pub struct ArctanPrincipalLowerBoundBuiltinRuleProof {}
pub struct ArctanPrincipalUpperBoundBuiltinRuleProof {}
pub struct ArccotPrincipalLowerBoundBuiltinRuleProof {}
pub struct ArccotPrincipalUpperBoundBuiltinRuleProof {}

pub struct SumBothPositiveBuiltinRuleProof {
    pub left_positive_proof: VerifyFactResult,
    pub right_positive_proof: VerifyFactResult,
}

pub struct SumLeftStrictRightNonnegativeBuiltinRuleProof {
    pub left_positive_proof: VerifyFactResult,
    pub right_nonnegative_proof: VerifyFactResult,
}

pub struct SumLeftNonnegativeRightStrictBuiltinRuleProof {
    pub left_nonnegative_proof: VerifyFactResult,
    pub right_positive_proof: VerifyFactResult,
}

pub struct ProductBothPositiveBuiltinRuleProof {
    pub left_positive_proof: VerifyFactResult,
    pub right_positive_proof: VerifyFactResult,
}

impl Runtime {
    // Builtin search for `a < b`.
    // B0: none (no known-cite / reflexivity for strict < here).
    // A: match on Obj shapes of (left, right).
    // B1: closed decimal evaluation.
    // Example: prove `n - 1 < n`, `-pi/2 < arctan(x)`, or `1 < 2`.
    pub fn search_less_fact_proof_by_builtin_rule(
        &mut self,
        fact: &LessFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        match (&fact.left, &fact.right) {
            // `x - 1 < x`
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })),
                minuend,
            ) if is_number_value(right.as_ref(), "1") && left.as_ref().ir() == minuend.ir() => {
                return Ok(Some(LessFactSearchProofByBuiltinRule::SubtractOneLess(
                    SubtractOneLessBuiltinRuleProof {
                        minuend: left.as_ref().clone(),
                    },
                )));
            }

            // `-pi/2 < arctan(x)`
            (_, Obj::TrigOperator(TrigOperator::Arctan(_)))
                if match_arctan_principal_lower(&fact.left, &fact.right) =>
            {
                return Ok(Some(
                    LessFactSearchProofByBuiltinRule::ArctanPrincipalLowerBound(
                        ArctanPrincipalLowerBoundBuiltinRuleProof {},
                    ),
                ));
            }

            // `arctan(x) < pi/2`
            (Obj::TrigOperator(TrigOperator::Arctan(_)), _)
                if match_arctan_principal_upper(&fact.left, &fact.right) =>
            {
                return Ok(Some(
                    LessFactSearchProofByBuiltinRule::ArctanPrincipalUpperBound(
                        ArctanPrincipalUpperBoundBuiltinRuleProof {},
                    ),
                ));
            }

            // `0 < arccot(x)`
            (_, Obj::TrigOperator(TrigOperator::Arccot(_)))
                if match_arccot_principal_lower(&fact.left, &fact.right) =>
            {
                return Ok(Some(
                    LessFactSearchProofByBuiltinRule::ArccotPrincipalLowerBound(
                        ArccotPrincipalLowerBoundBuiltinRuleProof {},
                    ),
                ));
            }

            // `arccot(x) < pi`
            (Obj::TrigOperator(TrigOperator::Arccot(_)), _)
                if match_arccot_principal_upper(&fact.left, &fact.right) =>
            {
                return Ok(Some(
                    LessFactSearchProofByBuiltinRule::ArccotPrincipalUpperBound(
                        ArccotPrincipalUpperBoundBuiltinRuleProof {},
                    ),
                ));
            }

            // `0 < a + b` / `0 < a * b`
            (left, Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left: a, right: b })))
                if is_zero_obj(left) =>
            {
                if let Some(proof) =
                    self.sum_positive_cone_proof(a.as_ref(), b.as_ref(), verify_state)?
                {
                    return Ok(Some(proof));
                }
            }
            (left, Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left: a, right: b })))
                if is_zero_obj(left) =>
            {
                if let Some(proof) =
                    self.product_both_positive_proof(a.as_ref(), b.as_ref(), verify_state)?
                {
                    return Ok(Some(proof));
                }
            }

            _ => {}
        }

        let Some((cmp, left_normal, right_normal)) =
            compare_closed_objs_by_normalized_decimal(&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        if cmp != NumberCompareResult::Less {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::ClosedNumericComparison(
                ClosedNumericComparisonBuiltinRuleProof {
                    left_normal,
                    right_normal,
                },
            ),
        ))
    }


    // Prefer both-strict, then left-strict/right-weak, then left-weak/right-strict.
    fn sum_positive_cone_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let left_pos = self.verify_positive(left, verify_state.clone())?;
        let right_pos = self.verify_positive(right, verify_state.clone())?;
        if !left_pos.is_failed() && !right_pos.is_failed() {
            return Ok(Some(LessFactSearchProofByBuiltinRule::SumBothPositive(
                SumBothPositiveBuiltinRuleProof {
                    left_positive_proof: left_pos,
                    right_positive_proof: right_pos,
                },
            )));
        }
        let left_pos = self.verify_positive(left, verify_state.clone())?;
        let right_nonneg = self.verify_nonnegative_for_less(right, verify_state.clone())?;
        if !left_pos.is_failed() && !right_nonneg.is_failed() {
            return Ok(Some(
                LessFactSearchProofByBuiltinRule::SumLeftStrictRightNonnegative(
                    SumLeftStrictRightNonnegativeBuiltinRuleProof {
                        left_positive_proof: left_pos,
                        right_nonnegative_proof: right_nonneg,
                    },
                ),
            ));
        }
        let left_nonneg = self.verify_nonnegative_for_less(left, verify_state.clone())?;
        let right_pos = self.verify_positive(right, verify_state)?;
        if !left_nonneg.is_failed() && !right_pos.is_failed() {
            return Ok(Some(
                LessFactSearchProofByBuiltinRule::SumLeftNonnegativeRightStrict(
                    SumLeftNonnegativeRightStrictBuiltinRuleProof {
                        left_nonnegative_proof: left_nonneg,
                        right_positive_proof: right_pos,
                    },
                ),
            ));
        }
        Ok(None)
    }

    fn product_both_positive_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let left_positive_proof = self.verify_positive(left, verify_state.clone())?;
        if left_positive_proof.is_failed() {
            return Ok(None);
        }
        let right_positive_proof = self.verify_positive(right, verify_state)?;
        if right_positive_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(LessFactSearchProofByBuiltinRule::ProductBothPositive(
            ProductBothPositiveBuiltinRuleProof {
                left_positive_proof,
                right_positive_proof,
            },
        )))
    }

    fn verify_positive(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = Fact::AtomicFact(AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: zero_obj(),
            right: obj.clone(),
            line_file: None,
        }));
        self.verify_fact(&goal, verify_state)
    }

    fn verify_nonnegative_for_less(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        // Reuse the shared `0 <= obj` goal helper from order_abs via verify_fact.
        let goal = Fact::AtomicFact(AtomicFact::LessEqualFact(
            crate::new_pipeline::ast::fact::LessEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: zero_obj(),
                right: obj.clone(),
                line_file: None,
            },
        ));
        self.verify_fact(&goal, verify_state)
    }
}
