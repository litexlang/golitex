use crate::new_pipeline::ast::fact::LessFact;
use crate::new_pipeline::ast::obj::{ArithmeticOperator, Obj, Sub, TrigOperator};
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

impl Runtime {
    // Builtin search for `a < b`.
    // B0: none (no known-cite / reflexivity for strict < here).
    // A: match on Obj shapes of (left, right).
    // B1: closed decimal evaluation.
    // Example: prove `n - 1 < n`, `-pi/2 < arctan(x)`, or `1 < 2`.
    pub fn search_less_fact_proof_by_builtin_rule(
        &mut self,
        fact: &LessFact,
        _verify_state: VerifyState,
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
}
