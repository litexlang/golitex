use crate::new_pipeline::ast::fact::LessFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::predecessor_helpers::match_sub_one;
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
    // Builtin: subtract-one decrease, trig principal open bounds, then closed decimal strict less.
    // Example: prove `n - 1 < n` or `1 < 2`.
    pub fn search_less_fact_proof_by_builtin_rule(
        &mut self,
        fact: &LessFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        if let Some(minuend) = match_sub_one(&fact.left) {
            if minuend.ir() == fact.right.ir() {
                return Ok(Some(LessFactSearchProofByBuiltinRule::SubtractOneLess(
                    SubtractOneLessBuiltinRuleProof {
                        minuend: minuend.clone(),
                    },
                )));
            }
        }
        if match_arctan_principal_lower(&fact.left, &fact.right) {
            return Ok(Some(
                LessFactSearchProofByBuiltinRule::ArctanPrincipalLowerBound(
                    ArctanPrincipalLowerBoundBuiltinRuleProof {},
                ),
            ));
        }
        if match_arctan_principal_upper(&fact.left, &fact.right) {
            return Ok(Some(
                LessFactSearchProofByBuiltinRule::ArctanPrincipalUpperBound(
                    ArctanPrincipalUpperBoundBuiltinRuleProof {},
                ),
            ));
        }
        if match_arccot_principal_lower(&fact.left, &fact.right) {
            return Ok(Some(
                LessFactSearchProofByBuiltinRule::ArccotPrincipalLowerBound(
                    ArccotPrincipalLowerBoundBuiltinRuleProof {},
                ),
            ));
        }
        if match_arccot_principal_upper(&fact.left, &fact.right) {
            return Ok(Some(
                LessFactSearchProofByBuiltinRule::ArccotPrincipalUpperBound(
                    ArccotPrincipalUpperBoundBuiltinRuleProof {},
                ),
            ));
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
