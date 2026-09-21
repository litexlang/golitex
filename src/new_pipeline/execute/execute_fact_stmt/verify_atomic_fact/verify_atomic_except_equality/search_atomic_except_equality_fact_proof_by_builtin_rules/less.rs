use crate::new_pipeline::ast::fact::LessFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::predecessor_helpers::match_sub_one;
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

impl Runtime {
    // Builtin: subtract-one decrease, then closed decimal strict less.
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
