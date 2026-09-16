use crate::new_pipeline::ast::fact::NotLessEqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::{
    compare_closed_objs_by_normalized_decimal, NumberCompareResult,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin rules for `not a <= b` (i.e. a > b on numbers).
pub enum NotLessEqualFactSearchProofByBuiltinRule {
    // Closed numeric comparison: evaluated L is strictly greater than R.
    // Mathematical property: if L > R as decimals, then `not (left <= right)`.
    // Examples: `not 3 <= 1`, `not 1 + 1 <= 1`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
}

pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

impl Runtime {
    // Builtin: closed decimal proves `not a <= b`.
    // Example: prove `not 5 <= 2`.
    pub fn search_not_less_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotLessEqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotLessEqualFactSearchProofByBuiltinRule>> {
        let Some((cmp, left_normal, right_normal)) =
            compare_closed_objs_by_normalized_decimal(&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        if cmp != NumberCompareResult::Greater {
            return Ok(None);
        }
        Ok(Some(
            NotLessEqualFactSearchProofByBuiltinRule::ClosedNumericComparison(
                ClosedNumericComparisonBuiltinRuleProof {
                    left_normal,
                    right_normal,
                },
            ),
        ))
    }
}
