use crate::new_pipeline::ast::fact::NotLessFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::{
    compare_closed_objs_by_normalized_decimal, NumberCompareResult,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin rules for `not a < b` (i.e. a >= b on numbers).
pub enum NotLessFactSearchProofByBuiltinRule {
    // Closed numeric comparison: evaluated L is not strictly less than R.
    // Mathematical property: if L >= R as decimals, then `not (left < right)`.
    // Examples: `not 2 < 1`, `not 2 < 2`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
}

pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

impl Runtime {
    // Builtin: closed decimal proves `not a < b`.
    // Example: prove `not 3 < 1`.
    pub fn search_not_less_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotLessFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotLessFactSearchProofByBuiltinRule>> {
        let Some((cmp, left_normal, right_normal)) =
            compare_closed_objs_by_normalized_decimal(&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        if cmp == NumberCompareResult::Less {
            return Ok(None);
        }
        Ok(Some(
            NotLessFactSearchProofByBuiltinRule::ClosedNumericComparison(
                ClosedNumericComparisonBuiltinRuleProof {
                    left_normal,
                    right_normal,
                },
            ),
        ))
    }
}
