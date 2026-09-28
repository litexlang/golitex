use crate::ast::fact::NotGreaterEqualFact;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::{
    compare_closed_objs_by_normalized_decimal, NumberCompareResult,
};
use crate::runtime::{Runtime, RuntimeResult};

// Builtin rules for `not a >= b` (i.e. a < b on numbers).
pub enum NotGreaterEqualFactSearchProofByBuiltinRule {
    // Closed numeric comparison: evaluated L is strictly less than R.
    // Mathematical property: if L < R as decimals, then `not (left >= right)`.
    // Examples: `not 1 >= 3`, `not 1 >= 1 + 1`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
}

pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

impl Runtime {
    // Builtin: closed decimal proves `not a >= b`.
    // Example: prove `not 1 >= 4`.
    pub fn search_not_greater_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotGreaterEqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotGreaterEqualFactSearchProofByBuiltinRule>> {
        let Some((cmp, left_normal, right_normal)) =
            compare_closed_objs_by_normalized_decimal(&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        if cmp != NumberCompareResult::Less {
            return Ok(None);
        }
        Ok(Some(
            NotGreaterEqualFactSearchProofByBuiltinRule::ClosedNumericComparison(
                ClosedNumericComparisonBuiltinRuleProof {
                    left_normal,
                    right_normal,
                },
            ),
        ))
    }
}
