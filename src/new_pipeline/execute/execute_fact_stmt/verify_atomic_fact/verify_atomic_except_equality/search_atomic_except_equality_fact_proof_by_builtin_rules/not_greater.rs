use crate::new_pipeline::ast::fact::NotGreaterFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::{
    compare_closed_objs_by_normalized_decimal, NumberCompareResult,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin rules for `not a > b` (i.e. a <= b on numbers).
pub enum NotGreaterFactSearchProofByBuiltinRule {
    // Closed numeric comparison: evaluated L is not strictly greater than R.
    // Mathematical property: if L <= R as decimals, then `not (left > right)`.
    // Examples: `not 1 > 2`, `not 2 > 2`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
}

pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

impl Runtime {
    // Builtin: closed decimal proves `not a > b`.
    // Example: prove `not 1 > 3`.
    pub fn search_not_greater_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotGreaterFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotGreaterFactSearchProofByBuiltinRule>> {
        let Some((cmp, left_normal, right_normal)) =
            compare_closed_objs_by_normalized_decimal(&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        if cmp == NumberCompareResult::Greater {
            return Ok(None);
        }
        Ok(Some(
            NotGreaterFactSearchProofByBuiltinRule::ClosedNumericComparison(
                ClosedNumericComparisonBuiltinRuleProof {
                    left_normal,
                    right_normal,
                },
            ),
        ))
    }
}
