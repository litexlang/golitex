use crate::new_pipeline::ast::fact::GreaterFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::{
    compare_closed_objs_by_normalized_decimal, NumberCompareResult,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin rules for `a > b`.
pub enum GreaterFactSearchProofByBuiltinRule {
    // Closed numeric comparison by evaluation.
    // Mathematical property: if both sides evaluate to decimals L, R with L > R,
    // then `left > right`.
    // Examples: `2 > 1`, `5 > 1 + 1`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
}

// Payload: both evaluated normals with left_normal > right_normal.
pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

impl Runtime {
    // Builtin: closed decimal proves strict greater.
    // Example: prove `2 > 1`.
    pub fn search_greater_fact_proof_by_builtin_rule(
        &mut self,
        fact: &GreaterFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<GreaterFactSearchProofByBuiltinRule>> {
        let Some((cmp, left_normal, right_normal)) =
            compare_closed_objs_by_normalized_decimal(&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        if cmp != NumberCompareResult::Greater {
            return Ok(None);
        }
        Ok(Some(
            GreaterFactSearchProofByBuiltinRule::ClosedNumericComparison(
                ClosedNumericComparisonBuiltinRuleProof {
                    left_normal,
                    right_normal,
                },
            ),
        ))
    }
}
