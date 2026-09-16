use crate::new_pipeline::ast::fact::LessFact;
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
}

// Payload: both evaluated normals with left_normal < right_normal.
pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

impl Runtime {
    // Builtin: closed decimal proves strict less.
    // Example: prove `1 < 2`.
    pub fn search_less_fact_proof_by_builtin_rule(
        &mut self,
        fact: &LessFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
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
