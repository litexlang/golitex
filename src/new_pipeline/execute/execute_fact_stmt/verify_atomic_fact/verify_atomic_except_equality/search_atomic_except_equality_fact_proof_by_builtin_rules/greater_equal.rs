use crate::new_pipeline::ast::fact::GreaterEqualFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::{
    compare_closed_objs_by_normalized_decimal, NumberCompareResult,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin rules for `a >= b`.
pub enum GreaterEqualFactSearchProofByBuiltinRule {
    // Closed numeric comparison by evaluation.
    // Mathematical property: if both sides evaluate to decimals L, R with L >= R,
    // then `left >= right`.
    // Examples: `2 >= 1`, `2 >= 2`, `3 >= 1 + 1`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
    // Order reflexivity: `x >= x`.
    // Mathematical property: >= is reflexive on any object.
    // Example: prove `a >= a`.
    OrderReflexivity(OrderReflexivityBuiltinRuleProof),
}

// Payload: both evaluated normals with left_normal >= right_normal.
pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

// Payload for reflexivity: the repeated object.
pub struct OrderReflexivityBuiltinRuleProof {
    pub repeated_object: Obj,
}

impl Runtime {
    // Builtin: reflexivity first, then closed decimal `>=`.
    // Examples: `a >= a`; `2 >= 1`.
    pub fn search_greater_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &GreaterEqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<GreaterEqualFactSearchProofByBuiltinRule>> {
        if fact.left.ir() == fact.right.ir() {
            return Ok(Some(
                GreaterEqualFactSearchProofByBuiltinRule::OrderReflexivity(
                    OrderReflexivityBuiltinRuleProof {
                        repeated_object: fact.left.clone(),
                    },
                ),
            ));
        }
        let Some((cmp, left_normal, right_normal)) =
            compare_closed_objs_by_normalized_decimal(&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        if matches!(cmp, NumberCompareResult::Less) {
            return Ok(None);
        }
        Ok(Some(
            GreaterEqualFactSearchProofByBuiltinRule::ClosedNumericComparison(
                ClosedNumericComparisonBuiltinRuleProof {
                    left_normal,
                    right_normal,
                },
            ),
        ))
    }
}
