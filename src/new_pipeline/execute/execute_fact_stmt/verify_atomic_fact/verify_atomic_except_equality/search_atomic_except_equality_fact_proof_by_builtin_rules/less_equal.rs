use crate::new_pipeline::ast::fact::LessEqualFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::{
    compare_closed_objs_by_normalized_decimal, NumberCompareResult,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin rules for `a <= b`.
pub enum LessEqualFactSearchProofByBuiltinRule {
    // Closed numeric comparison by evaluation.
    // Mathematical property: if both sides evaluate to decimals L, R with L <= R,
    // then `left <= right`.
    // Examples: `1 <= 2`, `2 <= 2`, `1 + 1 <= 3`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
    // Order reflexivity: `x <= x`.
    // Mathematical property: <= is reflexive on any object.
    // Example: prove `a <= a`.
    OrderReflexivity(OrderReflexivityBuiltinRuleProof),
}

// Payload: both evaluated normals with left_normal <= right_normal.
pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

// Payload for reflexivity: the repeated object.
pub struct OrderReflexivityBuiltinRuleProof {
    pub repeated_object: Obj,
}

impl Runtime {
    // Builtin: reflexivity first, then closed decimal `<=`.
    // Examples: `a <= a`; `1 <= 2`.
    pub fn search_less_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &LessEqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        if fact.left.ir() == fact.right.ir() {
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::OrderReflexivity(
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
        if matches!(
            cmp,
            NumberCompareResult::Greater
        ) {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::ClosedNumericComparison(
                ClosedNumericComparisonBuiltinRuleProof {
                    left_normal,
                    right_normal,
                },
            ),
        ))
    }
}
