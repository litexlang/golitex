use super::order_complement::FromKnownOrderComplementBuiltinRuleProof;
use crate::ast::fact::NotLessEqualFact;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::{compare_closed_numeric_objs, NumberCompareResult};
use crate::runtime::{Runtime, RuntimeResult};

// Builtin rules for `not a <= b` (i.e. a > b on numbers).
pub enum NotLessEqualFactSearchProofByBuiltinRule {
    FromKnownOrderComplement(FromKnownOrderComplementBuiltinRuleProof),
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
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotLessEqualFactSearchProofByBuiltinRule>> {
        if let Some(proof) =
            self.known_order_complement(fact.clone().into(), verify_state.clone())?
        {
            return Ok(Some(
                NotLessEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            ));
        }
        let Some((cmp, left_normal, right_normal)) =
            compare_closed_numeric_objs(&fact.left, &fact.right)
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
