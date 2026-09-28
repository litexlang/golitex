use crate::ast::fact::NotGreaterFact;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::{
    compare_closed_objs_by_normalized_decimal, NumberCompareResult,
};
use crate::runtime::{FactId, Runtime, RuntimeResult};

// Builtin rules for `not a > b` (i.e. a <= b on numbers).
pub enum NotGreaterFactSearchProofByBuiltinRule {
    // Closed numeric comparison: evaluated L is not strictly greater than R.
    // Mathematical property: if L <= R as decimals, then `not (left > right)`.
    // Examples: `not 1 > 2`, `not 2 > 2`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
    // Strict less implies not-greater.
    // Mathematical property: `a < b` ⇒ `not (a > b)`.
    // Example: known `x < 0` proves `not x > 0`.
    FromKnownLess(FromKnownLessBuiltinRuleProof),
}

pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

pub struct FromKnownLessBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

impl Runtime {
    // Builtin: known `<`, then closed decimal.
    pub fn search_not_greater_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotGreaterFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotGreaterFactSearchProofByBuiltinRule>> {
        if let Some(cite_fact_id) = self.known_less_fact_id(&fact.left, &fact.right) {
            return Ok(Some(
                NotGreaterFactSearchProofByBuiltinRule::FromKnownLess(
                    FromKnownLessBuiltinRuleProof { cite_fact_id },
                ),
            ));
        }
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
