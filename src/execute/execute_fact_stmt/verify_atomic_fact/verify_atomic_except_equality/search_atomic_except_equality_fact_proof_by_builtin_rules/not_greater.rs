use super::order_complement::FromKnownOrderComplementBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::ast::fact::NotGreaterFact;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::{
    compare_closed_objs_by_normalized_decimal, NumberCompareResult,
};
use crate::runtime::{Runtime, RuntimeResult};

// Builtin rules for `not a > b` (i.e. a <= b on numbers).
pub enum NotGreaterFactSearchProofByBuiltinRule {
    FromKnownOrderComplement(FromKnownOrderComplementBuiltinRuleProof),
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
    pub premise_proof: AtomicExceptEqualityFactKnownProof,
}

impl Runtime {
    // Builtin: known `<`, then closed decimal.
    pub fn search_not_greater_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotGreaterFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotGreaterFactSearchProofByBuiltinRule>> {
        if let Some(proof) = self.known_order_complement(fact.clone().into(), verify_state.clone())? {
            return Ok(Some(NotGreaterFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof)));
        }
        if let Some(premise_proof) = self.known_less_proof(&fact.left, &fact.right) {
            return Ok(Some(
                NotGreaterFactSearchProofByBuiltinRule::FromKnownLess(
                    FromKnownLessBuiltinRuleProof { premise_proof },
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
