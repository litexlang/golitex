use super::order_complement::FromKnownOrderComplementBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::ast::fact::NotLessFact;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::{
    compare_closed_numeric_objs, NumberCompareResult,
};
use crate::runtime::{Runtime, RuntimeResult};

// Builtin rules for `not a < b` (i.e. a >= b on numbers).
pub enum NotLessFactSearchProofByBuiltinRule {
    FromKnownOrderComplement(FromKnownOrderComplementBuiltinRuleProof),
    // Closed numeric comparison: evaluated L is not strictly less than R.
    // Mathematical property: if L >= R as decimals, then `not (left < right)`.
    // Examples: `not 2 < 1`, `not 2 < 2`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
    // Strict greater implies not-less.
    // Mathematical property: `a > b` ⇒ `not (a < b)`.
    // Example: known `x > 0` proves `not x < 0`.
    FromKnownGreater(FromKnownGreaterBuiltinRuleProof),
}

pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

pub struct FromKnownGreaterBuiltinRuleProof {
    pub premise_proof: AtomicExceptEqualityFactKnownProof,
}

impl Runtime {
    // Builtin: known `>`, then closed decimal.
    pub fn search_not_less_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotLessFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotLessFactSearchProofByBuiltinRule>> {
        if let Some(proof) = self.known_order_complement(fact.clone().into(), verify_state.clone())? {
            return Ok(Some(NotLessFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof)));
        }
        if let Some(premise_proof) = self.known_greater_proof(&fact.left, &fact.right) {
            return Ok(Some(
                NotLessFactSearchProofByBuiltinRule::FromKnownGreater(
                    FromKnownGreaterBuiltinRuleProof { premise_proof },
                ),
            ));
        }
        let Some((cmp, left_normal, right_normal)) =
            compare_closed_numeric_objs(&fact.left, &fact.right)
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
