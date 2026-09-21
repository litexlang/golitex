use crate::new_pipeline::ast::fact::{Fact, NotEqualFact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::evaluate_obj_to_normalized_decimal_number;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};

// Builtin rules for `!=` facts (zero-premise routes).
pub enum NotEqualFactSearchProofByBuiltinRule {
    // Closed decimal evaluation yields unequal normals.
    // Mathematical property: if both sides evaluate to normalized decimals
    // `L` and `R` with `L != R`, then the objects are unequal.
    // Examples: `1 != 0`, `1 + 1 != 3`.
    ClosedDecimal(ClosedDecimalNotEqualBuiltinRuleProof),
    // Not-equal symmetry: prove `a != b` from a proved `b != a`.
    // Example: known `0 != x` proves `x != 0`.
    NotEqualSymmetry(NotEqualSymmetryBuiltinRuleProof),
    // List sets of different lengths are unequal.
    // Example: prove `{1} != {1, 2}`.
    ListSetDifferentLength(ListSetDifferentLengthBuiltinRuleProof),
    // Strict order implies inequality.
    // Mathematical property: `a > b` or `a < b` ⇒ `a != b`.
    // Example: known `x > 0` proves `x != 0`.
    FromKnownStrictOrder(FromKnownStrictOrderBuiltinRuleProof),
}

pub struct ClosedDecimalNotEqualBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

pub struct NotEqualSymmetryBuiltinRuleProof {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}

pub struct ListSetDifferentLengthBuiltinRuleProof {}

pub struct FromKnownStrictOrderBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

impl Runtime {
    // Builtin not-equal: closed decimal, known strict order, then list-set length.
    pub fn search_not_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotEqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        if let (Some(left), Some(right)) = (
            evaluate_obj_to_normalized_decimal_number(&fact.left),
            evaluate_obj_to_normalized_decimal_number(&fact.right),
        ) {
            if left.normalized_value != right.normalized_value {
                return Ok(Some(NotEqualFactSearchProofByBuiltinRule::ClosedDecimal(
                    ClosedDecimalNotEqualBuiltinRuleProof {
                        left_normal: left.normalized_value,
                        right_normal: right.normalized_value,
                    },
                )));
            }
        }
        if let Some(cite_fact_id) = self
            .known_greater_fact_id(&fact.left, &fact.right)
            .or_else(|| self.known_less_fact_id(&fact.left, &fact.right))
        {
            return Ok(Some(
                NotEqualFactSearchProofByBuiltinRule::FromKnownStrictOrder(
                    FromKnownStrictOrderBuiltinRuleProof { cite_fact_id },
                ),
            ));
        }
        if let (Obj::ListSet(left), Obj::ListSet(right)) = (&fact.left, &fact.right) {
            if left.list.len() != right.list.len() {
                return Ok(Some(
                    NotEqualFactSearchProofByBuiltinRule::ListSetDifferentLength(
                        ListSetDifferentLengthBuiltinRuleProof {},
                    ),
                ));
            }
        }
        Ok(None)
    }
}
