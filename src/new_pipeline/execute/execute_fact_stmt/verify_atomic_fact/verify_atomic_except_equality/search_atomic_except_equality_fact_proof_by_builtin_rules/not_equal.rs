use crate::new_pipeline::ast::fact::{Fact, NotEqualFact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::evaluate_obj_to_normalized_decimal_number;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

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
}

// Payload for ClosedDecimal not-equal: both evaluated normals (must differ).
// Example: `1 != 0` stores left_normal `"1"`, right_normal `"0"`.
pub struct ClosedDecimalNotEqualBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

// Payload for symmetry: the flipped fact and its successful proof.
pub struct NotEqualSymmetryBuiltinRuleProof {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}

// Payload for different-length list sets (no extra data; sides live on the fact).
pub struct ListSetDifferentLengthBuiltinRuleProof {}

impl Runtime {
    // Builtin not-equal search order: closed decimal, then list-set length.
    // Examples: `1 != 0`; `{1} != {1, 2}`.
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
