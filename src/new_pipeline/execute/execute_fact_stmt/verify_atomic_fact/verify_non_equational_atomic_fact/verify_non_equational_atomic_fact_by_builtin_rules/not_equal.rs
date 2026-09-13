use crate::new_pipeline::ast::fact::{Fact, NotEqualFact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub enum NotEqualFactSearchProofByBuiltinRule {
    // Not-equal symmetry, e.g. prove `a != b` from a proved `b != a`.
    NotEqualSymmetry(NotEqualSymmetryBuiltinRuleProof),
    // List sets of different lengths are unequal.
    // Example: prove `{1} != {1, 2}`.
    ListSetDifferentLength(ListSetDifferentLengthBuiltinRuleProof),
}

pub struct NotEqualSymmetryBuiltinRuleProof {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}

pub struct ListSetDifferentLengthBuiltinRuleProof {}

impl Runtime {
    // Builtin: zero-premise not-equal for list sets of different lengths.
    // Example: prove `{1} != {1, 2}`.
    pub fn search_not_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        let _ = verify_state;
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
