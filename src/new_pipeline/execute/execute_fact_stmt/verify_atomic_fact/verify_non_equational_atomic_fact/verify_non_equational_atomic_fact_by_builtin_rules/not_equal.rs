use crate::new_pipeline::ast::fact::{Fact, NotEqualFact};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub enum NotEqualFactSearchProofByBuiltinRule {
    // Not-equal symmetry, e.g. prove `a != b` from a proved `b != a`.
    NotEqualSymmetry(NotEqualSymmetryBuiltinRuleProof),
}

pub struct NotEqualSymmetryBuiltinRuleProof {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}

impl Runtime {
    pub fn search_not_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
