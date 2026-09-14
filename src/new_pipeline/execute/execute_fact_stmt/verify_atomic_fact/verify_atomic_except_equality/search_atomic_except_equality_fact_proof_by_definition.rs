use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::AtomicExceptEqualityFactSearchProofByDefinition;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn search_atomic_except_equality_fact_proof_by_definition(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByDefinition>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
