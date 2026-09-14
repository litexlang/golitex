use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::VerifyAtomicExceptEqualityFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn verify_atomic_except_equality(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyAtomicExceptEqualityFactResult> {
        let well_defined_proof =
            self.verify_atomic_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_atomic_except_equality_fact_proof(fact, verify_state)?;
        Ok(VerifyAtomicExceptEqualityFactResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }
}
