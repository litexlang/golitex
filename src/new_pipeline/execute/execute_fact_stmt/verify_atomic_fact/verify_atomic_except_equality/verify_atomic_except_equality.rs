use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::VerifyAtomicExceptEqualityFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::{
    VerifyFactResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn verify_atomic_except_equality(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let well_defined_proof =
            self.verify_atomic_fact_well_definedness(fact, verify_state.clone())?;
        if well_defined_proof.is_failed() {
            return Ok(VerifyFactResult::FailToVerifyWellDefined);
        }
        match self.search_atomic_except_equality_fact_proof(fact, verify_state)? {
            Some(searched_proof) => Ok(VerifyFactResult::AtomicExceptEquality(Box::new(
                VerifyAtomicExceptEqualityFactResult {
                    fact: fact.clone(),
                    well_defined_proof,
                    searched_proof,
                },
            ))),
            None => Ok(VerifyFactResult::FailToSearchProof),
        }
    }
}
