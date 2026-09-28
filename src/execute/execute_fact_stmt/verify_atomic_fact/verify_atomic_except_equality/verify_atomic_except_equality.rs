use crate::ast::fact::AtomicFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{
    atomic_except_equality_fact_result_from_search_fail,
    atomic_except_equality_fact_result_from_success,
    atomic_except_equality_fact_result_from_wd_fail,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::{
    VerifyAtomicFactWellDefinedResult, VerifyState,
};
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn verify_atomic_except_equality(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let well_defined_proof = match self
            .verify_atomic_fact_well_definedness(fact, verify_state.clone())?
        {
            VerifyAtomicFactWellDefinedResult::Success(proof) => proof,
            VerifyAtomicFactWellDefinedResult::Failed(reason) => {
                return Ok(atomic_except_equality_fact_result_from_wd_fail(reason));
            }
        };
        match self.search_atomic_except_equality_fact_proof(fact, verify_state)? {
            Some(searched_proof) => Ok(atomic_except_equality_fact_result_from_success(
                fact,
                well_defined_proof,
                searched_proof,
            )),
            None => Ok(atomic_except_equality_fact_result_from_search_fail(
                fact,
                well_defined_proof,
            )),
        }
    }
}
