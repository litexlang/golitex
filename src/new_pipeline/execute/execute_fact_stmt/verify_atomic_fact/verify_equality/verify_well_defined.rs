use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::{
    EqualFactWellDefinedProof, FailToVerifyEqualFactWellDefinedResult,
    VerifyEqualFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::VerifyObjWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // WD left, then right. First soft miss → Failed(reason); otherwise Success(proofs).
    // Example: `1 + 1 = 2` needs WD of `1 + 1` and of `2`.
    pub fn verify_equal_fact_well_definedness(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyEqualFactWellDefinedResult> {
        let left = match self.verify_obj_well_definedness(&fact.left, verify_state.clone())? {
            VerifyObjWellDefinedResult::Success(proof) => proof,
            VerifyObjWellDefinedResult::Failed(reason) => {
                return Ok(VerifyEqualFactWellDefinedResult::Failed(
                    FailToVerifyEqualFactWellDefinedResult { reason },
                ));
            }
        };
        let right = match self.verify_obj_well_definedness(&fact.right, verify_state)? {
            VerifyObjWellDefinedResult::Success(proof) => proof,
            VerifyObjWellDefinedResult::Failed(reason) => {
                return Ok(VerifyEqualFactWellDefinedResult::Failed(
                    FailToVerifyEqualFactWellDefinedResult { reason },
                ));
            }
        };
        Ok(VerifyEqualFactWellDefinedResult::Success(
            EqualFactWellDefinedProof { left, right },
        ))
    }
}
