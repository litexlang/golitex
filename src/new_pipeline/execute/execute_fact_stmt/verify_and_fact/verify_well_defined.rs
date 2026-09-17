use crate::new_pipeline::ast::fact::AndFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_and_fact::well_defined_result::{
    AndFactWellDefinedProof, FailToVerifyAndFactWellDefinedResult, VerifyAndFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::VerifyAtomicFactWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // WD each atomic conjunct. First soft miss → Failed.
    // Example: `1 < 2 and 2 < 3` succeeds only if both atomics are WD.
    pub fn verify_and_fact_well_definedness(
        &mut self,
        fact: &AndFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyAndFactWellDefinedResult> {
        let mut components = Vec::with_capacity(fact.facts.len());
        for (failed_index, atomic) in fact.facts.iter().enumerate() {
            match self.verify_atomic_fact_well_definedness(atomic, verify_state.clone())? {
                VerifyAtomicFactWellDefinedResult::Success(proof) => {
                    components.push(proof);
                }
                VerifyAtomicFactWellDefinedResult::Failed(failed_component) => {
                    return Ok(VerifyAndFactWellDefinedResult::Failed(
                        FailToVerifyAndFactWellDefinedResult {
                            failed_index,
                            succeeded_components: components,
                            failed_component,
                        },
                    ));
                }
            }
        }
        Ok(VerifyAndFactWellDefinedResult::Success(
            AndFactWellDefinedProof { components },
        ))
    }
}
