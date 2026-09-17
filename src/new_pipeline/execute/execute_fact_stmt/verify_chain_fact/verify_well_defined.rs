use crate::new_pipeline::ast::fact::ChainFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::VerifyAtomicFactWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_chain_fact::well_defined_result::{
    ChainFactWellDefinedProof, FailToVerifyChainFactWellDefinedResult,
    VerifyChainFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Expand chain to adjacent atomics, then WD each. First soft miss → Failed.
    // Example: `1 < 2 < 3` succeeds only if both adjacent atomics are WD.
    pub fn verify_chain_fact_well_definedness(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyChainFactWellDefinedResult> {
        let adjacent_atomics = self.chain_adjacent_atomics(fact)?;
        let mut adjacent = Vec::with_capacity(adjacent_atomics.len());
        for (failed_index, atomic) in adjacent_atomics.iter().enumerate() {
            match self.verify_atomic_fact_well_definedness(atomic, verify_state.clone())? {
                VerifyAtomicFactWellDefinedResult::Success(proof) => {
                    adjacent.push(proof);
                }
                VerifyAtomicFactWellDefinedResult::Failed(failed_adjacent) => {
                    return Ok(VerifyChainFactWellDefinedResult::Failed(
                        FailToVerifyChainFactWellDefinedResult {
                            failed_index,
                            succeeded_adjacent: adjacent,
                            failed_adjacent,
                        },
                    ));
                }
            }
        }
        Ok(VerifyChainFactWellDefinedResult::Success(
            ChainFactWellDefinedProof { adjacent },
        ))
    }
}
