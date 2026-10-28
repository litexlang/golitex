use crate::ast::fact::ChainFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::VerifyAtomicFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_chain_fact::well_defined_result::{
    ChainFactWellDefinedProof, FailToVerifyChainFactWellDefinedResult,
    VerifyChainFactWellDefinedResult,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Expand chain to adjacent atomics, then WD each. First soft miss → Failed.
    // Example: `1 < 2 < 3` succeeds only if both adjacent atomics are WD.
    pub fn verify_chain_fact_well_definedness(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyChainFactWellDefinedResult> {
        let adjacent_atomics = self.chain_adjacent_atomics(fact)?;
        let mut proof =
            ChainFactWellDefinedProof::new(self.result_detail(), adjacent_atomics.len());
        for (failed_index, atomic) in adjacent_atomics.iter().enumerate() {
            match self.verify_atomic_component_well_definedness(atomic, verify_state.clone())? {
                VerifyAtomicFactWellDefinedResult::Success(adjacent) => {
                    proof.push_adjacent(adjacent)?;
                }
                VerifyAtomicFactWellDefinedResult::Failed(failed_adjacent) => {
                    return Ok(VerifyChainFactWellDefinedResult::Failed(
                        FailToVerifyChainFactWellDefinedResult {
                            fact: fact.clone(),
                            failed_index,
                            succeeded_adjacent: proof.into_completed(),
                            failed_adjacent,
                        },
                    ));
                }
            }
        }
        Ok(VerifyChainFactWellDefinedResult::Success(proof))
    }
}
