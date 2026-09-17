use crate::new_pipeline::ast::fact::ChainFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_chain_fact::result::{
    chain_fact_result_from_adjacent_fail, chain_fact_result_from_success,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Prove chain by proving each adjacent atomic edge.
    // Example: `1 < 2 < 3` requires proofs of `1 < 2` and `2 < 3`.
    pub fn verify_chain_fact(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let adjacent_atomics = self.chain_adjacent_atomics(fact)?;
        let mut adjacent = Vec::with_capacity(adjacent_atomics.len());
        for (failed_index, atomic) in adjacent_atomics.iter().enumerate() {
            let step = self.verify_atomic_fact(atomic, verify_state.clone())?;
            if step.is_failed() {
                return Ok(chain_fact_result_from_adjacent_fail(
                    fact,
                    failed_index,
                    adjacent,
                    step,
                ));
            }
            adjacent.push(step);
        }
        Ok(chain_fact_result_from_success(fact, adjacent))
    }
}
