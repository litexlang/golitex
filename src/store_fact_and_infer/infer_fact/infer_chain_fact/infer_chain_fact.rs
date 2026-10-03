use crate::ast::fact::ChainFact;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::InferChainFactResult;

impl Runtime {
    // Adjacent edges: atomic packaging. Transitive closures: chain-level rules (not packaging).
    // Example: `a < b < c` infers on a<b and b<c, then stores BuiltinNumericOrder ⇒ a<c.
    pub(crate) fn infer_chain_fact(
        &mut self,
        chain_fact: &ChainFact,
     verify_state: crate::execute::execute_fact_stmt::VerifyState) -> RuntimeResult<InferChainFactResult> {
        let adjacent_atomics = self.chain_adjacent_atomics(chain_fact)?;
        let mut adjacent_infers = Vec::with_capacity(adjacent_atomics.len());
        for atomic in &adjacent_atomics {
            adjacent_infers.push(self.infer_atomic_fact(atomic, verify_state)?);
        }
        let transitive_closures =
            self.infer_chain_transitive_closures(chain_fact, adjacent_infers.len(), verify_state)?;
        Ok(InferChainFactResult {
            adjacent_infers,
            transitive_closures,
        })
    }
}
