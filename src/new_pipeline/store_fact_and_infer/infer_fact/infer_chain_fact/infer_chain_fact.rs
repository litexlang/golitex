use crate::new_pipeline::ast::fact::ChainFact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::InferChainFactResult;

impl Runtime {
    // Infer adjacent edges of a stored chain, then optional transitive closures.
    // Example: `a < b < c` infers on a<b and b<c, then stores BuiltinNumericOrder ⇒ a<c.
    pub(crate) fn infer_chain_fact(
        &mut self,
        chain_fact: &ChainFact,
    ) -> RuntimeResult<InferChainFactResult> {
        let adjacent_atomics = self.chain_adjacent_atomics(chain_fact)?;
        let mut adjacent_infers = Vec::with_capacity(adjacent_atomics.len());
        for atomic in &adjacent_atomics {
            adjacent_infers.push(self.infer_atomic_fact(atomic)?);
        }
        let transitive_closures =
            self.infer_chain_transitive_closures(chain_fact, adjacent_infers.len())?;
        Ok(InferChainFactResult {
            adjacent_infers,
            transitive_closures,
        })
    }
}
