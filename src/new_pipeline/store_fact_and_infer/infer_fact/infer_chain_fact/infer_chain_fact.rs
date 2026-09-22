use crate::new_pipeline::ast::fact::ChainFact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::{
    InferFactResult, StoreChainAdjacentResult,
};

impl Runtime {
    // Infer adjacent edges of a stored chain, then optional transitive closures.
    // Example: `a < b < c` infers on a<b and b<c, then stores BuiltinNumericOrder ⇒ a<c.
    pub(crate) fn infer_chain_fact(
        &mut self,
        chain_fact: &ChainFact,
    ) -> RuntimeResult<InferFactResult> {
        let adjacent_atomics = self.chain_adjacent_atomics(chain_fact)?;
        for atomic in &adjacent_atomics {
            self.infer_atomic_fact(atomic)?;
        }
        let mut adjacent = Vec::with_capacity(adjacent_atomics.len());
        for (edge_index, atomic) in adjacent_atomics.into_iter().enumerate() {
            adjacent.push(StoreChainAdjacentResult {
                edge_index,
                fact_id: atomic.fact_id(),
                fact: atomic,
            });
        }
        let transitive_closures =
            self.infer_chain_transitive_closures(chain_fact, &adjacent)?;
        Ok(InferFactResult::ChainFact {
            transitive_closures,
        })
    }
}
