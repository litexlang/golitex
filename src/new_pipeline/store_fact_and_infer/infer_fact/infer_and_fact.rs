use crate::new_pipeline::ast::fact::AndFact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::InferFactResult;

impl Runtime {
    // Infer each atomic conjunct of an already-stored and-fact.
    // Example: stored `a $in {x R: x > 0} and b = cart(R, R)` runs atomic stages on both sides.
    pub(crate) fn infer_and_fact(
        &mut self,
        and_fact: &AndFact,
    ) -> RuntimeResult<InferFactResult> {
        for atomic in &and_fact.facts {
            self.infer_atomic_fact(atomic)?;
        }
        Ok(InferFactResult::Empty)
    }
}
