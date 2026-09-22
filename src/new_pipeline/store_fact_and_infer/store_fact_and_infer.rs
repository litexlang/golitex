use super::store_fact_and_infer_result::{merge_store_and_infer, StoreFactAndInferResult};
use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Store by fact shape, then run local inference on that fact.
    // Callers verify first; this path is not open-ended proof search.
    pub fn store_fact_and_infer(&mut self, fact: &Fact) -> RuntimeResult<StoreFactAndInferResult> {
        let stored = self.store_fact(fact)?;
        let inferred = self.infer_fact(fact)?;
        Ok(merge_store_and_infer(stored, inferred))
    }
}
