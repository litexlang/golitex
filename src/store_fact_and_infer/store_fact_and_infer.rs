use super::store_fact_and_infer_result::StoreFactAndInferResult;
use crate::ast::fact::Fact;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Store by fact shape, then run local inference on that fact.
    // Callers already verified the seed fact; this path is not open-ended proof search.
    // Infer may only generate extra facts (see store_inferred_fact_and_infer for those).
    pub fn store_fact_and_infer(&mut self, fact: &Fact) -> RuntimeResult<StoreFactAndInferResult> {
        let store = self.store_fact(fact)?;
        let infer = self.infer_fact(fact)?;
        Ok(StoreFactAndInferResult { store, infer })
    }
}
