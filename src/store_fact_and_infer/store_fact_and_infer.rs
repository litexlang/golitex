use super::store_fact_and_infer_result::StoreFactAndInferResult;
use crate::ast::fact::Fact;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Store by fact shape, then run local inference on that fact.
    // Callers already verified the seed fact; this path is not open-ended proof search.
    // Infer may only generate extra facts (see store_inferred_fact for those).
    pub fn store_fact_and_infer(
        &mut self,
        fact: &Fact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<StoreFactAndInferResult> {
        let store = self.store_fact(fact)?;
        self.remember_formed_atomic_subjects(fact);
        let infer = if verify_state.allows_inference() {
            Some(self.infer_fact(fact, verify_state)?)
        } else {
            None
        };
        Ok(StoreFactAndInferResult { store, infer })
    }
}

#[cfg(test)]
#[path = "../../tests/unit/execute/inferred_store_only/tests.rs"]
mod inferred_store_only_tests;
