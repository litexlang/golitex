use crate::prelude::*;

impl Runtime {
    pub(super) fn store_builtin_definition_consequences(
        &mut self,
        fact: &AtomicFact,
        _verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<crate::store_fact_and_infer::StoreInferredFactResult>> {
        let mut derived = Vec::new();
        for consequence in self.builtin_atomic_definition_consequences(fact) {
            derived.push(self.store_inferred_fact(&consequence)?);
        }
        Ok(derived)
    }
}
