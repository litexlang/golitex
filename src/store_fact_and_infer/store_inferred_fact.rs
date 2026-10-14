use crate::prelude::*;

impl Runtime {
    // A named infer rule owns formation and truth of this conclusion.
    // Only its direct store is recorded; no WD cache write and no further infer.
    // Infer conclusions are fixed translation patterns — do not call
    // remember_formed_atomic_subjects here (that belongs to user/store paths).
    pub(crate) fn store_inferred_fact(
        &mut self,
        fact: &Fact,
    ) -> RuntimeResult<crate::store_fact_and_infer::StoreInferredFactResult> {
        let store = self.store_fact(fact)?;
        Ok(crate::store_fact_and_infer::StoreInferredFactResult { store })
    }
}
