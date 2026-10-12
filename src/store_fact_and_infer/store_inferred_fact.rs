use crate::prelude::*;

impl Runtime {
    // A named infer rule owns formation and truth of this conclusion.
    // Only its direct store is recorded; no WD or inference is repeated here.
    pub(crate) fn store_inferred_fact(
        &mut self,
        fact: &Fact,
    ) -> RuntimeResult<crate::store_fact_and_infer::StoreInferredFactResult> {
        let store = self.store_fact(fact)?;
        self.remember_formed_atomic_subjects(fact);
        Ok(crate::store_fact_and_infer::StoreInferredFactResult { store })
    }
}
