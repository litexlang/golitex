use crate::prelude::*;

impl Runtime {
    // A named infer rule owns formation and truth of this conclusion.
    // Only its direct store is recorded; no further infer is repeated here.
    // The inferred conclusion's atomic subjects are formed by the named rule,
    // so cache their direct WD just as the checked user-fact path does. Without
    // this, later congruence/citation steps cannot reuse the inferred
    // equality's endpoint objects under a restricted premise state.
    pub(crate) fn store_inferred_fact(
        &mut self,
        fact: &Fact,
    ) -> RuntimeResult<crate::store_fact_and_infer::StoreInferredFactResult> {
        let store = self.store_fact(fact)?;
        self.remember_formed_atomic_subjects(fact);
        Ok(crate::store_fact_and_infer::StoreInferredFactResult { store })
    }
}
