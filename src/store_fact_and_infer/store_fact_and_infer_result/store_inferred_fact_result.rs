use crate::prelude::*;

/// The enclosing named infer rule certifies this conclusion and its construction.
/// Storage does not repeat verification or start another inference pass.
pub struct StoreInferredFactResult {
    pub store: StoreFactResult,
}

impl StoreInferredFactResult {
    pub fn primary_fact_id(&self) -> FactId {
        self.store.primary_fact_id()
    }

    pub fn atomic_components(&self) -> Vec<(FactId, AtomicFact)> {
        self.store.atomic_components()
    }

    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        self.store.stored_fact_ids()
    }
}
