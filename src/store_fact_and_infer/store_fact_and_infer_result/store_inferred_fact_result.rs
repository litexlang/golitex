use crate::execute::execute_fact_stmt::FactWellDefinedProof;
use crate::prelude::*;

/// An inferred conclusion is formed, then indexed without further inference.
pub struct StoreInferredFactResult {
    pub well_defined: FactWellDefinedProof,
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
