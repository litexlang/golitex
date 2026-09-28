use crate::ast::fact::AtomicFact;
use crate::runtime::FactId;

use super::{InferFactResult, StoreFactResult};

// Option A: always store then infer as two explicit stages.
pub struct StoreFactAndInferResult {
    pub store: StoreFactResult,
    pub infer: InferFactResult,
}

impl StoreFactAndInferResult {
    pub fn primary_fact_id(&self) -> FactId {
        self.store.primary_fact_id()
    }

    pub fn atomic_components(&self) -> Vec<(FactId, AtomicFact)> {
        self.store.atomic_components()
    }

    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        let mut ids = self.store.stored_fact_ids();
        ids.extend(self.infer.stored_fact_ids());
        ids
    }
}
