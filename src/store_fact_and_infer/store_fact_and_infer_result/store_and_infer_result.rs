use crate::ast::fact::AtomicFact;
use crate::runtime::FactId;

use super::{InferFactResult, StoreFactResult};

// Store first; inference is absent in inferred-fact formation scopes.
pub struct StoreFactAndInferResult {
    pub store: StoreFactResult,
    pub infer: Option<InferFactResult>,
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
        if let Some(infer) = &self.infer {
            ids.extend(infer.stored_fact_ids());
        }
        ids
    }
}
