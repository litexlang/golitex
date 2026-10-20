use crate::ast::fact::AtomicFact;
use crate::runtime::{FactId, WellDefinednessId};

use super::StoreFactResult;
use crate::store_fact_and_infer::InferResult;

// Store → register formed atomic subjects → infer.
pub struct StoreFactAndInferResult {
    pub store: StoreFactResult,
    pub formed_subjects: Vec<FormedAtomicSubject>,
    pub infer: Option<InferResult>,
}

/// A registration actually created by this store, at the original argument index.
/// The construction proof belongs to the enclosing verify/assumption producer.
pub struct FormedAtomicSubject {
    pub argument_index: usize,
    pub wd_id: WellDefinednessId,
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
