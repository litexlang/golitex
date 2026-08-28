//! Composition root for Environment-owned fact indexes.

use crate::prelude::*;

/// Canonical stored facts and the search indexes derived from them.
#[derive(Clone)]
pub struct EnvironmentFactStore {
    pub known_equality: KnownEquality,
    pub atomic: AtomicFactIndex,
    pub set_relations: SetRelationIndex,
    pub quantified: QuantifiedFactIndex,
    pub forall_conclusions: ForallConclusionIndex,
    pub stored_facts: EnvironmentStoredFactStore,
}

impl EnvironmentFactStore {
    pub fn new() -> Self {
        Self {
            known_equality: KnownEquality::new(),
            atomic: AtomicFactIndex::new(),
            set_relations: SetRelationIndex::new(),
            quantified: QuantifiedFactIndex::new(),
            forall_conclusions: ForallConclusionIndex::new(),
            stored_facts: EnvironmentStoredFactStore::default(),
        }
    }

    /// Merge every fact owner except equality, which Environment replays
    /// through `store_equality` so derived equalities remain consistent.
    pub fn merge_non_equality_from(&mut self, child: Self) -> Result<(), RuntimeError> {
        let EnvironmentFactStore {
            known_equality: _,
            atomic,
            set_relations,
            quantified,
            forall_conclusions,
            stored_facts,
        } = child;
        self.atomic.merge_from(atomic);
        self.set_relations.merge_from(set_relations);
        self.quantified.merge_from(quantified);
        self.forall_conclusions.merge_from(forall_conclusions);
        self.stored_facts.merge_from(stored_facts)
    }
}
