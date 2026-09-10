//! Composition root for Environment-owned fact indexes.

use crate::prelude::*;

/// Canonical stored facts and the search indexes derived from them.
#[derive(Clone)]
pub struct KnownFactMemory {
    pub known_equality: KnownEquality,
    pub atomic: AtomicFactMemory,
    pub special_set_relations: SpecialSetRelationMemory,
    pub quantified: QuantifiedFactMemory,
    pub forall_conclusions: KnownForallFactMemory,
    pub stored_facts: EnvironmentStoredFactStore,
}

impl KnownFactMemory {
    pub fn new() -> Self {
        Self {
            known_equality: KnownEquality::new(),
            atomic: AtomicFactMemory::new(),
            special_set_relations: SpecialSetRelationMemory::new(),
            quantified: QuantifiedFactMemory::new(),
            forall_conclusions: KnownForallFactMemory::new(),
            stored_facts: EnvironmentStoredFactStore::default(),
        }
    }

    /// Merge every fact owner except equality, which Environment replays
    /// through `store_equality` so derived equalities remain consistent.
    pub fn merge_non_equality_from(&mut self, child: Self) -> Result<(), RuntimeError> {
        let KnownFactMemory {
            known_equality: _,
            atomic,
            special_set_relations: set_relations,
            quantified,
            forall_conclusions,
            stored_facts,
        } = child;
        self.atomic.merge_from(atomic);
        self.special_set_relations.merge_from(set_relations);
        self.quantified.merge_from(quantified);
        self.forall_conclusions.merge_from(forall_conclusions);
        self.stored_facts.merge_from(stored_facts)
    }
}
