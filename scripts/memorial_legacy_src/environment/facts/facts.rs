//! Composition root for Environment-owned fact indexes.

use crate::prelude::*;

/// Canonical stored facts and the search indexes derived from them.
#[derive(Clone)]
pub struct KnownFactMemory {
    pub known_equality: KnownEquality,
    pub known_atomic_except_equality_facts: AtomicExceptEqualityFactMemory,
    pub special_set_relations: SpecialSetRelationMemory,
    pub known_exist: ExistFactMemory,
    pub known_or: OrFactMemory,
    pub forall_conclusions: KnownForallFactMemory,
    pub stored_facts: EnvironmentStoredFactStore,
}

impl KnownFactMemory {
    pub fn new() -> Self {
        Self {
            known_equality: KnownEquality::new(),
            known_atomic_except_equality_facts: AtomicExceptEqualityFactMemory::new(),
            special_set_relations: SpecialSetRelationMemory::new(),
            known_exist: ExistFactMemory::new(),
            known_or: OrFactMemory::new(),
            forall_conclusions: KnownForallFactMemory::new(),
            stored_facts: EnvironmentStoredFactStore::default(),
        }
    }

    /// Merge every fact owner except equality, which Environment replays
    /// through `store_equality` so derived equalities remain consistent.
    pub fn merge_non_equality_from(&mut self, child: Self) -> Result<(), RuntimeError> {
        let KnownFactMemory {
            known_equality: _,
            known_atomic_except_equality_facts,
            special_set_relations: set_relations,
            known_exist,
            known_or,
            forall_conclusions,
            stored_facts,
        } = child;
        self.known_atomic_except_equality_facts
            .merge_from(known_atomic_except_equality_facts);
        self.special_set_relations.merge_from(set_relations);
        self.known_exist.merge_from(known_exist);
        self.known_or.merge_from(known_or);
        self.forall_conclusions.merge_from(forall_conclusions);
        self.stored_facts.merge_from(stored_facts)
    }
}
