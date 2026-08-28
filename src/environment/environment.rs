use crate::prelude::*;

/// The mutable mathematical context for a runtime environment.
///
/// `Environment` is intentionally broad: it is the physical storage for the
/// checked world that later statements can reuse. The fields are grouped by
/// role rather than by proof rule:
///
/// - definition tables for identifiers, predicates, algorithms, structs,
///   templates, theorems, and strategies;
/// - known fact indexes for equality, atomic, existential, and disjunctive
///   facts;
/// - known `forall` indexes, including argument-shape indexes for faster
///   matching against later goals;
/// - derived object-shape caches for tuples, carts, finite sequences,
///   matrices, object values, set builders, and function-set information;
/// - verification caches for well-defined objects and already-known facts.
#[derive(Clone)]
pub struct Environment {
    pub definitions: EnvironmentDefinitionRegistry,
    pub facts: EnvironmentFactStore,
    pub objects: EnvironmentObjectKnowledgeStore,
    pub predicate_algebraic_properties: EnvironmentPredicateAlgebraicPropertyStore,
    pub caches: EnvironmentVerificationCache,
}

impl Environment {
    pub fn new_empty_env() -> Self {
        Environment {
            definitions: EnvironmentDefinitionRegistry::new(),
            facts: EnvironmentFactStore::new(),
            objects: EnvironmentObjectKnowledgeStore::new(),
            predicate_algebraic_properties: EnvironmentPredicateAlgebraicPropertyStore::new(),
            caches: EnvironmentVerificationCache::new(),
        }
    }
}
