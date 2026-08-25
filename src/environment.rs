mod definitions;
mod display;
mod facts;
mod merge;
mod object_knowledge;
mod predicates;
mod verification_cache;
mod well_definedness_environment_delta;

pub use definitions::EnvironmentDefinitionRegistry;
pub use facts::equality_linear_derive;
pub use facts::{
    forall_argument_shape, AtomicFactIndex, CachedKnownFact, EnvironmentFactStore,
    EnvironmentStoredFactStore, ForallArgumentShape, ForallConclusionIndex, KnownEquality,
    KnownEqualityProofStep, QuantifiedFactIndex, SetRelationIndex, StoredFactRecord,
    StoredForallConclusionReference,
};
pub use object_knowledge::{
    EnvironmentObjectKnowledge, EnvironmentObjectKnowledgeStore, KnownFnInfo, KnownObjValue,
};
pub use predicates::{EnvironmentPredicateProperties, EnvironmentPredicatePropertyStore};
pub use verification_cache::EnvironmentVerificationCache;
pub use well_definedness_environment_delta::WellDefinednessEnvironmentDelta;

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
    pub predicate_properties: EnvironmentPredicatePropertyStore,
    pub caches: EnvironmentVerificationCache,
}

impl Environment {
    pub fn new_empty_env() -> Self {
        Environment {
            definitions: EnvironmentDefinitionRegistry::new(),
            facts: EnvironmentFactStore::new(),
            objects: EnvironmentObjectKnowledgeStore::new(),
            predicate_properties: EnvironmentPredicatePropertyStore::new(),
            caches: EnvironmentVerificationCache::new(),
        }
    }
}
