use crate::prelude::*;
use crate::verify_rewrite::WellDefinednessId2;
use std::collections::HashMap;

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
/// - persistent infer-rule firing deduplication. Returned WD and truth proofs
///   belong to `VerifyState` and `VerifyFactResult`, never this environment;
/// - object well-definedness identities whose proof details remain in Results.
#[derive(Clone)]
pub struct ExecEnv {
    /// Definitions and symbol identities for declarations visible to later
    /// statements.
    pub definitions: DefinitionMemory,

    /// Stored facts and indexes used to find mathematical evidence.
    pub facts: KnownFactMemory,

    /// Known object values and shape facets keyed by canonical object string.
    pub object_properties: ObjectPropertyMemory,

    /// Algebraic properties registered for predicates, such as transitivity,
    /// symmetry, reflexivity, and antisymmetry.
    pub prop_algebraic_properties: PropAlgebraicPropertyMemory,

    /// Environment-scoped keys that deduplicate persistent infer-rule firings.
    pub known_facts_cache: KnownFactsCache,

    /// Objects whose well-definedness has been established in this environment.
    /// The proof itself remains owned by the corresponding Result.
    pub well_defined_objects: HashMap<ObjString, WellDefinednessId2>,
}

impl ExecEnv {
    pub fn new_empty_env() -> Self {
        ExecEnv {
            definitions: DefinitionMemory::new(),
            facts: KnownFactMemory::new(),
            object_properties: ObjectPropertyMemory::new(),
            prop_algebraic_properties: PropAlgebraicPropertyMemory::new(),
            known_facts_cache: KnownFactsCache::new(),
            well_defined_objects: HashMap::new(),
        }
    }
}
