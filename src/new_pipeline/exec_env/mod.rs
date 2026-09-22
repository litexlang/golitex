pub mod exec_env;
pub mod exist_fact_index_key;
pub mod forall_conclusion_index_key;
pub mod known_fact_memory;
pub mod known_forall_conclusion_memory;
// Temp child → merge on Success / discard on Failed. See merge_exec_env.rs.
mod merge_exec_env;
pub mod or_fact_index_key;

pub use exec_env::{
    ExecEnv, SpecialObjectPropertyByDefinition, StoredIdentifierDefinition,
};
pub use exist_fact_index_key::{
    exist_fact_alpha_match_key, exist_fact_can_prove_goal, exist_fact_index_key,
    exist_fact_known_lookup_keys, plain_exist_fact, ExistFactIndexKey, ExistFactKind,
    QuantifierFreeShape,
};
pub use known_fact_memory::{
    AtomicExceptEqualityFactMemory, ExistFactMemory, maybe_index_known_closed_numeric_equal,
    KnownEqualToObjWithFreeParamsMemory, KnownEqualToObjWithFreeParamsShape,
    KnownEquivalenceClassMemory, KnownFactMemory, ObjIR, OrFactMemory,
};
pub use known_forall_conclusion_memory::{
    atomic_at_forall_location, exist_at_forall_location, or_at_forall_location, ForallConclusionCite,
    KnownForallConclusionMemory,
};
pub use or_fact_index_key::{AtomicAndChainFactShape, AtomicFactShape, OrFactIndexKey};
