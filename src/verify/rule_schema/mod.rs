mod canonical_match;
mod compile;
mod matcher;
mod source;
mod substitution;

pub(crate) use canonical_match::{
    atomic_fact_head, canonical_obj_view, AtomicFactHead, CanonicalMatchError,
};
pub(crate) use compile::compile_local_builtin_schema;
pub(crate) use matcher::{
    canonical_atomic_facts_equal, canonical_objs_equal, match_conclusion, MatchLimits,
};
pub use source::{CompiledRuleSchema, RuleFingerprint, RuleId, RuleSourceRef, RuleVariable};
pub use substitution::RuleSubstitution;
