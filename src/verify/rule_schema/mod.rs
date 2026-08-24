mod canonical_match;
mod compile;
mod matcher;
mod source;
mod substitution;

pub use canonical_match::{
    atomic_fact_head, canonical_obj_view, AtomicFactHead, CanonicalMatchError,
};
pub use compile::compile_local_builtin_schema;
pub use matcher::{canonical_objs_equal, match_conclusion, MatchLimits};
pub use source::{CompiledRuleSchema, RuleFingerprint, RuleId, RuleSourceRef, RuleVariable};
pub use substitution::RuleSubstitution;
