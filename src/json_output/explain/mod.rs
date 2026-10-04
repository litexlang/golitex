//! Localized explanations for JSON output.
//!
//! Keep all localized copy here. Verify/exec IR types stay language-free;
//! projection calls into this module with `OutputLanguage` from LaunchCommand.
//!
//! Policy: every Normal surface has localized `rule_name` / `message`,
//! including every atomic builtin leaf (no family-level stubs).

pub mod atomic_builtin_rule;
pub mod bilingual;
pub mod equality_builtin_rule;
pub mod fallback;
pub mod searched_proof_why;
pub mod stmt_why;

pub use bilingual::bilingual_stmt_pair;
pub use fallback::{fallback_builtin_rule_text, BuiltinRuleText};
pub use searched_proof_why::explain_searched_proof_why;
pub use stmt_why::{explain_compound_fact_why, explain_define_obj_why, explain_stmt_kind};
