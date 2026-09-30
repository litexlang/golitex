//! Localized explanations for JSON output.
//!
//! Keep all Chinese/English copy here. Verify/exec IR types stay language-free;
//! projection calls into this module with `OutputLanguage` from LaunchCommand.
//!
//! Policy: every Normal surface should have English and Chinese `rule_name` /
//! `message`. Family-level stubs stay until leaf modules are wired.

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
