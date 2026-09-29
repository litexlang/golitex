//! Localized explanations for JSON output.
//!
//! Keep all Chinese/English copy here. Verify/exec IR types stay language-free;
//! projection calls into this module with `OutputLanguage` from LaunchCommand.
//!
//! Policy (current phase): finish **English** `rule_name` / `message` for every
//! surface. Chinese slots stay in the API (`bilingual_*` / `OutputLanguage`)
//! and fall back to English until filled.

pub mod atomic_builtin_rule;
pub mod bilingual;
pub mod equality_builtin;
pub mod equality_calculation;
pub mod fallback;
pub mod stmt_why;

pub use bilingual::bilingual_stmt_pair;
pub use equality_builtin::explain_equality_builtin_rule;
pub use equality_calculation::explain_calculation;
pub use fallback::{fallback_builtin_rule_text, BuiltinRuleText};
pub use stmt_why::{explain_compound_fact_why, explain_define_obj_why, explain_stmt_kind};
