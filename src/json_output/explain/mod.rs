//! Localized explanations for JSON output.
//!
//! Keep all Chinese/English copy here. Verify/exec IR types stay language-free;
//! projection calls into this module with `OutputLanguage` from LaunchCommand.

pub mod atomic_common;
pub mod equality_builtin;
pub mod equality_calculation;
pub mod fallback;
pub mod stmt_why;

pub use atomic_common::explain_atomic_rule_id;
pub use equality_builtin::explain_equality_builtin_rule;
pub use equality_calculation::explain_calculation;
pub use fallback::{fallback_builtin_rule_text, BuiltinRuleText};
pub use stmt_why::{explain_compound_fact_why, explain_define_obj_why};
