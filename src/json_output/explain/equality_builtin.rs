//! Dispatch localized text for EqualitySearchProofByBuiltinRule.
//!
//! Only Calculation has dedicated copy for now; other variants use fallback
//! English rule ids until their explain files are filled in.

use super::equality_calculation::explain_calculation;
use super::fallback::{fallback_builtin_rule_text, BuiltinRuleText};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::EqualitySearchProofByBuiltinRule;
use crate::launch_command::OutputLanguage;

pub fn explain_equality_builtin_rule(
    rule: &EqualitySearchProofByBuiltinRule,
    lang: OutputLanguage,
) -> BuiltinRuleText {
    match rule {
        EqualitySearchProofByBuiltinRule::Calculation(proof) => explain_calculation(proof, lang),
        EqualitySearchProofByBuiltinRule::EqualFromKnownDifferenceZero(_) => {
            fallback_builtin_rule_text("EqualFromKnownDifferenceZero", lang)
        }
        // Remaining equality builtins: add dedicated explain files over time.
        _ => fallback_builtin_rule_text("EqualityBuiltin", lang),
    }
}
