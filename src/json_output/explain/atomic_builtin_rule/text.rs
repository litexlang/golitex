use crate::json_output::explain::fallback::{fallback_builtin_rule_text, BuiltinRuleText};
use crate::launch_command::OutputLanguage;

pub(super) fn family_fallback(rule_id: &'static str, lang: OutputLanguage) -> BuiltinRuleText {
    fallback_builtin_rule_text(rule_id, lang)
}

pub(super) fn text(
    rule_id: &'static str,
    rule_name: &'static str,
    message: &'static str,
) -> BuiltinRuleText {
    BuiltinRuleText {
        rule_id,
        rule_name: rule_name.to_string(),
        message: message.to_string(),
    }
}
