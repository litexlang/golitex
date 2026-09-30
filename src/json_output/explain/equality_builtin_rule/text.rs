use crate::json_output::explain::fallback::BuiltinRuleText;

pub(super) fn text(
    rule_id: &'static str,
    rule_name: &'static str,
    message: &'static str,
) -> BuiltinRuleText {
    BuiltinRuleText {
        rule_id,
        rule_name: rule_name.to_string(),
        message: message.to_string()
    }
}
