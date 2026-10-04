/// Localized builtin-rule name and explanation for Normal JSON.
/// The owning proof type or enum variant identifies the rule.
pub struct BuiltinRuleText {
    pub rule_name: String,
    pub message: String,
}

pub(super) fn text(rule_name: &str, message: &str) -> BuiltinRuleText {
    BuiltinRuleText {
        rule_name: rule_name.to_string(),
        message: message.to_string(),
    }
}
