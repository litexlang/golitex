use crate::launch_command::OutputLanguage;

/// Localized builtin-rule text for Normal JSON.
///
/// `rule_id` is for Rust tests / internal matching only — Normal JSON prints
/// `rule_name` + `message`, not `rule_id`.
pub struct BuiltinRuleText {
    pub rule_id: &'static str,
    pub rule_name: String,
    pub message: String,
}

/// Temporary text when a dedicated explain file is not written yet.
/// `rule_name` stays the English rule id until a real translation exists.
pub fn fallback_builtin_rule_text(rule_id: &'static str, lang: OutputLanguage) -> BuiltinRuleText {
    let (rule_name, message) = match lang {
        OutputLanguage::English => (
            rule_id.to_string(),
            format!("Verified by builtin rule `{rule_id}`"),
        ),
        OutputLanguage::Chinese => (
            rule_id.to_string(),
            format!("由内置规则 `{rule_id}` 验证"),
        ),
    };
    BuiltinRuleText {
        rule_id,
        rule_name,
        message,
    }
}
