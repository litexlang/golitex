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

/// Temporary text when a dedicated explain entry is not written yet.
/// English uses a humanized rule id; Chinese currently reuses English
/// (EN-first policy — fill translations later without changing call sites).
pub fn fallback_builtin_rule_text(rule_id: &'static str, lang: OutputLanguage) -> BuiltinRuleText {
    let rule_name = humanize_rule_id(rule_id);
    let message = format!("Verified by the `{rule_id}` builtin rule");
    let _ = lang; // keep signature for bilingual call sites
    BuiltinRuleText {
        rule_id,
        rule_name,
        message,
    }
}

fn humanize_rule_id(rule_id: &str) -> String {
    let mut out = String::new();
    for (i, ch) in rule_id.chars().enumerate() {
        if i > 0 && ch.is_ascii_uppercase() {
            out.push(' ');
        }
        out.push(ch);
    }
    out
}
