//! Shared bilingual helper: English is complete; Chinese may fall back to English
//! until a translation is filled in.

use super::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;

/// Build builtin text. Missing Chinese copy intentionally reuses English so
/// `-lang zh` stays readable while translations catch up.
pub fn bilingual_builtin(
    rule_id: &'static str,
    en_name: &'static str,
    en_message: &'static str,
    zh_name: Option<&'static str>,
    zh_message: Option<&'static str>,
    lang: OutputLanguage,
) -> BuiltinRuleText {
    let (rule_name, message) = match lang {
        OutputLanguage::English => (en_name, en_message),
        OutputLanguage::Chinese => (
            zh_name.unwrap_or(en_name),
            zh_message.unwrap_or(en_message),
        ),
    };
    BuiltinRuleText {
        rule_id,
        rule_name: rule_name.to_string(),
        message: message.to_string(),
    }
}

/// Same policy for stmt why-text pairs.
pub fn bilingual_stmt_pair(
    en_name: &'static str,
    en_message: &'static str,
    zh_name: Option<&'static str>,
    zh_message: Option<&'static str>,
    lang: OutputLanguage,
) -> (String, String) {
    match lang {
        OutputLanguage::English => (en_name.to_string(), en_message.to_string()),
        OutputLanguage::Chinese => (
            zh_name.unwrap_or(en_name).to_string(),
            zh_message.unwrap_or(en_message).to_string(),
        ),
    }
}
