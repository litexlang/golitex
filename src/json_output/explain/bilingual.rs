//! Shared bilingual helper for stmt why text (not builtin rules).

/// English is complete; Chinese may fall back to English until filled.
pub fn bilingual_stmt_pair(
    en_name: &'static str,
    en_message: &'static str,
    zh_name: Option<&'static str>,
    zh_message: Option<&'static str>,
    lang: crate::launch_command::OutputLanguage,
) -> (String, String) {
    use crate::launch_command::OutputLanguage;
    match lang {
        OutputLanguage::English => (en_name.to_string(), en_message.to_string()),
        OutputLanguage::Chinese => (
            zh_name.unwrap_or(en_name).to_string(),
            zh_message.unwrap_or(en_message).to_string(),
        ),
    }
}
