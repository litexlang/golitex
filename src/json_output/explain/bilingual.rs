//! Shared bilingual helper for stmt why text (not builtin rules).

/// Legacy helper for callers that supply only English/Chinese copy.
/// Other locales use the supplied English copy; localized output uses the
/// exhaustive statement/rule explainers instead of this compatibility helper.
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
        OutputLanguage::ChineseTraditional => (en_name.to_string(), en_message.to_string()),
        OutputLanguage::French => (en_name.to_string(), en_message.to_string()),
        OutputLanguage::Russian => (en_name.to_string(), en_message.to_string()),
        OutputLanguage::Spanish => (en_name.to_string(), en_message.to_string()),
        OutputLanguage::Arabic => (en_name.to_string(), en_message.to_string()),
        OutputLanguage::Japanese => (en_name.to_string(), en_message.to_string()),
        OutputLanguage::Korean => (en_name.to_string(), en_message.to_string()),
        OutputLanguage::Vietnamese => (en_name.to_string(), en_message.to_string()),

        OutputLanguage::Chinese => (
            zh_name.unwrap_or(en_name).to_string(),
            zh_message.unwrap_or(en_message).to_string(),
        ),
    }
}
