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
/// Existing English/Chinese fallback copy is retained for compatibility.
/// Other locales identify the rule explicitly in the selected language.
pub fn fallback_builtin_rule_text(rule_id: &'static str, lang: OutputLanguage) -> BuiltinRuleText {
    let rule_name = humanize_rule_id(rule_id);
    let message = format!("Verified by the `{rule_id}` builtin rule");
    let (rule_name, message) = match lang {
        OutputLanguage::English | OutputLanguage::Chinese => (rule_name, message),
        OutputLanguage::ChineseTraditional => (
            format!("內建規則 {rule_id}"),
            format!("由內建規則 `{rule_id}` 驗證"),
        ),
        OutputLanguage::French => (
            format!("Règle intégrée {rule_id}"),
            format!("Vérifié par la règle intégrée `{rule_id}`"),
        ),
        OutputLanguage::Russian => (
            format!("Встроенное правило {rule_id}"),
            format!("Проверено встроенным правилом `{rule_id}`"),
        ),
        OutputLanguage::Spanish => (
            format!("Regla incorporada {rule_id}"),
            format!("Verificado por la regla incorporada `{rule_id}`"),
        ),
        OutputLanguage::Arabic => (
            format!("قاعدة مدمجة {rule_id}"),
            format!("تم التحقق بالقاعدة المدمجة `{rule_id}`"),
        ),
        OutputLanguage::Japanese => (
            format!("組み込み規則 {rule_id}"),
            format!("組み込み規則 `{rule_id}` で検証しました"),
        ),
        OutputLanguage::Korean => (
            format!("내장 규칙 {rule_id}"),
            format!("내장 규칙 `{rule_id}`으로 검증했습니다"),
        ),
        OutputLanguage::Vietnamese => (
            format!("Quy tắc tích hợp {rule_id}"),
            format!("Đã kiểm chứng bằng quy tắc tích hợp `{rule_id}`"),
        ),
    };
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
