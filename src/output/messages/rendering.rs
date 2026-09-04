//! Recursive JSON message translation and language-specific templates.

use super::catalogs::*;
use super::*;

pub fn translate_json_messages(runtime: &Runtime, value: JsonValue) -> JsonValue {
    translate_json_messages_for_language(runtime.execution_options.output_language(), value)
}

fn translate_json_messages_for_language(
    output_language: OutputLanguage,
    value: JsonValue,
) -> JsonValue {
    if output_language == OutputLanguage::English {
        return value;
    }
    translate_json_messages_for_key(output_language, None, value)
}

fn translate_json_messages_for_key(
    output_language: OutputLanguage,
    parent_key: Option<&str>,
    value: JsonValue,
) -> JsonValue {
    match value {
        JsonValue::JsonString(text) => JsonValue::JsonString(translate_json_string_message(
            output_language,
            parent_key,
            text,
        )),
        JsonValue::Array(items) => JsonValue::Array(
            items
                .into_iter()
                .map(|item| translate_json_messages_for_key(output_language, parent_key, item))
                .collect::<Vec<_>>(),
        ),
        JsonValue::Object(fields) => {
            if matches!(parent_key, Some("instantiation")) {
                return JsonValue::Object(fields);
            }
            let mut translated_fields = Vec::new();
            for (key, field_value) in fields {
                let translated_value = translate_json_messages_for_key(
                    output_language,
                    Some(key.as_str()),
                    field_value,
                );
                translated_fields.push((key, translated_value));
            }
            JsonValue::Object(translated_fields)
        }
        JsonValue::RawJson(_) => value,
        JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_) => value,
    }
}

fn translate_json_string_message(
    output_language: OutputLanguage,
    parent_key: Option<&str>,
    text: String,
) -> String {
    if output_language == OutputLanguage::English || should_preserve_string_value(parent_key) {
        return text;
    }
    translate_text(output_language, text.as_str()).unwrap_or(text)
}

fn should_preserve_string_value(parent_key: Option<&str>) -> bool {
    matches!(
        parent_key,
        Some("statement")
            | Some("fact")
            | Some("facts")
            | Some("inferred_facts")
            | Some("cited_statement")
            | Some("failed_goal")
            | Some("verify_what")
            | Some("goal")
            | Some("body")
            | Some("branches")
            | Some("requirements")
            | Some("assumptions")
            | Some("parameters")
            | Some("name")
            | Some("label")
            | Some("path")
            | Some("trace")
            | Some("runner")
            | Some("runner_version")
    )
}

fn translate_text(output_language: OutputLanguage, text: &str) -> Option<String> {
    let exact = match output_language {
        OutputLanguage::English => None,
        OutputLanguage::SimplifiedChinese => find_translation(ZH_TEXTS, text),
        OutputLanguage::TraditionalChinese => find_translation(ZH_HANT_TEXTS, text),
        OutputLanguage::Japanese => find_translation(JA_TEXTS, text),
        OutputLanguage::Korean => find_translation(KO_TEXTS, text),
        OutputLanguage::Spanish => find_translation(ES_TEXTS, text),
        OutputLanguage::French => find_translation(FR_TEXTS, text),
        OutputLanguage::German => find_translation(DE_TEXTS, text),
        OutputLanguage::Portuguese => find_translation(PT_TEXTS, text),
        OutputLanguage::Russian => find_translation(RU_TEXTS, text),
        OutputLanguage::Arabic => find_translation(AR_TEXTS, text),
        OutputLanguage::Hindi => find_translation(HI_TEXTS, text),
        OutputLanguage::Vietnamese => find_translation(VI_TEXTS, text),
        OutputLanguage::Indonesian => find_translation(ID_TEXTS, text),
    };
    if exact.is_some() {
        return exact;
    }

    if let Some(rest) = text.strip_prefix("cite ") {
        let translated_rest =
            translate_text(output_language, rest).unwrap_or_else(|| rest.to_string());
        return Some(cite_template(output_language, translated_rest.as_str()));
    }

    if let Some(rule) = text
        .strip_prefix("inferred by builtin rule `")
        .and_then(|s| s.strip_suffix('`'))
    {
        return Some(inferred_by_builtin_rule_template(output_language, rule));
    }

    if let Some(rule) = text
        .strip_prefix("inferred by infer rule `")
        .and_then(|s| s.strip_suffix('`'))
    {
        return Some(inferred_by_infer_rule_template(output_language, rule));
    }

    if let Some(name) = text
        .strip_prefix("prop with meaning `")
        .and_then(|s| s.strip_suffix("` (param constraints and definition clauses)"))
    {
        return Some(prop_meaning_template(output_language, name));
    }

    None
}

fn find_translation(entries: &[(&str, &str)], text: &str) -> Option<String> {
    for (source, target) in entries {
        if *source == text {
            return Some((*target).to_string());
        }
    }
    None
}

fn cite_template(output_language: OutputLanguage, rest: &str) -> String {
    match output_language {
        OutputLanguage::English => format!("cite {}", rest),
        OutputLanguage::SimplifiedChinese => format!("引用{}", rest),
        OutputLanguage::TraditionalChinese => format!("引用{}", rest),
        OutputLanguage::Japanese => format!("{}を引用", rest),
        OutputLanguage::Korean => format!("{} 인용", rest),
        OutputLanguage::Spanish => format!("cita {}", rest),
        OutputLanguage::French => format!("citer {}", rest),
        OutputLanguage::German => format!("zitiere {}", rest),
        OutputLanguage::Portuguese => format!("citar {}", rest),
        OutputLanguage::Russian => format!("цитировать {}", rest),
        OutputLanguage::Arabic => format!("اقتباس {}", rest),
        OutputLanguage::Hindi => format!("{} का उद्धरण", rest),
        OutputLanguage::Vietnamese => format!("trích dẫn {}", rest),
        OutputLanguage::Indonesian => format!("kutip {}", rest),
    }
}

fn inferred_by_builtin_rule_template(output_language: OutputLanguage, rule: &str) -> String {
    match output_language {
        OutputLanguage::English => format!("inferred by builtin rule `{}`", rule),
        OutputLanguage::SimplifiedChinese => format!("由内置规则 `{}` 推出", rule),
        OutputLanguage::TraditionalChinese => format!("由內建規則 `{}` 推出", rule),
        OutputLanguage::Japanese => format!("組み込みルール `{}` により導出", rule),
        OutputLanguage::Korean => format!("내장 규칙 `{}`에서 추론됨", rule),
        OutputLanguage::Spanish => format!("inferido por la regla integrada `{}`", rule),
        OutputLanguage::French => format!("déduit par la règle intégrée `{}`", rule),
        OutputLanguage::German => format!("durch eingebaute Regel `{}` hergeleitet", rule),
        OutputLanguage::Portuguese => format!("inferido pela regra interna `{}`", rule),
        OutputLanguage::Russian => format!("выведено встроенным правилом `{}`", rule),
        OutputLanguage::Arabic => format!("مستنتج من القاعدة المضمنة `{}`", rule),
        OutputLanguage::Hindi => format!("आंतरिक नियम `{}` से निष्कर्षित", rule),
        OutputLanguage::Vietnamese => format!("suy ra bởi quy tắc tích hợp `{}`", rule),
        OutputLanguage::Indonesian => format!("disimpulkan oleh aturan bawaan `{}`", rule),
    }
}

fn inferred_by_infer_rule_template(output_language: OutputLanguage, rule: &str) -> String {
    match output_language {
        OutputLanguage::English => format!("inferred by infer rule `{}`", rule),
        OutputLanguage::SimplifiedChinese => format!("由推理规则 `{}` 推出", rule),
        OutputLanguage::TraditionalChinese => format!("由推理規則 `{}` 推出", rule),
        OutputLanguage::Japanese => format!("推論ルール `{}` により導出", rule),
        OutputLanguage::Korean => format!("추론 규칙 `{}`에서 추론됨", rule),
        OutputLanguage::Spanish => format!("inferido por la regla de inferencia `{}`", rule),
        OutputLanguage::French => format!("déduit par la règle d'inférence `{}`", rule),
        OutputLanguage::German => format!("durch Inferenzregel `{}` hergeleitet", rule),
        OutputLanguage::Portuguese => format!("inferido pela regra de inferência `{}`", rule),
        OutputLanguage::Russian => format!("выведено правилом вывода `{}`", rule),
        OutputLanguage::Arabic => format!("مستنتج من قاعدة الاستدلال `{}`", rule),
        OutputLanguage::Hindi => format!("अनुमान नियम `{}` से निष्कर्षित", rule),
        OutputLanguage::Vietnamese => format!("suy ra bởi quy tắc suy luận `{}`", rule),
        OutputLanguage::Indonesian => format!("disimpulkan oleh aturan inferensi `{}`", rule),
    }
}

fn prop_meaning_template(output_language: OutputLanguage, name: &str) -> String {
    match output_language {
        OutputLanguage::English => {
            format!(
                "prop with meaning `{}` (param constraints and definition clauses)",
                name
            )
        }
        OutputLanguage::SimplifiedChinese => {
            format!("具有含义 `{}` 的 prop（参数约束和定义子句）", name)
        }
        OutputLanguage::TraditionalChinese => {
            format!("具有含義 `{}` 的 prop（參數限制和定義子句）", name)
        }
        OutputLanguage::Japanese => {
            format!("意味 `{}` を持つ prop（パラメータ制約と定義節）", name)
        }
        OutputLanguage::Korean => {
            format!("의미 `{}`를 가진 prop(매개변수 제약과 정의 절)", name)
        }
        OutputLanguage::Spanish => {
            format!(
                "prop con significado `{}` (restricciones de parámetros y cláusulas de definición)",
                name
            )
        }
        OutputLanguage::French => {
            format!(
                "prop de sens `{}` (contraintes de paramètres et clauses de définition)",
                name
            )
        }
        OutputLanguage::German => {
            format!(
                "prop mit Bedeutung `{}` (Parameterbeschränkungen und Definitionsklauseln)",
                name
            )
        }
        OutputLanguage::Portuguese => {
            format!(
                "prop com significado `{}` (restrições de parâmetros e cláusulas de definição)",
                name
            )
        }
        OutputLanguage::Russian => {
            format!(
                "prop со смыслом `{}` (ограничения параметров и пункты определения)",
                name
            )
        }
        OutputLanguage::Arabic => {
            format!("prop بمعنى `{}` (قيود المعاملات وبنود التعريف)", name)
        }
        OutputLanguage::Hindi => {
            format!(
                "अर्थ `{}` वाला prop (पैरामीटर constraints और definition clauses)",
                name
            )
        }
        OutputLanguage::Vietnamese => {
            format!(
                "prop với nghĩa `{}` (ràng buộc tham số và mệnh đề định nghĩa)",
                name
            )
        }
        OutputLanguage::Indonesian => {
            format!(
                "prop dengan makna `{}` (batasan parameter dan klausa definisi)",
                name
            )
        }
    }
}
