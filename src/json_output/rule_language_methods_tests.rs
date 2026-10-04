//! Each rule owns its language methods; the generic API only selects one.

use super::explain::BuiltinRuleText;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_power_laws::PowerProductSameBaseBuiltinRuleProof;
use crate::launch_command::OutputLanguage;
use std::path::Path;

const LANGUAGES: [(&str, &str); 10] = [
    ("English", "en"),
    ("Chinese", "zh"),
    ("ChineseTraditional", "zh_hant"),
    ("French", "fr"),
    ("Russian", "ru"),
    ("Spanish", "es"),
    ("Arabic", "ar"),
    ("Japanese", "ja"),
    ("Korean", "ko"),
    ("Vietnamese", "vi"),
];

#[test]
fn every_rule_impl_owns_ten_methods_and_a_selection_only_dispatcher() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/json_output/explain");
    let expected = format!(
        "match lang {{ {} }}",
        LANGUAGES
            .iter()
            .map(|(language, suffix)| {
                format!("OutputLanguage::{language} => self.rule_name_and_message_{suffix}(),")
            })
            .collect::<Vec<_>>()
            .join(" ")
    );
    let mut checked = 0;
    for folder in ["atomic_builtin_rule", "equality_builtin_rule"] {
        for entry in std::fs::read_dir(root.join(folder)).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().and_then(|s| s.to_str()) != Some("rs") {
                continue;
            }
            let source = std::fs::read_to_string(&path).unwrap();
            for implementation in source.split("\nimpl ").skip(1) {
                let Some(dispatch) = implementation.find("pub fn rule_name_and_message(") else {
                    continue;
                };
                let owner = implementation.split('{').next().unwrap().trim();
                for (_, suffix) in LANGUAGES {
                    assert!(
                        implementation.contains(&format!("pub fn rule_name_and_message_{suffix}(")),
                        "{}: {owner} missing method for {suffix}",
                        path.display()
                    );
                }
                let body_start = dispatch + implementation[dispatch..].find('{').unwrap();
                let mut depth = 0;
                let body_end = implementation[body_start..]
                    .char_indices()
                    .find_map(|(offset, ch)| {
                        if ch == '{' {
                            depth += 1;
                        }
                        if ch == '}' {
                            depth -= 1;
                            if depth == 0 {
                                return Some(body_start + offset);
                            }
                        }
                        None
                    })
                    .unwrap();
                // A selector contains no strings/braces other than the method and match.
                let body = &implementation[body_start + 1..body_end];
                assert_eq!(
                    without_whitespace(body),
                    without_whitespace(&expected),
                    "{}: {owner} generic dispatcher must only call its language methods",
                    path.display()
                );
                checked += 1;
            }
        }
    }
    assert!(
        checked > 0,
        "the source audit must inspect actual rule implementations"
    );
}

#[test]
fn power_product_exposes_every_named_language_method() {
    let rule = PowerProductSameBaseBuiltinRuleProof {
        proof_of_requirement_facts: Vec::new(),
    };
    let methods: [fn(&PowerProductSameBaseBuiltinRuleProof) -> BuiltinRuleText; 10] = [
        PowerProductSameBaseBuiltinRuleProof::rule_name_and_message_en,
        PowerProductSameBaseBuiltinRuleProof::rule_name_and_message_zh,
        PowerProductSameBaseBuiltinRuleProof::rule_name_and_message_zh_hant,
        PowerProductSameBaseBuiltinRuleProof::rule_name_and_message_fr,
        PowerProductSameBaseBuiltinRuleProof::rule_name_and_message_ru,
        PowerProductSameBaseBuiltinRuleProof::rule_name_and_message_es,
        PowerProductSameBaseBuiltinRuleProof::rule_name_and_message_ar,
        PowerProductSameBaseBuiltinRuleProof::rule_name_and_message_ja,
        PowerProductSameBaseBuiltinRuleProof::rule_name_and_message_ko,
        PowerProductSameBaseBuiltinRuleProof::rule_name_and_message_vi,
    ];
    for (language, method) in OutputLanguage::ALL.into_iter().zip(methods) {
        let BuiltinRuleText { rule_name, message } = method(&rule);
        assert!(has_localized_prose(&rule_name, language), "{language:?}");
        assert!(has_localized_prose(&message, language), "{language:?}");
        assert!(message.contains("a^m · a^n = a^(m+n)"));
        let selected = rule.rule_name_and_message(language);
        assert_eq!((selected.rule_name, selected.message), (rule_name, message));
    }
}

#[test]
fn every_literal_builtin_explanation_has_localized_names_and_prose() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/json_output/explain");
    let mut checked = 0;
    for folder in ["atomic_builtin_rule", "equality_builtin_rule"] {
        for entry in std::fs::read_dir(root.join(folder)).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().and_then(|s| s.to_str()) != Some("rs") {
                continue;
            }
            let source = std::fs::read_to_string(&path).unwrap();
            for implementation in source.split("\nimpl ").skip(1) {
                let owner = implementation.split('{').next().unwrap().trim();
                let english_messages: Vec<_> = implementation
                    .split("pub fn rule_name_and_message_en(")
                    .nth(1)
                    .unwrap_or("")
                    .split("pub fn ")
                    .next()
                    .unwrap()
                    .split("text(")
                    .skip(1)
                    .map(|call| first_string_literals(call, 2))
                    .collect();
                for (language, (_, suffix)) in OutputLanguage::ALL.into_iter().zip(LANGUAGES) {
                    let needle = format!("pub fn rule_name_and_message_{suffix}(");
                    let Some(start) = implementation.find(&needle) else {
                        continue;
                    };
                    let body = implementation[start + needle.len()..]
                        .split("pub fn ")
                        .next()
                        .unwrap();
                    let calls: Vec<_> = body.split("text(").skip(1).collect();
                    assert_eq!(
                        calls.len(),
                        english_messages.len(),
                        "{}: {owner} {language:?} must cover the same branches as English",
                        path.display()
                    );
                    // Existing impl ownership and match-arm order locate the copy;
                    // presentation text does not need a second rule identifier.
                    for (branch, call) in calls.into_iter().enumerate() {
                        let strings = first_string_literals(call, 2);
                        assert_eq!(strings.len(), 2, "{}: incomplete text()", path.display());
                        if language != OutputLanguage::English {
                            assert_ne!(
                                strings[1], english_messages[branch][1],
                                "{}: {owner} branch {branch} {language:?} copied the whole English message",
                                path.display()
                            );
                        }
                        for (field, value) in [("name", &strings[0]), ("message", &strings[1])] {
                            assert!(
                                has_localized_prose(value, language),
                                "{}: {owner} branch {branch} {language:?} {field} lacks localized prose: {value}",
                                path.display()
                            );
                        }
                        checked += 1;
                    }
                    // Some aggregate/calculation leaves construct the payload
                    // directly instead of calling text(). Audit their literal
                    // fields too; dynamic names are covered by runtime variants.
                    for field in ["rule_name:", "message:"] {
                        for value in body.split(field).skip(1) {
                            if !value.trim_start().starts_with('"') {
                                continue;
                            }
                            let value = first_string_literals(value, 1).pop().unwrap();
                            assert!(
                                has_localized_prose(&value, language),
                                "{}: {language:?} literal {field} lacks localized prose: {value}",
                                path.display()
                            );
                            checked += 1;
                        }
                    }
                }
            }
        }
    }
    assert!(
        checked > 4_000,
        "audit must cover the maintained literal inventory"
    );
}

fn first_string_literals(source: &str, limit: usize) -> Vec<String> {
    let mut chars = source.chars();
    let mut values = Vec::new();
    while let Some(ch) = chars.next() {
        if ch != '"' {
            continue;
        }
        let mut value = String::new();
        while let Some(ch) = chars.next() {
            match ch {
                '"' => break,
                '\\' => value.push(chars.next().expect("complete Rust string escape")),
                _ => value.push(ch),
            }
        }
        values.push(value);
        if values.len() == limit {
            break;
        }
    }
    values
}

fn has_localized_prose(value: &str, lang: OutputLanguage) -> bool {
    match lang {
        OutputLanguage::Chinese | OutputLanguage::ChineseTraditional => value
            .chars()
            .any(|c| ('\u{4e00}'..='\u{9fff}').contains(&c)),
        OutputLanguage::Russian => value
            .chars()
            .any(|c| ('\u{0400}'..='\u{04ff}').contains(&c)),
        OutputLanguage::Arabic => value
            .chars()
            .any(|c| ('\u{0600}'..='\u{06ff}').contains(&c) && c.is_alphabetic()),
        OutputLanguage::Japanese => value.chars().any(|c| {
            ('\u{3040}'..='\u{30ff}').contains(&c) || ('\u{4e00}'..='\u{9fff}').contains(&c)
        }),
        OutputLanguage::Korean => value
            .chars()
            .any(|c| ('\u{ac00}'..='\u{d7af}').contains(&c)),
        OutputLanguage::Vietnamese => value.chars().any(|c| c.is_alphabetic() && !c.is_ascii()),
        OutputLanguage::English | OutputLanguage::French | OutputLanguage::Spanish => {
            let math_words = [
                "sin",
                "cos",
                "tan",
                "cot",
                "arcsin",
                "arccos",
                "arctan",
                "arccot",
                "sqrt",
                "abs",
                "log",
                "ln",
                "exp",
                "sign",
                "min",
                "max",
                "gcd",
                "lcm",
                "mod",
                "quot",
                "pow",
                "union",
                "intersect",
                "cart",
                "embed",
                "sum",
                "product",
                "reduce",
                "range",
                "forall",
                "exist",
                "not",
                "subset",
                "superset",
                "set",
                "minus",
                "power",
                "family",
                "index",
                "closed",
                "proj",
                "dim",
                "tuple",
                "list",
                "img",
                "prime",
                "coprime",
            ];
            value.contains(" of ")
                || value.split(|c: char| !c.is_alphabetic()).any(|word| {
                    word.chars().count() > 2 && !math_words.contains(&word.to_lowercase().as_str())
                })
        }
    }
}

fn without_whitespace(value: &str) -> String {
    value.chars().filter(|ch| !ch.is_whitespace()).collect()
}
