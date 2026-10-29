//! Per-application bilingual mathematical comments, with real verifier evidence.
use litex::knowledge_base::JsonValue;
use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, ReadingInput};
use std::path::PathBuf;

fn field<'a>(value: &'a JsonValue, key: &str) -> &'a JsonValue {
    value.as_object().unwrap().get(key).unwrap()
}
fn document(relative: &str) -> JsonValue {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(relative);
    let result = build_reading(&ReadingInput::File(path), true, OutputLanguage::English);
    assert!(result.success, "{relative}");
    result.document
}
fn nodes(document: &JsonValue) -> Vec<&JsonValue> {
    field(document, "evidence_nodes")
        .as_array()
        .unwrap()
        .iter()
        .map(|entry| field(entry, "node"))
        .collect()
}

#[test]
fn actual_builtin_applications_own_both_languages() {
    let cases = [
        "examples/proof_nodes/atomic/by_builtin_rule/dvd_one.lit",
        "examples/proof_nodes/equal/by_builtin_rule/composition_left_identity.lit",
        "examples/proof_nodes/equal/by_builtin_rule/sqrt_product_from_known_argument.lit",
        "examples/proof_nodes/or/by_builtin_rule/abs_sign_split.lit",
        "examples/proof_nodes/exist/by_builtin_rule/archimedean_reciprocal.lit",
    ];
    for case in cases {
        let doc = document(case);
        let applications: Vec<_> = nodes(&doc)
            .into_iter()
            .filter(|node| {
                node.as_object()
                    .unwrap()
                    .get("rule_id")
                    .and_then(|value| value.as_str().ok())
                    .is_some_and(|id| id.starts_with("builtin."))
            })
            .collect();
        assert!(!applications.is_empty(), "{case}");
        for node in applications {
            for locale in ["en", "zh"] {
                let copy = field(field(node, "comment"), locale);
                let name = field(copy, "name").as_str().unwrap();
                let message = field(copy, "message").as_str().unwrap();
                assert!(!name.is_empty() && !message.is_empty(), "{case}: {locale}");
                if locale == "zh" {
                    assert!(
                        message
                            .chars()
                            .any(|c| ('\u{4e00}'..='\u{9fff}').contains(&c)),
                        "{case}: {message}"
                    );
                }
                assert!(!message.contains("enclosing WD"), "{case}: {message}");
            }
        }
    }
}

#[test]
fn rules_sharing_a_family_keep_their_own_mathematical_comment() {
    let product =
        document("examples/proof_nodes/equal/by_builtin_rule/sqrt_product_from_known_argument.lit");
    let quotient = document(
        "examples/proof_nodes/equal/by_builtin_rule/sqrt_quotient_from_known_argument.lit",
    );
    let copy = |doc: &JsonValue| {
        nodes(doc)
            .into_iter()
            .find(|node| {
                node.as_object()
                    .unwrap()
                    .get("rule_id")
                    .and_then(|v| v.as_str().ok())
                    == Some("builtin.EqualitySearchProofByBuiltinRule::ScalarExtra")
            })
            .map(|node| field(node, "comment").clone())
            .expect("the actual scalar-extra rule application")
    };
    let product_copy = copy(&product);
    let quotient_copy = copy(&quotient);
    assert_ne!(product_copy, quotient_copy);
    assert!(field(field(&product_copy, "zh"), "message")
        .as_str()
        .unwrap()
        .contains("a·b"));
    assert!(field(field(&quotient_copy, "zh"), "message")
        .as_str()
        .unwrap()
        .contains("b>0"));
}

#[test]
fn structural_integer_quotient_explains_the_actual_rule_and_keeps_wd_separate() {
    let doc = document("examples/reading/lessons/en/sqrt-two.lit");
    let all = nodes(&doc);
    let quotient = all
        .iter()
        .find(|node| {
            node.as_object()
                .unwrap()
                .get("type")
                .and_then(|v| v.as_str().ok())
                == Some("StructuralMembershipReason")
                && node
                    .as_object()
                    .unwrap()
                    .get("variant")
                    .and_then(|v| v.as_str().ok())
                    == Some("ExactIntegerDiv")
        })
        .expect("the retained structural integer-quotient certificate");
    let message = field(field(field(quotient, "comment"), "zh"), "message")
        .as_str()
        .unwrap();
    assert!(message.contains("b≠0") && message.contains("b 整除 a"));
    assert!(!message.contains("外层") && !message.contains("WD"));
    assert!(all.iter().any(|node| {
        node.as_object()
            .unwrap()
            .get("type")
            .and_then(|v| v.as_str().ok())
            == Some("VerifyAtomicExceptEqualityFactSuccess")
            && field(node, "fields")
                .as_object()
                .unwrap()
                .get("well_defined_proof")
                .is_some()
    }));
}
