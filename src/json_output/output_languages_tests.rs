//! Locale changes must preserve proof results, source text and JSON structure.

use super::json_keys::localize_key;
use super::{project_stmt_compact, project_stmt_detailed, project_stmt_normal};
use crate::execute::ExecStmtResult;
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;
use std::collections::HashMap;

#[test]
fn every_language_preserves_success_failure_and_source() {
    for language in OutputLanguage::ALL {
        for (code, success) in [("1 + 2 = 3", true), ("1 + 2 = 4", false)] {
            let mut runtime = runtime(language);
            let result = execute(&mut runtime, code);
            for json in [
                project_stmt_compact(&result, &runtime),
                project_stmt_normal(&result, &runtime),
                project_stmt_detailed(&result, &runtime),
            ] {
                assert_eq!(
                    field(&json, "success", language),
                    &JsonValue::Bool(success),
                    "{language:?}: {code}"
                );
                assert_eq!(field(&json, "statement", language).as_str().unwrap(), code);
            }
        }
    }
}

#[test]
fn every_language_preserves_exact_function_domain_evidence_and_rejection() {
    for language in OutputLanguage::ALL {
        let mut rt = runtime(language);
        assert!(!execute(&mut rt, "have fn u(k closed_range(1,2)) Z = 0").is_failed());
        for (code, success) in [
            ("release thm fn_set_member(u, finite_seq(R,2))", true),
            ("release thm fn_set_member(u, finite_seq(R,3))", false),
        ] {
            let result = execute(&mut rt, code);
            for json in [project_stmt_compact(&result, &rt), project_stmt_normal(&result, &rt), project_stmt_detailed(&result, &rt)] {
                assert_eq!(field(&json, "success", language), &JsonValue::Bool(success), "{language:?}: {code}");
            }
            let detailed = project_stmt_detailed(&result, &rt);
            if success {
                let domain = find_evidence_value(&detailed, &localize_key("function_domain", language)).unwrap();
                let target = field(&domain, "target_signature", language).as_str().unwrap();
                assert!(target.contains("closed_range(1, 2)"), "{language:?}: {target}");
                assert!(find_evidence_value(&domain, &localize_key("subject_equal", language)).is_some());
            } else {
                let failure = find_evidence_value(&detailed, &localize_key("failure", language)).unwrap();
                assert_eq!(field(&failure, "phase", language).as_str().unwrap(), "function_domain");
            }
        }
        for key in ["function_domain", "subject_equal", "target_signature"] {
            if language != OutputLanguage::English { assert_ne!(localize_key(key, language), key); }
        }
    }
}

fn find_evidence_value(json: &JsonValue, key: &str) -> Option<JsonValue> {
    match json {
        JsonValue::Object(object) => {
            if let Some(value) = object.get(key) { return Some(value.clone()); }
            for (_, value) in object.iter() {
                if let Some(found) = find_evidence_value(value, key) { return Some(found); }
            }
        }
        JsonValue::Array(values) => {
            for value in values {
                if let Some(found) = find_evidence_value(value, key) { return Some(found); }
            }
        }
        _ => {}
    }
    None
}

#[test]
fn normal_output_keeps_field_order_and_localizes_explanations() {
    let expected_names = [
        "Closed calculation",
        "封闭计算",
        "封閉計算",
        "Calcul fermé",
        "Вычисление замкнутого выражения",
        "Cálculo cerrado",
        "حساب تعبير مغلق",
        "閉じた式の計算",
        "닫힌 식 계산",
        "Tính toán biểu thức đóng",
    ];
    for (language, name) in OutputLanguage::ALL.into_iter().zip(expected_names) {
        let mut runtime = runtime(language);
        let result = execute(&mut runtime, "1 + 2 = 3");
        let json = project_stmt_normal(&result, &runtime);
        let expected_keys = ["success", "statement", "proof_method", "stores", "infers"]
            .map(|key| localize_key(key, language));
        assert_eq!(
            json.as_object().unwrap().keys_in_order(),
            expected_keys.iter().map(String::as_str).collect::<Vec<_>>()
        );
        let why = field(&json, "proof_method", language);
        assert_eq!(field(why, "rule_name", language).as_str().unwrap(), name);
        let message = field(why, "message", language).as_str().unwrap();
        assert!(!message.is_empty());
        if language != OutputLanguage::English {
            assert_ne!(
                message,
                "Exact evaluation of closed expressions without proof search"
            );
        }
        assert_eq!(
            field(&json, "stores", language).as_array().unwrap()[0]
                .as_str()
                .unwrap(),
            "1 + 2 = 3"
        );
        assert!(why.as_object().unwrap().get("rule_id").is_none());
    }
}

#[test]
fn every_language_preserves_readable_citations_and_identifiers() {
    for language in OutputLanguage::ALL {
        let mut runtime = runtime(language);
        execute(&mut runtime, "have k N");
        let result = execute(&mut runtime, "k >= 0");
        let json = project_stmt_normal(&result, &runtime);
        let why = field(&json, "proof_method", language);
        assert_eq!(field(why, "cite", language).as_str().unwrap(), "0 <= k");
        assert_eq!(
            field(&json, "statement", language).as_str().unwrap(),
            "k >= 0"
        );
    }
}

#[test]
fn locale_keys_do_not_collide_beyond_existing_aliases() {
    for language in OutputLanguage::ALL {
        let mut seen = HashMap::new();
        for key in LOCALIZED_KEYS {
            let localized = localize_key(key, language);
            if let Some(previous) = seen.insert(localized.clone(), *key) {
                let same_existing_alias = matches!(
                    (previous, *key),
                    ("success", "ok")
                        | ("why_failed", "fail_reason")
                        | ("assumptions_stored", "assumption_stored")
                        | ("theorem", "thm_name")
                );
                assert!(
                    same_existing_alias,
                    "{language:?}: {previous} and {key} collide as {localized}"
                );
            }
        }
        assert_eq!(
            localize_key("future_extension_key", language),
            "future_extension_key"
        );
    }
}

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}

fn execute(runtime: &mut Runtime, code: &str) -> ExecStmtResult {
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .unwrap();
    let statements = runtime.parse(&tokens).unwrap();
    assert_eq!(statements.len(), 1);
    runtime.exec_stmt(&statements[0]).unwrap()
}

fn field<'a>(json: &'a JsonValue, key: &str, language: OutputLanguage) -> &'a JsonValue {
    json.as_object()
        .unwrap()
        .get(&localize_key(key, language))
        .unwrap()
}

const LOCALIZED_KEYS: &[&str] = &[
    "artifact", "format", "output_path", "content", "error",
    "function_domain", "domain_comparison", "source_signature", "target_signature",
    "function_wd", "target_wd", "subject_equal", "carrier_equal", "right_domain",
    "comparison", "source", "forward", "reverse", "forward_proof", "reverse_proof",
    "pointwise", "pointwise_proof", "signature_source", "return_space", "checked_domain",
    "left_function_body", "left_expanded_body", "right_function_body", "right_expanded_body",
    "parameter_group_index", "empty_carrier", "empty_carrier_proof", "empty_carrier_store",
    "left_normalization", "right_normalization", "parent_well_defined_side",
    "kind",
    "shape",
    "left_path",
    "bridge",
    "right_path",
    "why_parameters_of_known_fact_are_equal_to_givens",
    "success",
    "ok",
    "target",
    "path",
    "detail",
    "language",
    "statement_results",
    "session_error",
    "statement",
    "proof_method",
    "why_failed",
    "fail_reason",
    "stores",
    "infers",
    "evaluated_object",
    "aggregate_evaluations",
    "function_evaluations",
    "algo_evaluations",
    "type",
    "rule_name",
    "message",
    "cite",
    "line",
    "phase",
    "goal",
    "family",
    "verify",
    "store_and_infer",
    "fact",
    "fact_id",
    "source_fact_id",
    "definition_facts",
    "well_defined",
    "searched_proof",
    "rule",
    "failure",
    "result",
    "goal_index",
    "step_index",
    "case_index",
    "left_case_index",
    "right_case_index",
    "from_in_z",
    "goal_domain_stored",
    "goals_wd",
    "body",
    "base",
    "step",
    "form",
    "assumptions_stored",
    "assumption_stored",
    "proof_steps",
    "goals_verified",
    "stored",
    "fn_set_well_defined",
    "measure_in_z",
    "lower_in_z",
    "measure_ge_lower",
    "case_checks",
    "coverage",
    "disjoint",
    "cases",
    "negated_component",
    "in_ret_set",
    "theorem",
    "thm_name",
    "builtin",
    "arguments",
    "requirements",
    "conclusions",
    "provenance",
    "type_proofs",
    "dom_proofs",
    "conclusions_wd",
    "expected",
    "actual",
    "index",
    "mode",
    "left_identity",
    "right_identity",
    "reversed",
];

#[test]
fn positive_and_negative_numeric_membership_have_distinct_translations() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::ClosedNumericMembershipBuiltinRuleProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_in_fact::ClosedNumericNonMembershipBuiltinRuleProof;
    let positive = ClosedNumericMembershipBuiltinRuleProof {};
    let negative = ClosedNumericNonMembershipBuiltinRuleProof {
        normal: "1/2".into(),
    };
    for language in OutputLanguage::ALL.into_iter().skip(2) {
        let member = positive.rule_name_and_message(language);
        let nonmember = negative.rule_name_and_message(language);
        assert_ne!(member.rule_name, nonmember.rule_name, "{language:?}");
        assert_ne!(member.message, nonmember.message, "{language:?}");
    }
    assert_eq!(
        positive
            .rule_name_and_message(OutputLanguage::Japanese)
            .message,
        "閉じた式の評価値は対象集合に属します"
    );
    assert_eq!(
        negative
            .rule_name_and_message(OutputLanguage::Japanese)
            .message,
        "閉じた式の評価値は対象集合に属しません"
    );
}
