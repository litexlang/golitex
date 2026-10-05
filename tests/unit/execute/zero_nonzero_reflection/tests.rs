use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::json_output::json_keys::localize_key;
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict: true, language,
    })
}

fn check(rt: &mut Runtime, code: &str, expected: bool) -> JsonValue {
    let run = rt.run_litex_code(code).expect("public Runtime");
    assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
    assert_eq!(run.success, expected, "{code}");
    crate::json_output::project_run_detailed(&run, rt, "eval", None)
}

fn find_rule<'a>(value: &'a JsonValue, name: &str) -> Option<&'a JsonValue> {
    match value {
        JsonValue::Object(fields) => {
            if fields.keys_in_order().into_iter().any(|k| {
                fields.get(&k).and_then(|v| v.as_str().ok()) == Some(name)
            }) { return Some(value); }
            fields.keys_in_order().into_iter().find_map(|k| find_rule(fields.get(&k).unwrap(), name))
        }
        JsonValue::Array(items) => items.iter().find_map(|v| find_rule(v, name)),
        _ => None,
    }
}

fn contains_string(value: &JsonValue, expected: &str) -> bool {
    match value {
        JsonValue::String(s) => s == expected,
        JsonValue::Object(fields) => fields.keys_in_order().into_iter()
            .any(|k| contains_string(fields.get(&k).unwrap(), expected)),
        JsonValue::Array(items) => items.iter().any(|v| contains_string(v, expected)),
        _ => false,
    }
}

#[test]
fn native_negation_and_existing_subtraction_retain_checked_premises() {
    for domain in ["R", "C"] {
        for premise in ["a!=(-b)", "a!=0-b", "b!=(-a)", "b!=0-a"] {
            let code = format!("forall a,b {domain}:\n    {premise}\n    =>:\n        a+b!=0\n");
            let json = check(&mut runtime(OutputLanguage::English), &code, true);
            let rule = find_rule(&json, "AddNonzeroFromNotEqualNegation").expect("actual builtin");
            let child = rule.as_object().unwrap().get("not_equal_negation_proof").unwrap();
            assert!(contains_string(child, "by_known_atomic"));
        }
    }
}

#[test]
fn product_source_fact_and_citation_survive_in_both_languages() {
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        for source in ["a*b!=0", "0!=a*b"] {
            let code = format!("forall a,b C:\n    {source}\n    =>:\n        a!=0\n");
            let json = check(&mut runtime(language.clone()), &code, true);
            let rule = find_rule(&json, "ProductComponentNonzero").expect("actual builtin");
            let child = rule.as_object().unwrap().get("product_nonzero_proof").unwrap();
            assert!(contains_string(child, if source.starts_with('0') { "0 != a * b" } else { "a * b != 0" }));
            assert!(contains_string(child, "by_known_atomic"));
            let key = |name| localize_key(name, language.clone());
            let statement = &json.as_object().unwrap().get(&key("statement_results")).unwrap().as_array().unwrap()[0];
            let verify = statement.as_object().unwrap().get(&key("verify")).unwrap().as_object().unwrap();
            let assumption = &verify.get(&key("assumed_dom_facts")).unwrap().as_array().unwrap()[0];
            let stores = assumption.as_object().unwrap().get(&key("store_and_infer")).unwrap().as_object().unwrap().get(&key("stores")).unwrap().as_array().unwrap();
            let source_id = stores[0].as_object().unwrap().get(&key("fact_id")).unwrap().as_str().unwrap();
            assert!(contains_string(child, source_id), "missing actual source citation {source_id}");
        }
    }
}

#[test]
fn product_components_both_orientations_and_scalar_carriers_pass() {
    for domain in ["R", "C", "Q", "Z"] {
        for goal in ["a!=0", "0!=a", "b!=0", "0!=b"] {
            let code = format!("forall a,b {domain}:\n    0!=b*a\n    =>:\n        {goal}\n");
            let json = check(&mut runtime(OutputLanguage::English), &code, true);
            let rule = find_rule(&json, "ProductComponentNonzero").expect("actual leaf");
            assert!(contains_string(rule, "0 != b * a"));
        }
    }
}

#[test]
fn false_nonzero_and_zero_product_controls_reject() {
    for code in [
        "forall a,b R:\n    a=(-b)\n    =>:\n        a+b!=0\n",
        "forall a,b C:\n    a=(-b)\n    =>:\n        a+b!=0\n",
        "forall a,b R:\n    a*b!=1\n    =>:\n        a!=0\n",
        "forall a,b R:\n    a*b!=0\n    =>:\n        a!=1\n",
        "forall a,b R:\n    a+b!=0\n    =>:\n        a!=0\n",
        "forall a,b R:\n    a=b\n    =>:\n        a+b!=0\n",
        "forall a,b R:\n    a*b=0\n    =>:\n        b=0\n",
    ] { check(&mut runtime(OutputLanguage::English), code, false); }
}

#[test]
fn failed_reflection_does_not_publish_and_valid_reuse_continues() {
    let mut rt = runtime(OutputLanguage::English);
    let false_goal = "forall a,b R:\n    a*b!=1\n    =>:\n        a!=0\n";
    check(&mut rt, false_goal, false);
    let tokens = Tokenizer::new().tokenize(false_goal, rt.current_file.clone()).unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else { panic!("fact") };
    assert!(rt.verify_fact(&goal, VerifyState::new(VerifyStateLevel::Direct)).unwrap().is_failed());
    check(&mut rt, false_goal, false);
    let valid = "forall a,b C:\n    a*b!=0\n    =>:\n        a!=0\n";
    check(&mut rt, valid, true);
    check(&mut rt, valid, true);
    check(&mut rt, false_goal, false);
    check(&mut rt, "forall a,b C:\n    a!=(-b)\n    =>:\n        a+b!=0\n", true);
}

#[test]
fn dedicated_zero_nonzero_evidence_tracer_passes() {
    let code = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/proof_nodes/atomic/by_builtin_rule/zero_nonzero_reflection_evidence.lit"));
    let json = check(&mut runtime(OutputLanguage::English), code, true);
    assert!(find_rule(&json, "ProductComponentNonzero").is_some());
    assert!(find_rule(&json, "AddNonzeroFromNotEqualNegation").is_some());
}

#[test]
fn reflection_rules_respect_parent_search_ceiling() {
    for source in [
        "forall a,b C:\n    a*b!=0\n    =>:\n        a!=0\n",
        "forall a,b C:\n    a!=(-b)\n    =>:\n        a+b!=0\n",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let tokens = Tokenizer::new().tokenize(source, rt.current_file.clone()).unwrap();
        let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else { panic!("fact") };
        for level in [VerifyStateLevel::Direct, VerifyStateLevel::KnownSpecialProperty] {
            assert!(rt.verify_fact(&goal, VerifyState::new(level)).unwrap().is_failed());
        }
        assert!(!rt.verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule)).unwrap().is_failed());
    }
}
