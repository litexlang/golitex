use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{
    AtomicExceptEqualityFactSearchProofByBuiltinRule,
    less::LessFactSearchProofByBuiltinRule,
    less_equal::LessEqualFactSearchProofByBuiltinRule,
};
use crate::execute::execute_fact_stmt::verify_forall_fact::{VerifyForallFactProof, VerifyForallFactResult};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState, VerifyStateLevel};
use crate::execute::{ExecFactStmtResult, ExecStmtResult};
use crate::json_output::explain::BuiltinRuleText;
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

fn check(rt: &mut Runtime, code: &str, accepted: bool) -> JsonValue {
    let run = rt.run_litex_code(code).expect("public Runtime");
    assert!(run.session_error.is_none(), "{code}");
    assert_eq!(run.success, accepted, "{code}");
    crate::json_output::project_run_detailed(&run, rt, "eval", None)
}

fn find_rule(value: &JsonValue, name: &str) -> Option<JsonValue> {
    match value {
        JsonValue::Object(fields) => {
            if fields.keys_in_order().into_iter().any(|k| {
                fields.get(&k).and_then(|v| v.as_str().ok()) == Some(name)
            }) { return Some(value.clone()); }
            fields.keys_in_order().into_iter().find_map(|k| find_rule(fields.get(&k).unwrap(), name))
        }
        JsonValue::Array(items) => items.iter().find_map(|v| find_rule(v, name)),
        _ => None,
    }
}

fn contains_string(value: &JsonValue, text: &str) -> bool {
    match value {
        JsonValue::String(s) => s == text,
        JsonValue::Object(fields) => fields.keys_in_order().into_iter().any(|k| contains_string(fields.get(&k).unwrap(), text)),
        JsonValue::Array(items) => items.iter().any(|v| contains_string(v, text)),
        _ => false,
    }
}

fn actual_leaf_text(result: &ExecStmtResult, language: OutputLanguage) -> BuiltinRuleText {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) = result else { panic!("fact success") };
    let VerifyFactResult::ForallFact(f) = &s.verify_result else { panic!("forall") };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) = &**f else { panic!("local forall") };
    let VerifyFactResult::AtomicExceptEquality(a) = &p.proved_then_facts[0].verify_result else { panic!("atomic") };
    let VerifyAtomicExceptEqualityFactResult::Success(p) = &**a else { panic!("atomic success") };
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) = &p.searched_proof else { panic!("actual builtin") };
    match rule {
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(LessFactSearchProofByBuiltinRule::LogStrictDecreasing(p)) => {
            assert!(!p.guards.base_positive_proof.is_failed());
            assert!(!p.guards.base_lt_one_proof.is_failed());
            assert!(!p.guards.left_arg_positive_proof.is_failed());
            assert!(!p.guards.right_arg_positive_proof.is_failed());
            assert!(!p.argument_order.is_failed());
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(LessEqualFactSearchProofByBuiltinRule::LogWeakDecreasing(p)) => {
            assert!(!p.guards.base_positive_proof.is_failed());
            assert!(!p.guards.base_lt_one_proof.is_failed());
            assert!(!p.guards.left_arg_positive_proof.is_failed());
            assert!(!p.guards.right_arg_positive_proof.is_failed());
            assert!(!p.argument_order.is_failed());
        }
        _ => panic!("actual owned log leaf"),
    }
    rule.rule_name_and_message(language)
}

#[test]
fn legal_carriers_both_source_directions_and_existing_increasing_routes() {
    for (relation, reverse, name) in [("<", ">", "LogStrictDecreasing"), ("<=", ">=", "LogWeakDecreasing")] {
        for domain in ["R+", "Q+", "N+", "Z+"] {
            for source in [format!("x{relation}y"), format!("y{reverse}x")] {
                let code = format!("forall a R+,x,y {domain}:\n    a<1\n    {source}\n    =>:\n        log(a,y){relation}log(a,x)\n");
                assert!(find_rule(&check(&mut runtime(OutputLanguage::English), &code, true), name).is_some());
            }
        }
        let code = format!("forall a,x,y R+:\n    1<a\n    x{relation}y\n    =>:\n        log(a,x){relation}log(a,y)\n");
        let json = check(&mut runtime(OutputLanguage::English), &code, true);
        let old_name = if relation == "<" { "LogOrderPreservingStrict" } else { "LogOrderPreservingWeak" };
        assert!(find_rule(&json, old_name).is_some());
        assert!(find_rule(&json, name).is_none());
    }
}

#[test]
fn actual_reverse_guards_and_argument_citations_survive_detailed_projection() {
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        for (relation, reverse, name) in [("<", ">", "LogStrictDecreasing"), ("<=", ">=", "LogWeakDecreasing")] {
            let code = format!("forall a,x,y R:\n    a>0\n    1>a\n    x>0\n    y>0\n    y{reverse}x\n    =>:\n        log(a,y){relation}log(a,x)\n");
            let mut rt = runtime(language);
            let run = rt.run_litex_code(&code).unwrap();
            assert!(run.success && run.session_error.is_none());
            actual_leaf_text(run.statement_results.last().unwrap(), language);
            let json = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
            let key = |s| localize_key(s, language);
            let statement = &json.as_object().unwrap().get(&key("statement_results")).unwrap().as_array().unwrap()[0];
            let assumptions = statement.as_object().unwrap().get(&key("verify")).unwrap().as_object().unwrap().get(&key("assumed_dom_facts")).unwrap().as_array().unwrap();
            assert_eq!(assumptions.len(), 5);
            let source_id = |i: usize| assumptions[i].as_object().unwrap().get(&key("store_and_infer")).unwrap().as_object().unwrap().get(&key("stores")).unwrap().as_array().unwrap()[0].as_object().unwrap().get(&key("fact_id")).unwrap().as_str().unwrap();
            let leaf_value = find_rule(&json, name).unwrap();
            let leaf = leaf_value.as_object().unwrap();
            let guards = leaf.get(&key("guards")).unwrap().as_object().unwrap();
            assert_eq!(guards.keys_in_order().len(), 4);
            for (field, index) in [("base_positive_proof", 0), ("base_lt_one_proof", 1), ("left_arg_positive_proof", 3), ("right_arg_positive_proof", 2)] {
                let proof = guards.get(&key(field)).unwrap();
                assert!(contains_string(proof, source_id(index)), "{field}");
            }
            assert!(contains_string(leaf.get(&key("argument_order")).unwrap(), source_id(4)));
        }
    }
}

#[test]
fn wrong_directions_nonpositive_or_unit_bases_and_strictness_do_not_pass() {
    for code in [
        "forall a,x,y R+:\n    a<1\n    x<y\n    =>:\n        log(a,x)<log(a,y)\n",
        "forall a,x,y R+:\n    a<1\n    x<=y\n    =>:\n        log(a,x)<=log(a,y)\n",
        "forall a,x,y R+:\n    a<1\n    x<=y\n    =>:\n        log(a,y)<log(a,x)\n",
        "forall a,x,y R+:\n    a!=1\n    x<y\n    =>:\n        log(a,y)<log(a,x)\n",
        "forall a,b,x,y R+:\n    a<1\n    b<1\n    x<y\n    =>:\n        log(a,y)<log(b,x)\n",
        "forall a,x,y R:\n    a<1\n    x<y\n    =>:\n        log(a,y)<log(a,x)\n",
        "log(1,2)<log(1,1)\n",
        "log(0,2)<log(0,1)\n",
        "log(-0.5,2)<log(-0.5,1)\n",
        "log(0.5,2)<log(0.5,0)\n",
        "log(0.5,2)<log(0.5,-1)\n",
    ] { check(&mut runtime(OutputLanguage::English), code, false); }
    check(&mut runtime(OutputLanguage::English), "forall a,x R+:\n    a<1\n    =>:\n        log(a,x)<=log(a,x)\n", true);
}

#[test]
fn inherited_ceiling_and_failed_statement_publication_are_retained() {
    for relation in ["<", "<="] {
        let code = format!("forall a,x,y R+:\n    a<1\n    x{relation}y\n    =>:\n        log(a,y){relation}log(a,x)\n");
        let mut rt = runtime(OutputLanguage::English);
        let tokens = Tokenizer::new().tokenize(&code, rt.current_file.clone()).unwrap();
        let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else { panic!("fact") };
        for level in [VerifyStateLevel::Direct, VerifyStateLevel::KnownSpecialProperty] {
            assert!(rt.verify_fact(&goal, VerifyState::new(level)).unwrap().is_failed());
        }
        assert!(!rt.verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule)).unwrap().is_failed());
        let bad = "forall a,x,y R+:\n    a<1\n    x<=y\n    =>:\n        log(a,y)<log(a,x)\n";
        check(&mut rt, bad, false);
        check(&mut rt, &code, true);
        let reused = check(&mut rt, &code, true);
        assert!(contains_string(&reused, "by_known_forall_fact"));
        check(&mut rt, bad, false);
    }
}

#[test]
fn two_actual_typed_leaves_have_ten_guarded_language_outputs() {
    for relation in ["<", "<="] {
        let code = format!("forall a,x,y R+:\n    a<1\n    x{relation}y\n    =>:\n        log(a,y){relation}log(a,x)\n");
        let mut rt = runtime(OutputLanguage::English);
        let run = rt.run_litex_code(&code).unwrap();
        assert!(run.success);
        let law = format!("0<a<1, 0<x, 0<y, x{relation}y, both logs well-defined => log(a,y){relation}log(a,x)");
        for language in [OutputLanguage::English, OutputLanguage::Chinese, OutputLanguage::ChineseTraditional, OutputLanguage::French, OutputLanguage::Russian, OutputLanguage::Spanish, OutputLanguage::Arabic, OutputLanguage::Japanese, OutputLanguage::Korean, OutputLanguage::Vietnamese] {
            let text = actual_leaf_text(run.statement_results.last().unwrap(), language);
            assert!(!text.rule_name.is_empty());
            assert!(text.message.ends_with(&law));
        }
    }
}

#[test]
fn persistent_rule_tracers_pass_without_trust() {
    for code in [
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/proof_nodes/atomic/by_builtin_rule/log_strict_decreasing_unit_interval.lit")),
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/proof_nodes/atomic/by_builtin_rule/log_weak_decreasing_unit_interval.lit")),
    ] { check(&mut runtime(OutputLanguage::English), code, true); }
}
