use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    AtomicExceptEqualityFactSearchedProof, EqualFactSearchedProof,
    VerifyAtomicExceptEqualityFactResult, VerifyEqualityResult,
};
use crate::execute::execute_fact_stmt::verify_forall_fact::{
    VerifyForallFactProof, VerifyForallFactResult,
};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState, VerifyStateLevel};
use crate::execute::{ExecFactStmtResult, ExecStmtResult};
use crate::json_output::explain::BuiltinRuleText;
use crate::json_output::json_keys::localize_key;
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;
use std::collections::BTreeSet;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}

fn check(rt: &mut Runtime, code: &str, accepted: bool) -> JsonValue {
    let run = rt.run_litex_code(code).expect("public Runtime");
    assert!(run.session_error.is_none(), "{code}");
    assert_eq!(run.success, accepted, "{code}");
    crate::json_output::project_run_detailed(&run, rt, "eval", None)
}

fn find_rule<'a>(value: &'a JsonValue, name: &str) -> Option<&'a JsonValue> {
    match value {
        JsonValue::Object(fields) => {
            if fields
                .keys_in_order()
                .into_iter()
                .any(|k| fields.get(&k).and_then(|v| v.as_str().ok()) == Some(name))
            {
                return Some(value);
            }
            fields
                .keys_in_order()
                .into_iter()
                .find_map(|k| find_rule(fields.get(&k).unwrap(), name))
        }
        JsonValue::Array(items) => items.iter().find_map(|v| find_rule(v, name)),
        _ => None,
    }
}

fn contains_string(value: &JsonValue, text: &str) -> bool {
    match value {
        JsonValue::String(s) => s == text,
        JsonValue::Object(fields) => fields
            .keys_in_order()
            .into_iter()
            .any(|k| contains_string(fields.get(&k).unwrap(), text)),
        JsonValue::Array(items) => items.iter().any(|v| contains_string(v, text)),
        _ => false,
    }
}

#[test]
fn factorial_weak_domains_and_order_directions_pass() {
    for m in ["N", "N+"] {
        for n in ["N", "N+"] {
            for (premise, goal) in [
                ("m<=n", "factorial(m)<=factorial(n)"),
                ("n>=m", "factorial(n)>=factorial(m)"),
            ] {
                let code = format!("forall m {m},n {n}:\n    {premise}\n    =>:\n        {goal}\n");
                let json = check(&mut runtime(OutputLanguage::English), &code, true);
                assert!(find_rule(&json, "FactorialMonotone").is_some());
            }
        }
    }
}

#[test]
fn factorial_strict_smaller_positive_and_refinements_pass() {
    for code in [
        "forall m N+,n N:\n    m<n\n    =>:\n        factorial(m)<factorial(n)\n",
        "forall m N+,n N+:\n    n>m\n    =>:\n        factorial(n)>factorial(m)\n",
        "forall m,n N:\n    0<m\n    m<n\n    =>:\n        m $in N+\n        factorial(m)<factorial(n)\n",
    ] {
        let json=check(&mut runtime(OutputLanguage::English),code,true);
        assert!(find_rule(&json,"FactorialStrictMonotone").is_some());
    }
}

#[test]
fn factorial_actual_premise_citations_survive_english_and_chinese() {
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        for (code,rule_name,proof_fields) in [
            ("forall m,n N:\n    m<=n\n    =>:\n        factorial(m)<=factorial(n)\n", "FactorialMonotone", vec!["argument_order"]),
            ("forall m,n N:\n    m $in N+\n    m<n\n    =>:\n        factorial(m)<factorial(n)\n", "FactorialStrictMonotone", vec!["positive_smaller","argument_order"]),
            ("forall m,n N:\n    n>=m\n    =>:\n        factorial(n)>=factorial(m)\n", "FactorialMonotone", vec!["argument_order"]),
            ("forall m,n N:\n    m $in N+\n    n>m\n    =>:\n        factorial(n)>factorial(m)\n", "FactorialStrictMonotone", vec!["positive_smaller","argument_order"]),
        ] {
            let json=check(&mut runtime(language),code,true);
            let key=|s|localize_key(s,language);
            let statement=&json.as_object().unwrap().get(&key("statement_results")).unwrap().as_array().unwrap()[0];
            let assumptions=statement.as_object().unwrap().get(&key("verify")).unwrap().as_object().unwrap().get(&key("assumed_dom_facts")).unwrap().as_array().unwrap();
            assert_eq!(assumptions.len(),proof_fields.len());
            let rule=find_rule(&json,rule_name).unwrap().as_object().unwrap();
            for (field,assumption) in proof_fields.iter().zip(assumptions) {
                let stores=assumption.as_object().unwrap().get(&key("store_and_infer")).unwrap().as_object().unwrap().get(&key("stores")).unwrap().as_array().unwrap();
                let source_id=stores[0].as_object().unwrap().get(&key("fact_id")).unwrap().as_str().unwrap();
                assert!(contains_string(rule.get(&key(field)).unwrap(),source_id),"missing actual {field} source {source_id}");
            }
        }
    }
}

#[test]
fn lcm_both_operands_and_equality_directions_pass_with_parent_wd() {
    for (side, rule) in [
        ("a", "LcmLeftAbsDivisibility"),
        ("b", "LcmRightAbsDivisibility"),
    ] {
        for reverse in [false, true] {
            let remainder = format!("lcm(a,b)%abs({side})");
            let goal = if reverse {
                format!("0={remainder}")
            } else {
                format!("{remainder}=0")
            };
            let code = format!("forall a,b Z*:\n    {goal}\n");
            let json = check(&mut runtime(OutputLanguage::English), &code, true);
            assert!(find_rule(&json, rule).is_some());
        }
    }
    for code in [
        "forall a Z*,b Z:\n    lcm(a,b)%abs(a)=0\n",
        "forall a Z,b Z*:\n    lcm(a,b)%abs(b)=0\n",
        "forall a Z*:\n    lcm(a,0)%abs(a)=0\n",
        "forall a Z*:\n    lcm(0,a)%abs(a)=0\n",
    ] {
        check(&mut runtime(OutputLanguage::English), code, true);
    }
}

#[test]
fn factorial_false_orders_and_lcm_false_or_wd_invalid_controls_reject() {
    for code in [
        "forall m,n N:\n    m<n\n    =>:\n        factorial(m)<factorial(n)\n",
        "forall m N+,n N:\n    m<=n\n    =>:\n        factorial(m)<factorial(n)\n",
        "forall m,n N:\n    factorial(m)<=factorial(n)\n",
        "forall m,n N:\n    m<n\n    =>:\n        factorial(n)<=factorial(m)\n",
        "factorial(0)<factorial(1)\n",
        "forall m,n R:\n    m<n\n    =>:\n        factorial(m)<factorial(n)\n",
        "forall a,b,c Z*:\n    lcm(a,b)%abs(c)=0\n",
        "forall a,b Z*:\n    lcm(a,b)%abs(a)=1\n",
        "forall a,b Z:\n    lcm(a,b)%abs(a)=0\n",
        "forall a Z*:\n    lcm(0,a)%abs(0)=0\n",
        "forall a,b R:\n    lcm(a,b)%abs(a)=0\n",
    ] {
        check(&mut runtime(OutputLanguage::English), code, false);
    }
}

#[test]
fn factorial_and_lcm_respect_the_parent_search_ceiling() {
    for code in [
        "forall m,n N:\n    m<=n\n    =>:\n        factorial(m)<=factorial(n)\n",
        "forall m N+,n N:\n    m<n\n    =>:\n        factorial(m)<factorial(n)\n",
        "forall a,b Z*:\n    lcm(a,b)%abs(a)=0\n",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let tokens = Tokenizer::new()
            .tokenize(code, rt.current_file.clone())
            .unwrap();
        let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
            panic!("fact")
        };
        for level in [
            VerifyStateLevel::Direct,
            VerifyStateLevel::KnownSpecialProperty,
        ] {
            assert!(rt
                .verify_fact(&goal, VerifyState::new(level))
                .unwrap()
                .is_failed());
        }
        assert!(!rt
            .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
            .unwrap()
            .is_failed());
    }
}

#[test]
fn failed_statement_does_not_publish_and_valid_reuse_survives() {
    let mut rt = runtime(OutputLanguage::English);
    let bad = "forall m,n N:\n    m<n\n    =>:\n        factorial(m)<factorial(n)\n";
    check(&mut rt, bad, false);
    let tokens = Tokenizer::new()
        .tokenize(bad, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    assert!(rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::Direct))
        .unwrap()
        .is_failed());
    let good = "forall m N+,n N:\n    m<n\n    =>:\n        factorial(m)<factorial(n)\n";
    check(&mut rt, good, true);
    check(&mut rt, good, true);
    check(&mut rt, bad, false);
    check(&mut rt, "forall a Z*:\n    lcm(0,a)%abs(0)=0\n", false);
    let lcm = "forall a,b Z*:\n    lcm(a,b)%abs(b)=0\n";
    check(&mut rt, lcm, true);
    check(&mut rt, lcm, true);
    check(&mut rt, "forall a,b,c Z*:\n    lcm(a,b)%abs(c)=0\n", false);
    check(&mut rt, lcm, true);
}

#[test]
fn dedicated_persistent_factorial_and_lcm_tracers_pass() {
    for code in [
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_rule/factorial_monotonicity.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_rule/lcm_input_divisibility.lit"
        )),
    ] {
        check(&mut runtime(OutputLanguage::English), code, true);
    }
}

fn actual_leaf_text(result: &ExecStmtResult, language: OutputLanguage) -> BuiltinRuleText {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) = result else {
        panic!("fact success")
    };
    let VerifyFactResult::ForallFact(f) = &s.verify_result else {
        panic!("forall")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) = &**f
    else {
        panic!("local forall")
    };
    match &p.proved_then_facts[0].verify_result {
        VerifyFactResult::AtomicExceptEquality(a) => {
            let VerifyAtomicExceptEqualityFactResult::Success(p) = &**a else {
                panic!("atomic success")
            };
            let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) = &p.searched_proof
            else {
                panic!("actual builtin")
            };
            rule.rule_name_and_message(language)
        }
        VerifyFactResult::Equality(e) => {
            let VerifyEqualityResult::Success(p) = &**e else {
                panic!("equal success")
            };
            let EqualFactSearchedProof::ByBuiltinRule(rule) = &p.searched_proof else {
                panic!("actual equal builtin")
            };
            rule.rule_name_and_message(language)
        }
        _ => panic!("selected atomic family"),
    }
}

#[test]
fn four_actual_winning_leaves_own_distinct_ten_language_explanations() {
    for (code, law) in [
        (
            "forall m,n N:\n    m<=n\n    =>:\n        factorial(m)<=factorial(n)\n",
            "m,n in N, m<=n",
        ),
        (
            "forall m N+,n N:\n    m<n\n    =>:\n        factorial(m)<factorial(n)\n",
            "m in N+, n in N, m<n",
        ),
        (
            "forall a,b Z*:\n    lcm(a,b)%abs(a)=0\n",
            "abs(a)!=0 => lcm(a,b)%abs(a)=0",
        ),
        (
            "forall a,b Z*:\n    lcm(a,b)%abs(b)=0\n",
            "abs(b)!=0 => lcm(a,b)%abs(b)=0",
        ),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.success);
        let mut names = BTreeSet::new();
        for language in [
            OutputLanguage::English,
            OutputLanguage::Chinese,
            OutputLanguage::ChineseTraditional,
            OutputLanguage::French,
            OutputLanguage::Russian,
            OutputLanguage::Spanish,
            OutputLanguage::Arabic,
            OutputLanguage::Japanese,
            OutputLanguage::Korean,
            OutputLanguage::Vietnamese,
        ] {
            let text = actual_leaf_text(&run.statement_results[0], language);
            assert!(!text.rule_name.is_empty());
            assert!(text.message.contains(law), "{law}: {}", text.message);
            assert!(
                names.insert(text.rule_name),
                "language fell back to an earlier name"
            );
        }
        assert_eq!(names.len(), 10);
    }
}

#[test]
fn positive_integer_both_surfaces_keep_actual_guard_citations() {
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        for domain in ["N", "Z"] {
            for bound in ["0<x", "x>0"] {
                let code = format!("forall x {domain}:\n    {bound}\n    =>:\n        x $in N+\n");
                let json = check(&mut runtime(language), &code, true);
                let rule = find_rule(&json, "PositiveIntegerInNPos")
                    .expect("actual integer-positive leaf")
                    .as_object()
                    .unwrap();
                let key = |s| localize_key(s, language);
                let statement = &json
                    .as_object()
                    .unwrap()
                    .get(&key("statement_results"))
                    .unwrap()
                    .as_array()
                    .unwrap()[0];
                let dom = &statement
                    .as_object()
                    .unwrap()
                    .get(&key("verify"))
                    .unwrap()
                    .as_object()
                    .unwrap()
                    .get(&key("assumed_dom_facts"))
                    .unwrap()
                    .as_array()
                    .unwrap()[0];
                let stores = dom
                    .as_object()
                    .unwrap()
                    .get(&key("store_and_infer"))
                    .unwrap()
                    .as_object()
                    .unwrap()
                    .get(&key("stores"))
                    .unwrap()
                    .as_array()
                    .unwrap();
                let source = stores[0]
                    .as_object()
                    .unwrap()
                    .get(&key("fact_id"))
                    .unwrap()
                    .as_str()
                    .unwrap();
                assert!(contains_string(
                    rule.get(&key("positive_proof")).unwrap(),
                    source
                ));
            }
        }
    }
}

#[test]
fn positive_integer_reverse_guard_rejects_zero_fraction_and_weak_bound() {
    for code in [
        "0 $in N+\n",
        "(-1) $in N+\n",
        "1/2 $in N+\n",
        "forall x N:\n    0<=x\n    =>:\n        x $in N+\n",
        "forall x R:\n    0<x\n    =>:\n        x $in N+\n",
    ] {
        check(&mut runtime(OutputLanguage::English), code, false);
    }
    let mut rt = runtime(OutputLanguage::English);
    let code = "forall x Z:\n    0<x\n    =>:\n        x $in N+\n";
    let tokens = Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    for level in [
        VerifyStateLevel::Direct,
        VerifyStateLevel::KnownSpecialProperty,
    ] {
        assert!(rt
            .verify_fact(&goal, VerifyState::new(level))
            .unwrap()
            .is_failed());
    }
    assert!(!rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
}
