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

fn find_rule(value: &JsonValue, name: &str) -> Option<JsonValue> {
    match value {
        JsonValue::Object(fields) => {
            if fields
                .keys_in_order()
                .into_iter()
                .any(|k| fields.get(&k).and_then(|v| v.as_str().ok()) == Some(name))
            {
                return Some(value.clone());
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
fn all_native_leaf_surfaces_and_directions_pass() {
    for (function, domain) in [("exp", "R"), ("ln", "R+")] {
        for weak in [false, true] {
            for reflection in [false, true] {
                for source_reverse in [false, true] {
                    for goal_reverse in [false, true] {
                        let op = if weak { "<=" } else { "<" };
                        let reverse = if weak { ">=" } else { ">" };
                        let (a, b) = if reflection {
                            (format!("{function}(a)"), format!("{function}(b)"))
                        } else {
                            ("a".to_string(), "b".to_string())
                        };
                        let (left, right) = if reflection {
                            ("a".to_string(), "b".to_string())
                        } else {
                            (format!("{function}(a)"), format!("{function}(b)"))
                        };
                        let source = if source_reverse {
                            format!("{b}{reverse}{a}")
                        } else {
                            format!("{a}{op}{b}")
                        };
                        let goal = if goal_reverse {
                            format!("{right}{reverse}{left}")
                        } else {
                            format!("{left}{op}{right}")
                        };
                        let code = format!(
                            "forall a,b {domain}:\n    {source}\n    =>:\n        {goal}\n"
                        );
                        let rule = format!(
                            "{}{}{}",
                            if function == "exp" { "Exp" } else { "Ln" },
                            if weak { "Weak" } else { "Strict" },
                            if reflection {
                                "OrderReflection"
                            } else {
                                "Monotone"
                            }
                        );
                        let json = check(&mut runtime(OutputLanguage::English), &code, true);
                        assert!(find_rule(&json, &rule).is_some());
                    }
                }
            }
        }
    }
}

#[test]
fn native_source_citations_survive_both_orientations_and_languages() {
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        for (code, name, field) in [
            (
                "forall a,b R:\n    a<b\n    =>:\n        exp(a)<exp(b)\n",
                "ExpStrictMonotone",
                "argument_order",
            ),
            (
                "forall a,b R:\n    b>a\n    =>:\n        exp(a)<exp(b)\n",
                "ExpStrictMonotone",
                "argument_order",
            ),
            (
                "forall a,b R:\n    exp(a)<exp(b)\n    =>:\n        a<b\n",
                "ExpStrictOrderReflection",
                "image_order",
            ),
            (
                "forall a,b R:\n    exp(b)>exp(a)\n    =>:\n        a<b\n",
                "ExpStrictOrderReflection",
                "image_order",
            ),
            (
                "forall a,b R:\n    a<=b\n    =>:\n        exp(a)<=exp(b)\n",
                "ExpWeakMonotone",
                "argument_order",
            ),
            (
                "forall a,b R:\n    b>=a\n    =>:\n        exp(a)<=exp(b)\n",
                "ExpWeakMonotone",
                "argument_order",
            ),
            (
                "forall a,b R:\n    exp(a)<=exp(b)\n    =>:\n        a<=b\n",
                "ExpWeakOrderReflection",
                "image_order",
            ),
            (
                "forall a,b R:\n    exp(b)>=exp(a)\n    =>:\n        a<=b\n",
                "ExpWeakOrderReflection",
                "image_order",
            ),
            (
                "forall a,b R+:\n    a<b\n    =>:\n        ln(a)<ln(b)\n",
                "LnStrictMonotone",
                "argument_order",
            ),
            (
                "forall a,b R+:\n    b>a\n    =>:\n        ln(a)<ln(b)\n",
                "LnStrictMonotone",
                "argument_order",
            ),
            (
                "forall a,b R+:\n    ln(a)<ln(b)\n    =>:\n        a<b\n",
                "LnStrictOrderReflection",
                "image_order",
            ),
            (
                "forall a,b R+:\n    ln(b)>ln(a)\n    =>:\n        a<b\n",
                "LnStrictOrderReflection",
                "image_order",
            ),
            (
                "forall a,b R+:\n    a<=b\n    =>:\n        ln(a)<=ln(b)\n",
                "LnWeakMonotone",
                "argument_order",
            ),
            (
                "forall a,b R+:\n    b>=a\n    =>:\n        ln(a)<=ln(b)\n",
                "LnWeakMonotone",
                "argument_order",
            ),
            (
                "forall a,b R+:\n    ln(a)<=ln(b)\n    =>:\n        a<=b\n",
                "LnWeakOrderReflection",
                "image_order",
            ),
            (
                "forall a,b R+:\n    ln(b)>=ln(a)\n    =>:\n        a<=b\n",
                "LnWeakOrderReflection",
                "image_order",
            ),
        ] {
            let json = check(&mut runtime(language), code, true);
            let key = |s| localize_key(s, language);
            let statement = &json
                .as_object()
                .unwrap()
                .get(&key("statement_results"))
                .unwrap()
                .as_array()
                .unwrap()[0];
            let assumptions = statement
                .as_object()
                .unwrap()
                .get(&key("verify"))
                .unwrap()
                .as_object()
                .unwrap()
                .get(&key("assumed_dom_facts"))
                .unwrap()
                .as_array()
                .unwrap();
            assert_eq!(assumptions.len(), 1);
            let stores = assumptions[0]
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
            let source_id = stores[0]
                .as_object()
                .unwrap()
                .get(&key("fact_id"))
                .unwrap()
                .as_str()
                .unwrap();
            let leaf_value = find_rule(&json, name).unwrap();
            let leaf = leaf_value.as_object().unwrap();
            assert!(contains_string(leaf.get(&key(field)).unwrap(), source_id));
        }
    }
}

#[test]
fn actual_eight_winning_leaves_own_ten_language_guarded_explanations() {
    for (code, name, field) in [
        (
            "forall a,b R:\n    a<b\n    =>:\n        exp(a)<exp(b)\n",
            "ExpStrictMonotone",
            "argument_order",
        ),
        (
            "forall a,b R:\n    exp(a)<exp(b)\n    =>:\n        a<b\n",
            "ExpStrictOrderReflection",
            "image_order",
        ),
        (
            "forall a,b R:\n    a<=b\n    =>:\n        exp(a)<=exp(b)\n",
            "ExpWeakMonotone",
            "argument_order",
        ),
        (
            "forall a,b R:\n    exp(a)<=exp(b)\n    =>:\n        a<=b\n",
            "ExpWeakOrderReflection",
            "image_order",
        ),
        (
            "forall a,b R+:\n    a<b\n    =>:\n        ln(a)<ln(b)\n",
            "LnStrictMonotone",
            "argument_order",
        ),
        (
            "forall a,b R+:\n    ln(a)<ln(b)\n    =>:\n        a<b\n",
            "LnStrictOrderReflection",
            "image_order",
        ),
        (
            "forall a,b R+:\n    a<=b\n    =>:\n        ln(a)<=ln(b)\n",
            "LnWeakMonotone",
            "argument_order",
        ),
        (
            "forall a,b R+:\n    ln(a)<=ln(b)\n    =>:\n        a<=b\n",
            "LnWeakOrderReflection",
            "image_order",
        ),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.success);
        let domain = if name.starts_with("Ln") {
            "a,b in R+"
        } else {
            "a,b in R"
        };
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
            let premise = code.lines().nth(1).unwrap().trim();
            let goal = code.lines().last().unwrap().trim();
            let law = format!("{domain}, {premise} => {goal}");
            assert!(text.message.ends_with(&law), "{name} {field}");
            assert!(!text.rule_name.trim().is_empty());
        }
        // Simplified/traditional wording may legitimately coincide.
        // Check each selected language against the actual mathematical input,
        // rather than inventing a title uniqueness requirement.
    }
}

#[test]
fn existing_subdomains_and_published_domain_refinements_pass() {
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b Q:\n    a<b\n    =>:\n        exp(a)<exp(b)\n",
        true,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b Q:\n    exp(a)<exp(b)\n    =>:\n        a<b\n",
        true,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b Z:\n    a<b\n    =>:\n        exp(a)<exp(b)\n",
        true,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b Z:\n    exp(a)<exp(b)\n    =>:\n        a<b\n",
        true,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b N:\n    a<b\n    =>:\n        exp(a)<exp(b)\n",
        true,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b N:\n    exp(a)<exp(b)\n    =>:\n        a<b\n",
        true,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R+:\n    a<b\n    =>:\n        exp(a)<exp(b)\n",
        true,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R+:\n    exp(a)<exp(b)\n    =>:\n        a<b\n",
        true,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b N+:\n    a<b\n    =>:\n        ln(a)<ln(b)\n",
        true,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b N+:\n    ln(a)<ln(b)\n    =>:\n        a<b\n",
        true,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b Z+:\n    a<b\n    =>:\n        ln(a)<ln(b)\n",
        true,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b Z+:\n    ln(a)<ln(b)\n    =>:\n        a<b\n",
        true,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b Q+:\n    a<b\n    =>:\n        ln(a)<ln(b)\n",
        true,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b Q+:\n    ln(a)<ln(b)\n    =>:\n        a<b\n",
        true,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b C:\n    a $in R\n    b $in R\n    a<b\n    =>:\n        exp(a)<exp(b)\n",
        true,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b C:\n    a $in R+\n    b $in R+\n    a<b\n    =>:\n        ln(a)<ln(b)\n",
        true,
    );
    check(&mut runtime(OutputLanguage::English),"forall a,b R:\n    0<a\n    0<b\n    a<b\n    =>:\n        a $in R+\n        b $in R+\n        ln(a)<ln(b)\n",true);
}

#[test]
fn wrong_orders_and_invalid_domains_remain_rejected() {
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R:\n    exp(a)<exp(b)\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R:\n    a<b\n    =>:\n        exp(b)<exp(a)\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R:\n    a<=b\n    =>:\n        exp(a)<exp(b)\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R:\n    exp(a)<=exp(b)\n    =>:\n        a<b\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R:\n    exp(a)<exp(b)\n    =>:\n        b<a\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R:\n    a=b\n    =>:\n        exp(a)<exp(b)\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R:\n    a<b\n    =>:\n        exp(a)<ln(b)\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R+:\n    ln(a)<ln(b)\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R+:\n    a<b\n    =>:\n        ln(b)<ln(a)\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R+:\n    a<=b\n    =>:\n        ln(a)<ln(b)\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R+:\n    ln(a)<=ln(b)\n    =>:\n        a<b\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R+:\n    ln(a)<ln(b)\n    =>:\n        b<a\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R+:\n    a=b\n    =>:\n        ln(a)<ln(b)\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b C:\n    a=b\n    =>:\n        exp(a)<=exp(b)\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "ln(0)<=ln(1)\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "ln(-1)<ln(1)\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "exp(1)<exp(0)\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "ln(2)<ln(1)\n",
        false,
    );
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,b R+:\n    a<b\n    =>:\n        ln(ln(a))<ln(ln(b))\n",
        false,
    );
}

#[test]
fn parent_truth_ceiling_cannot_reenter_forward_or_reflection() {
    for code in [
        "forall a,b R:\n    a<b\n    =>:\n        exp(a)<exp(b)\n",
        "forall a,b R:\n    exp(a)<exp(b)\n    =>:\n        a<b\n",
        "forall a,b R:\n    a<=b\n    =>:\n        exp(a)<=exp(b)\n",
        "forall a,b R:\n    exp(a)<=exp(b)\n    =>:\n        a<=b\n",
        "forall a,b R+:\n    a<b\n    =>:\n        ln(a)<ln(b)\n",
        "forall a,b R+:\n    ln(a)<ln(b)\n    =>:\n        a<b\n",
        "forall a,b R+:\n    a<=b\n    =>:\n        ln(a)<=ln(b)\n",
        "forall a,b R+:\n    ln(a)<=ln(b)\n    =>:\n        a<=b\n",
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
fn failed_statement_does_not_publish_and_legal_reuse_survives() {
    let mut rt = runtime(OutputLanguage::English);
    let bad = "forall a,b R:\n    a<=b\n    =>:\n        exp(a)<exp(b)\n";
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
    let good = "forall a,b R:\n    a<b\n    =>:\n        exp(a)<exp(b)\n";
    check(&mut rt, good, true);
    check(&mut rt, good, true);
    check(&mut rt, bad, false);
    check(
        &mut rt,
        "forall a,b R:\n    ln(a)<ln(b)\n    =>:\n        a<b\n",
        false,
    );
    check(&mut rt, good, true);
}

#[test]
fn persistent_native_order_tracer_passes() {
    check(
        &mut runtime(OutputLanguage::English),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_rule/exp_ln_order.lit"
        )),
        true,
    );
}
