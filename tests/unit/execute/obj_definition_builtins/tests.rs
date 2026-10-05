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

fn languages() -> [OutputLanguage; 10] {
    [
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
    ]
}

#[test]
fn seven_actual_typed_leaves_and_ten_language_consumers() {
    for (code, name, law) in [
        (
            "forall x R:\n    cos(x)!=0\n    =>:\n        tan(x)=sin(x)/cos(x)\n",
            "TanQuotientDefinition",
            "x in R, cos(x)!=0 => tan(x)=sin(x)/cos(x)",
        ),
        (
            "forall x R:\n    sin(x)!=0\n    =>:\n        cot(x)=cos(x)/sin(x)\n",
            "CotQuotientDefinition",
            "x in R, sin(x)!=0 => cot(x)=cos(x)/sin(x)",
        ),
        (
            "forall a Z,b N+:\n    gcd(a,b)=gcd(b,a%b)\n",
            "GcdEuclideanStep",
            "a,b in Z, b!=0 => gcd(a,b)=gcd(b,a%b)",
        ),
        (
            "forall x R:\n    floor(x)<=x\n",
            "FloorLowerBound",
            "x in R => floor(x)<=x",
        ),
        (
            "forall x R:\n    x<floor(x)+1\n",
            "FloorStrictUpperBound",
            "x in R => x<floor(x)+1",
        ),
        (
            "forall x R:\n    ceil(x)-1<x\n",
            "CeilStrictLowerBound",
            "x in R => ceil(x)-1<x",
        ),
        (
            "forall x R:\n    x<=ceil(x)\n",
            "CeilUpperBound",
            "x in R => x<=ceil(x)",
        ),
    ] {
        for language in languages() {
            let mut rt = runtime(language);
            let mut run = rt.run_litex_code(code).unwrap();
            assert!(run.success, "{code}");
            let detailed = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
            let leaf = find_rule(&detailed, name).expect("actual detailed leaf");
            assert_eq!(leaf.as_object().unwrap().keys_in_order().len(), 2);
            let text = actual_leaf_text(run.statement_results.last().unwrap(), language);
            assert!(!text.rule_name.is_empty());
            assert!(text.message.ends_with(law), "{}", text.message);
            // The actual public output path consumes this leaf in every language.
            let normal = project_actual_child_normal(run.statement_results.pop().unwrap(), &rt);
            assert!(contains_string(&normal, &text.rule_name));
            assert!(contains_string(&normal, &text.message));
        }
    }
}

#[test]
fn legal_domains_and_symmetric_equality() {
    for domain in ["Z", "N", "Q", "R"] {
        check(&mut runtime(OutputLanguage::English),
            &format!("forall x {domain}:\n    floor(x)<=x\n    x<floor(x)+1\n    ceil(x)-1<x\n    x<=ceil(x)\n"), true);
    }
    for code in [
        "forall x R:\n    cos(x)!=0\n    =>:\n        sin(x)/cos(x)=tan(x)\n",
        "forall x R:\n    sin(x)!=0\n    =>:\n        cos(x)/sin(x)=cot(x)\n",
        "forall a Z,b N+:\n    gcd(b,a%b)=gcd(a,b)\n",
        "forall a Z,b Z*:\n    gcd(a,b)=gcd(b,a%b)\n",
    ] {
        check(&mut runtime(OutputLanguage::English), code, true);
    }
}

#[test]
fn false_bounds_mismatched_arguments_and_missing_guards_reject() {
    for code in [
        "floor(0)<0\n",
        "ceil(0)>0\n",
        "forall x R:\n    x<=floor(x)\n",
        "forall x R:\n    ceil(x)<=x\n",
        "forall x R:\n    floor(x)<x\n",
        "forall x R:\n    x<ceil(x)\n",
        "forall x R:\n    x<floor(x)\n",
        "forall x R:\n    ceil(x)<x\n",
        "forall x,y R:\n    floor(x)<=y\n",
        "forall x,y R:\n    x<floor(y)+1\n",
        "forall x,y R:\n    ceil(y)-1<x\n",
        "forall x,y R:\n    x<=ceil(y)\n",
        "floor(i)<=1\n",
        "0<=ceil(i)\n",
        "forall x R:\n    tan(x)=sin(x)/cos(x)\n",
        "forall x R:\n    cot(x)=cos(x)/sin(x)\n",
        "cot(0)=cos(0)/sin(0)\n",
        "forall x,y R:\n    cos(x)!=0\n    cos(y)!=0\n    =>:\n        tan(x)=sin(y)/cos(y)\n",
        "forall x,y R:\n    sin(x)!=0\n    sin(y)!=0\n    =>:\n        cot(x)=cos(y)/sin(y)\n",
        "forall x R:\n    cos(x)!=0\n    sin(x)!=0\n    =>:\n        tan(x)=cos(x)/sin(x)\n",
        "forall a Z:\n    gcd(a,0)=gcd(0,a%0)\n",
        "forall a Z,b N+:\n    gcd(a,b)=gcd(b,b%a)\n",
        "forall a,c Z,b N+:\n    gcd(a,b)=gcd(b,c%b)\n",
        "forall a R,b N+:\n    gcd(a,b)=gcd(b,a%b)\n",
    ] {
        check(&mut runtime(OutputLanguage::English), code, false);
    }
}

#[test]
fn finite_bounds_retain_member_premise_and_carrier_evidence() {
    for (goal, name, native) in [
        (
            "x<=finite_set_max(S)",
            "FiniteSetMaxMemberLe",
            "finite_set_max",
        ),
        (
            "finite_set_min(S)<=x",
            "FiniteSetMinMemberLe",
            "finite_set_min",
        ),
    ] {
        let code = format!("forall S finite_set,x S:\n    $is_nonempty_set(S)\n    S $subset R\n    =>:\n        {goal}\n");
        for language in languages() {
            let mut rt = runtime(language);
            let mut run = rt.run_litex_code(&code).unwrap();
            assert!(run.success, "{code}");
            let detailed = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
            let leaf = find_rule(&detailed, name).expect("existing member-order leaf");
            let fields = leaf.as_object().unwrap();
            let key = crate::json_output::json_keys::localize_key("member_proof", language);
            assert!(fields.get(&key).is_some(), "member premise missing");
            assert!(contains_string(&detailed, "known_subset"));
            assert!(
                find_rule(&detailed, native).is_some(),
                "intrinsic extremum carrier missing"
            );
            let text = actual_leaf_text(run.statement_results.last().unwrap(), language);
            let normal = project_actual_child_normal(run.statement_results.pop().unwrap(), &rt);
            assert!(contains_string(&normal, &text.message));
        }
    }
}

#[test]
fn finite_carriers_and_subset_transport_are_cite_only_at_direct() {
    for goal in [
        "x $in R",
        "finite_set_max(S) $in R",
        "finite_set_min(S) $in C",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let code = format!("forall S finite_set,x S:\n    $is_nonempty_set(S)\n    S $subset R\n    =>:\n        {goal}\n");
        let tokens = Tokenizer::new()
            .tokenize(&code, rt.current_file.clone())
            .unwrap();
        let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
            panic!("fact")
        };
        let before = memory_sizes(&rt);
        assert!(!rt
            .verify_fact(&fact, VerifyState::new(VerifyStateLevel::Direct))
            .unwrap()
            .is_failed());
        assert_eq!(
            memory_sizes(&rt),
            before,
            "Direct search published evidence"
        );
    }
    for code in [
        "forall S finite_set,x R:\n    $is_nonempty_set(S)\n    S $subset R\n    =>:\n        x<=finite_set_max(S)\n",
        "forall S finite_set,x S:\n    $is_nonempty_set(S)\n    =>:\n        x<=finite_set_max(S)\n",
        "forall S finite_set:\n    S $subset R\n    =>:\n        finite_set_max(S) $in R\n",
        "finite_set_max({}) $in R\n",
        "finite_set_min({i}) $in R\n",
        "forall S set,x S:\n    x $in R\n",
        "forall S,T set,x S:\n    T $subset R\n    =>:\n        x $in R\n",
        "forall S set,x S:\n    R $subset S\n    =>:\n        x $in R\n",
    ] {
        check(&mut runtime(OutputLanguage::English), code, false);
    }
}

#[test]
fn restricted_rule_entry_and_failed_publication() {
    let mut rt = runtime(OutputLanguage::English);
    let code = "forall x R:\n    floor(x)<=x\n";
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
    // A failed theorem and its temporary binders must not contaminate the session.
    for accepted in [false, true, false, true] {
        check(
            &mut rt,
            if accepted {
                code
            } else {
                "forall x,y R:\n    floor(x)<=y\n"
            },
            accepted,
        );
    }
}

// Project the actual executed then-fact through Normal's atomic consumer.
// Normal intentionally summarizes a whole forall with its compound proof label.
fn project_actual_child_normal(result: ExecStmtResult, rt: &Runtime) -> JsonValue {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) = result else {
        panic!("fact")
    };
    let VerifyFactResult::ForallFact(f) = s.verify_result else {
        panic!("forall")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(mut p)) = *f
    else {
        panic!("local forall")
    };
    let child = p.proved_then_facts.remove(0);
    let executed = ExecStmtResult::Fact(ExecFactStmtResult::Success(
        crate::execute::execute_fact_stmt::result::ExecFactStmtSuccessResult {
            verify_result: child.verify_result,
            store_and_infer_result: child.store_and_infer,
        },
    ));
    crate::json_output::project_stmt_normal(&executed, rt)
}

fn memory_sizes(rt: &Runtime) -> Vec<(usize, usize)> {
    rt.execution_environments_stack
        .iter()
        .map(|env| {
            (
                env.facts.facts_by_id.len(),
                env.well_defined_objects.object_to_wd_id.len(),
            )
        })
        .collect()
}

#[test]
fn direct_carrier_leaves_keep_two_citations_and_ten_normal_outputs() {
    for goal in [
        "x $in R",
        "finite_set_max(S) $in R",
        "finite_set_min(S) $in R",
    ] {
        let code = format!("forall S finite_set,x S:\n    $is_nonempty_set(S)\n    S $subset R\n    =>:\n        {goal}\n");
        for language in languages() {
            let mut rt = runtime(language);
            let mut run = rt.run_litex_code(&code).unwrap();
            assert!(run.success);
            let detail = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
            if goal == "x $in R" {
                let proof = find_rule(&detail, "known_subset").unwrap();
                let fields = proof.as_object().unwrap();
                for key in ["member_proof", "subset_proof"] {
                    let key = crate::json_output::json_keys::localize_key(key, language);
                    let premise = fields.get(&key).unwrap();
                    let cite_key =
                        crate::json_output::json_keys::localize_key("cite_fact_id", language);
                    assert!(
                        find_rule(premise, "by_known_atomic_fact").is_some()
                            || has_key(premise, &cite_key)
                    );
                }
            }
            let normal = project_actual_child_normal(run.statement_results.pop().unwrap(), &rt);
            let expected = crate::json_output::explain::explain_searched_proof_why(
                "structural_membership",
                language,
            );
            assert!(contains_string(&normal, &expected.message));
            assert!(contains_string(&normal, &expected.rule_name));
        }
    }
    // Direct may cite one subset edge; it cannot derive a new intermediate edge.
    let mut rt = runtime(OutputLanguage::English);
    let code = "forall S,T set,x S:\n    S $subset T\n    T $subset R\n    =>:\n        x $in R\n";
    let tokens = Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    assert!(rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::Direct))
        .unwrap()
        .is_failed());
}

fn has_key(value: &JsonValue, key: &str) -> bool {
    match value {
        JsonValue::Object(fields) => {
            fields.get(key).is_some()
                || fields
                    .keys_in_order()
                    .iter()
                    .any(|k| has_key(fields.get(k).unwrap(), key))
        }
        JsonValue::Array(items) => items.iter().any(|v| has_key(v, key)),
        _ => false,
    }
}
