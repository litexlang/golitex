use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{
    EqualFactSearchedProof, EqualitySearchProofByBuiltinRule, VerifyEqualityResult,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::log_algebra_base_proof::LogAlgebraBaseProof;
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
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}

fn input(kind: usize, guard: &str) -> String {
    let (params, target) = match kind {
        0 => ("a,x,y R+", "log(a,x*y)=log(a,x)+log(a,y)"),
        1 => ("a,x,y R+", "log(a,x/y)=log(a,x)-log(a,y)"),
        2 => ("a,x R+", "log(a,1/x)=-log(a,x)"),
        3 => ("a,x R+,n Z", "log(a,x^n)=n*log(a,x)"),
        _ => panic!("four math leaves"),
    };
    format!("forall {params}:\n    {guard}\n    =>:\n        {target}\n")
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

fn assert_base(proof: &LogAlgebraBaseProof, kind: &str) {
    match proof {
        LogAlgebraBaseProof::GreaterThanOne(p) => {
            assert_eq!(kind, "greater_than_one");
            assert!(!p.is_failed());
        }
        LogAlgebraBaseProof::BelowOne(p) => {
            assert_eq!(kind, "below_one");
            assert!(!p.positive_proof.is_failed() && !p.less_than_one_proof.is_failed());
        }
        LogAlgebraBaseProof::PositiveNonunit(p) => {
            assert_eq!(kind, "positive_nonunit");
            assert!(!p.positive_proof.is_failed() && !p.nonunit_proof.is_failed());
        }
    }
}

fn actual_text(result: &ExecStmtResult, kind: &str, language: OutputLanguage) -> BuiltinRuleText {
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
    let VerifyFactResult::Equality(e) = &p.proved_then_facts[0].verify_result else {
        panic!("equality")
    };
    let VerifyEqualityResult::Success(p) = &**e else {
        panic!("equality success")
    };
    let EqualFactSearchedProof::ByBuiltinRule(rule) = &p.searched_proof else {
        panic!("actual builtin")
    };
    match rule {
        EqualitySearchProofByBuiltinRule::LogProduct(p) => {
            assert_base(&p.base_proof, kind);
            assert!(
                !p.left_argument_positive_proof.is_failed()
                    && !p.right_argument_positive_proof.is_failed()
            );
        }
        EqualitySearchProofByBuiltinRule::LogQuotient(p) => {
            assert_base(&p.base_proof, kind);
            assert!(
                !p.numerator_positive_proof.is_failed()
                    && !p.denominator_positive_proof.is_failed()
            );
        }
        EqualitySearchProofByBuiltinRule::LogReciprocal(p) => {
            assert_base(&p.base_proof, kind);
            assert!(!p.argument_positive_proof.is_failed());
        }
        EqualitySearchProofByBuiltinRule::LogArgPower(p) => {
            assert_base(&p.base_proof, kind);
            assert!(!p.argument_positive_proof.is_failed());
        }
        _ => panic!("actual owned log leaf"),
    }
    rule.rule_name_and_message(language)
}

#[test]
fn actual_three_guard_routes_and_four_typed_leaves_keep_ten_language_outputs() {
    let names = ["LogProduct", "LogQuotient", "LogReciprocal", "LogArgPower"];
    for kind in 0..4 {
        for (guard, route) in [
            ("a<1", "below_one"),
            ("1<a", "greater_than_one"),
            ("a!=1", "positive_nonunit"),
        ] {
            for language in OutputLanguage::ALL {
                let mut rt = runtime(language);
                let run = rt.run_litex_code(&input(kind, guard)).unwrap();
                assert!(run.success && run.session_error.is_none());
                let text = actual_text(run.statement_results.last().unwrap(), route, language);
                assert!(!text.rule_name.is_empty() && !text.message.is_empty());
                let json = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
                let leaf = find_rule(&json, names[kind]).unwrap();
                assert!(contains_string(&leaf, route));
                assert!(!leaf
                    .as_object()
                    .unwrap()
                    .keys_in_order()
                    .contains(&"proof_of_requirement_facts"));
            }
        }
    }
}

#[test]
fn reverse_real_guard_citations_and_mandatory_fields_are_exact() {
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        for (name, code, argument_fields) in [
            ("LogProduct", "forall a,x,y R:\n    a>0\n    1>a\n    x>0\n    y>0\n    =>:\n        log(a,x*y)=log(a,x)+log(a,y)\n", vec!["left_argument_positive_proof", "right_argument_positive_proof"]),
            ("LogQuotient", "forall a,x,y R:\n    a>0\n    1>a\n    x>0\n    y>0\n    =>:\n        log(a,x/y)=log(a,x)-log(a,y)\n", vec!["numerator_positive_proof", "denominator_positive_proof"]),
            ("LogReciprocal", "forall a,x R:\n    a>0\n    1>a\n    x>0\n    =>:\n        log(a,1/x)=-log(a,x)\n", vec!["argument_positive_proof"]),
            ("LogArgPower", "forall a,x R,n Z:\n    a>0\n    1>a\n    0<x\n    =>:\n        log(a,x^n)=n*log(a,x)\n", vec!["argument_positive_proof"]),
        ] {
            let mut rt = runtime(language);
            let run = rt.run_litex_code(code).unwrap();
            assert!(run.success && run.session_error.is_none());
            actual_text(run.statement_results.last().unwrap(), "below_one", language);
            let json = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
            let key = |s| localize_key(s, language);
            let statement = &json.as_object().unwrap().get(&key("statement_results")).unwrap().as_array().unwrap()[0];
            let assumptions = statement.as_object().unwrap().get(&key("verify")).unwrap().as_object().unwrap().get(&key("assumed_dom_facts")).unwrap().as_array().unwrap();
            assert_eq!(assumptions.len(), 2 + argument_fields.len());
            let source_id = |i: usize| assumptions[i].as_object().unwrap().get(&key("store_and_infer")).unwrap().as_object().unwrap().get(&key("stores")).unwrap().as_array().unwrap()[0].as_object().unwrap().get(&key("fact_id")).unwrap().as_str().unwrap();
            let leaf = find_rule(&json, name).unwrap();
            let leaf = leaf.as_object().unwrap();
            assert_eq!(leaf.keys_in_order().len(), 3 + argument_fields.len());
            let base = leaf.get(&key("base_proof")).unwrap().as_object().unwrap();
            assert_eq!(base.keys_in_order().len(), 3);
            for (field, i) in [("positive_proof", 0), ("less_than_one_proof", 1)] {
                assert!(contains_string(base.get(&key(field)).unwrap(), source_id(i)), "{field}");
            }
            for (i, field) in argument_fields.iter().enumerate() {
                assert!(contains_string(leaf.get(&key(field)).unwrap(), source_id(i+2)), "{field}");
            }
        }
    }
}

#[test]
fn equality_and_argument_permutations_and_reciprocal_spellings_use_owned_leaves() {
    for code in [
        "forall a,x,y R+:\n    a<1\n    =>:\n        log(a,x)+log(a,y)=log(a,x*y)\n",
        "forall a,x,y R+:\n    1>a\n    =>:\n        log(a,y)+log(a,x)=log(a,x*y)\n",
        "forall a,x R+,n Z:\n    a<1\n    =>:\n        log(a,x^n)=log(a,x)*n\n",
        "forall a,x R+:\n    a<1\n    =>:\n        log(a,1/x)=0-log(a,x)\n",
        "forall a,x R+:\n    a<1\n    =>:\n        log(a,1/x)=(-1)*log(a,x)\n",
        "forall a,x R+:\n    a<1\n    =>:\n        log(a,1/x)=-log(a,x)\n",
    ] {
        check(&mut runtime(OutputLanguage::English), code, true);
    }
}

#[test]
fn illegal_domains_missing_guards_and_false_laws_remain_rejected() {
    for code in [
        "log(1,2*3)=log(1,2)+log(1,3)\n",
        "log(0,2*3)=log(0,2)+log(0,3)\n",
        "log(-0.5,2*3)=log(-0.5,2)+log(-0.5,3)\n",
        "log(0.5,(-2)*(-3))=log(0.5,-2)+log(0.5,-3)\n",
        "log(0.5,0*3)=log(0.5,0)+log(0.5,3)\n",
        "forall a,x,y R+:\n    log(a,x*y)=log(a,x)+log(a,y)\n",
        "forall a,x,y R+:\n    a<=1\n    =>:\n        log(a,x*y)=log(a,x)+log(a,y)\n",
        "forall a,x,y R+:\n    a<1\n    =>:\n        log(a,x*y)=log(a,x)*log(a,y)\n",
        "forall a,b,x,y R+:\n    a<1\n    b<1\n    =>:\n        log(a,x*y)=log(a,x)+log(b,y)\n",
        "forall a,x,y R+:\n    a<1\n    =>:\n        log(a,x/y)=log(a,y)-log(a,x)\n",
        "forall a,x R+:\n    a<1\n    =>:\n        log(a,1/x)=log(a,x)\n",
        "forall a,x R+,n Z:\n    a<1\n    =>:\n        log(a,x^n)=(n+1)*log(a,x)\n",
    ] {
        check(&mut runtime(OutputLanguage::English), code, false);
    }
}

#[test]
fn real_argument_power_uses_the_expanded_power_wd_domain() {
    // Formerly rejected in Pow WD; the unchanged real power law is now legal.
    check(
        &mut runtime(OutputLanguage::English),
        "forall a,x,y R+:\n    a<1\n    =>:\n        log(a,x^y)=y*log(a,x)\n",
        true,
    );
    for guard in ["a<1", "1<a", "a!=1"] {
        let code =
            format!("forall a,x R+,y R:\n    {guard}\n    =>:\n        log(a,x^y)=y*log(a,x)\n");
        check(&mut runtime(OutputLanguage::English), &code, true);
        let wrong = code.replace("y*log(a,x)", "(y+1)*log(a,x)");
        check(&mut runtime(OutputLanguage::English), &wrong, false);
    }
}

#[test]
fn inherited_ceiling_and_failed_publication_stay_bounded() {
    for kind in 0..4 {
        let code = input(kind, "a<1");
        // BuiltinRule leaves their WD premises at KnownSpecialProperty: a<1
        // cannot yet supply the derived a!=1 there. Strategy admits that
        // existing proof for product/quotient/reciprocal. The symbolic power
        // argument needs the normal root route for its own carrier proof.
        for (level, passed) in [
            (VerifyStateLevel::Direct, false),
            (VerifyStateLevel::KnownSpecialProperty, false),
            (VerifyStateLevel::BuiltinRule, false),
            (VerifyStateLevel::Strategy, kind != 3),
        ] {
            let mut rt = runtime(OutputLanguage::English);
            let tokens = Tokenizer::new()
                .tokenize(&code, rt.current_file.clone())
                .unwrap();
            let mut stmts = rt.parse(&tokens).unwrap();
            let crate::ast::stmt::Stmt::Fact(fact) = stmts.remove(0) else {
                panic!("fact")
            };
            if level == VerifyStateLevel::BuiltinRule {
                assert!(rt
                    .verify_fact_well_definedness(&fact, VerifyState::new(level))
                    .unwrap()
                    .is_failed());
            }
            let result = rt.verify_fact(&fact, VerifyState::new(level)).unwrap();
            assert_eq!(!result.is_failed(), passed, "{code}");
        }
        let mut rt = runtime(OutputLanguage::English);
        let tokens = Tokenizer::new()
            .tokenize(&code, rt.current_file.clone())
            .unwrap();
        let crate::ast::stmt::Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
            panic!("fact")
        };
        assert!(
            !rt.verify_fact(&fact, VerifyState::top_level())
                .unwrap()
                .is_failed(),
            "{code}"
        );
    }
    let wrong = "forall a,x,y R+:\n    a<1\n    =>:\n        log(a,x*y)=log(a,x)*log(a,y)\n";
    let mut rt = runtime(OutputLanguage::English);
    check(&mut rt, wrong, false);
    let good = input(0, "a<1");
    let original = check(&mut rt, &good, true);
    let reuse = check(&mut rt, &good, true);
    // Repeating the complete forall cites the stored proposition, rather
    // than instantiating it to a new atomic goal.
    assert!(contains_string(&reuse, "by_known_forall_fact"));
    let statement = &original
        .as_object()
        .unwrap()
        .get("statement_results")
        .unwrap()
        .as_array()
        .unwrap()[0];
    let stored = statement
        .as_object()
        .unwrap()
        .get("store_and_infer")
        .unwrap()
        .as_object()
        .unwrap()
        .get("stores")
        .unwrap()
        .as_array()
        .unwrap();
    let source_id = stored[0]
        .as_object()
        .unwrap()
        .get("fact_id")
        .unwrap()
        .as_str()
        .unwrap();
    assert!(contains_string(&reuse, source_id));
    check(&mut rt, wrong, false);
}

#[test]
fn four_persistent_tracers_verify_without_trust() {
    for source in [
        include_str!(
            "../../../../examples/proof_nodes/equal/by_builtin_rule/log_product_valid_base.lit"
        ),
        include_str!(
            "../../../../examples/proof_nodes/equal/by_builtin_rule/log_quotient_valid_base.lit"
        ),
        include_str!(
            "../../../../examples/proof_nodes/equal/by_builtin_rule/log_reciprocal_valid_base.lit"
        ),
        include_str!(
            "../../../../examples/proof_nodes/equal/by_builtin_rule/log_arg_power_valid_base.lit"
        ),
    ] {
        assert!(!source.contains("trust"));
        check(&mut runtime(OutputLanguage::English), source, true);
    }
}
