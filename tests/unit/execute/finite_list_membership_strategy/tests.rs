use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::knowledge_base::{JsonObject, JsonValue};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn fact(rt: &mut Runtime, text: &str) -> Fact {
    let tokens = Tokenizer::new()
        .tokenize(text, rt.current_file.clone())
        .unwrap();
    let mut statements = rt.parse(&tokens).unwrap();
    assert_eq!(statements.len(), 1);
    let Stmt::Fact(fact) = statements.remove(0) else {
        panic!("{text}")
    };
    fact
}

#[test]
fn maintained_membership_and_nonmembership_tracers_pass() {
    for code in [
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_strategy/list_set_membership.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_strategy/list_set_nonmembership.lit"
        )),
    ] {
        let run = runtime().run_litex_code(code).unwrap();
        assert!(run.session_error.is_none(), "{:?}", run.session_error);
        assert!(run.success, "{code}");
    }
}

#[test]
fn false_members_and_nonmembers_and_ill_defined_objects_reject() {
    for code in [
        "{1, 2} $in {{}, {1, 3}}",
        "not 2 $in {1, 2, 3}",
        "4 $in {}",
        "1/0 $in {1/0}",
        "not 1/0 $in {}",
        "not 4 $in {1/0}",
    ] {
        let run = runtime().run_litex_code(code).unwrap();
        assert!(
            run.session_error.is_none(),
            "{code}: {:?}",
            run.session_error
        );
        assert!(!run.success, "false or ill-defined admission: {code}");
    }
}

#[test]
fn list_builtin_can_use_direct_numeric_leaves_without_enabling_strategy() {
    // Each query is fresh: no earlier positive stores the target or its WD.
    for code in ["{1, 2} $in {{}, {1, 2}}", "not 4 $in {1, 2, 3}"] {
        for (level, expected) in [
            (VerifyStateLevel::Direct, false),
            (VerifyStateLevel::KnownSpecialProperty, false),
            (VerifyStateLevel::BuiltinRule, true),
            (VerifyStateLevel::Strategy, true),
        ] {
            let mut rt = runtime();
            let goal = fact(&mut rt, code);
            assert_eq!(
                !rt.verify_fact(&goal, VerifyState::new(level))
                    .unwrap()
                    .is_failed(),
                expected,
                "{code} at {level:?}"
            );
        }
    }
}

#[test]
fn accepted_targets_can_be_cited_at_known_fact_level() {
    for code in ["{1, 2} $in {{}, {1, 2}}", "not 4 $in {1, 2, 3}"] {
        let mut rt = runtime();
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.success);
        let goal = fact(&mut rt, code);
        assert!(!rt
            .verify_fact(&goal, VerifyState::new(VerifyStateLevel::Direct))
            .unwrap()
            .is_failed());
        let repeat = rt.run_litex_code(code).unwrap();
        assert!(repeat.success);
        let detail = crate::json_output::project_stmt_detailed(&repeat.statement_results[0], &rt)
            .stringify();
        assert!(detail.contains("cite_fact_id"), "{detail}");
    }
}

#[test]
fn descent_does_not_reenable_a_function_definition_child() {
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("have fn bump(n Z) Z = n + 1")
            .unwrap()
            .success
    );
    let target = fact(&mut rt, "bump(3) $in {4}");
    // A root attempt may independently unfold/rewrite the application. This
    // query intentionally permits Strategy, without those later root stages.
    let state = VerifyState::new(VerifyStateLevel::Strategy);
    assert!(rt.verify_fact(&target, state).unwrap().is_failed());
    assert!(rt.run_litex_code("bump(3) = 4").unwrap().success);
    assert!(!rt.verify_fact(&target, state).unwrap().is_failed());
}

fn rule<'a>(value: &'a JsonValue, name: &str) -> Option<&'a JsonObject> {
    match value {
        JsonValue::Object(object) => {
            if matches!(object.get("rule"), Some(JsonValue::String(s)) if s == name) {
                return Some(object);
            }
            object.iter().find_map(|(_, child)| rule(child, name))
        }
        JsonValue::Array(children) => children.iter().find_map(|child| rule(child, name)),
        _ => None,
    }
}

#[test]
fn detailed_output_keeps_one_equality_or_all_disequality_certificates() {
    for (code, name, requirements) in [
        (
            "{1, 2} $in {{}, {1, 2}}",
            "ListSetElementMembership",
            vec!["{1, 2} = {1, 2}"],
        ),
        (
            "not 4 $in {1, 2, 3}",
            "ListSetExhaustiveDisequality",
            vec!["4 != 1", "4 != 2", "4 != 3"],
        ),
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.success, "{code}");
        let detail = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
        let proof = rule(&detail, name).unwrap_or_else(|| panic!("{}", detail.stringify()));
        let children: Vec<&JsonValue> = if let Some(equal) = proof.get("equality_proof") {
            vec![equal]
        } else {
            proof.get("disequality_proofs").unwrap().as_array().unwrap().iter().collect()
        };
        assert_eq!(children.len(), requirements.len());
        for (child, requirement) in children.iter().zip(&requirements) {
            assert_eq!(child.as_object().unwrap().get("fact").unwrap().as_str().unwrap(), *requirement);
        }
        for child in children {
            assert!(
                child.stringify().contains("\"success\""),
                "{}",
                child.stringify()
            );
        }
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::result::AtomicExceptEqualityFactSearchProofByBuiltinStrategy as S;
        let Fact::AtomicFact(atomic) = fact(&mut rt, code) else { panic!("atomic") };
        let strategy = rt.search_atomic_except_equality_fact_proof_by_builtin_strategy(
            &atomic, VerifyState::new(VerifyStateLevel::BuiltinRule),
        ).unwrap().unwrap();
        let (facts, proofs) = match strategy {
            S::ListSetMembership(p) => (p.requirement_facts, p.proof_of_requirement_facts),
            S::ListSetNonMembership(p) => (p.requirement_facts, p.proof_of_requirement_facts),
            _ => panic!("list strategy"),
        };
        assert_eq!(facts.iter().map(|f| f.readable_string()).collect::<Vec<_>>(), requirements);
        assert_eq!(proofs.len(), facts.len());
        assert!(proofs.iter().all(|p| !p.is_failed()));

    }
}
