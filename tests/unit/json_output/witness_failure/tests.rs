use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn atomic_body_failure_retains_exact_goal_and_does_not_publish_prop() {
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("prop has_copy(a R):\n    exist x R st {x = a}\n")
            .unwrap()
            .success
    );
    let sizes = |rt: &Runtime| {
        rt.execution_environments_stack
            .iter()
            .map(|e| {
                (
                    e.facts.facts_by_id.len(),
                    e.well_defined_objects.object_to_wd_id.len(),
                )
            })
            .collect::<Vec<_>>()
    };
    let before = sizes(&rt);
    let run = rt.run_litex_code("witness $has_copy(2) from 3").unwrap();
    assert!(!run.success && run.session_error.is_none());
    let json =
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    for needle in ["witness_atomic_fact", "exist_check", "body_check", "3 = 2"] {
        assert!(json.contains(needle), "{json}");
    }
    assert_eq!(before, sizes(&rt));
    // The proposition is independently true and full definition search can
    // prove it again. Only Direct lookup establishes whether this failed
    // witness published it.
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("$has_copy(2)", rt.current_file.clone())
        .unwrap();
    let crate::ast::stmt::Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    assert!(rt
        .verify_fact(
            &goal,
            crate::execute::execute_fact_stmt::VerifyState::new(
                crate::execute::execute_fact_stmt::VerifyStateLevel::Direct
            )
        )
        .unwrap()
        .is_failed());
}

#[test]
fn witness_type_failure_is_visible_before_local_binder_equality() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code("witness exist x {1} st {x = 1} from 0")
        .unwrap();
    assert!(!run.success && run.session_error.is_none());
    let json =
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    for needle in ["witness_exist_fact", "witness_type", "0 $in {1}"] {
        assert!(json.contains(needle), "{json}");
    }
}

fn runtime_language(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}

fn field<'a>(
    json: &'a crate::knowledge_base::JsonValue,
    name: &str,
    language: OutputLanguage,
) -> &'a crate::knowledge_base::JsonValue {
    let key = crate::json_output::json_keys::localize_key(name, language);
    json.as_object().unwrap().get(&key).unwrap_or_else(|| {
        panic!("missing {name}: {}", json.stringify())
    })
}

fn array(json: &crate::knowledge_base::JsonValue) -> &[crate::knowledge_base::JsonValue] {
    let crate::knowledge_base::JsonValue::Array(items) = json else {
        panic!("expected array: {}", json.stringify());
    };
    items
}

#[test]
fn atomic_success_preserves_checked_arguments_local_proof_and_obligations() {
    use crate::execute::execute_witness_stmt::{
        ExecWitnessAtomicFactStmtResult, ExecWitnessStmtResult,
    };
    use crate::execute::ExecStmtResult;
    use crate::knowledge_base::JsonValue;
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        let mut rt = runtime_language(language);
        let run = rt.run_litex_code(
            "prop has_copy(a R):\n    exist x R st {x=a}\nwitness $has_copy(2) from 2:\n    have local_copy R=2\n    local_copy=2\n$has_copy(2)\n",
        ).unwrap();
        assert!(run.success && run.session_error.is_none());
        let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessAtomicFact(
            ExecWitnessAtomicFactStmtResult::Success(s),
        )) = &run.statement_results[1] else { panic!("atomic success"); };
        let json = crate::json_output::project_stmt_detailed(&run.statement_results[1], &rt);
        assert_eq!(array(field(&json, "prop_argument_type_checks", language)).len(), 1);
        assert_eq!(field(&json, "projected_exist", language).as_str().unwrap(),
            "exist x R st {x = 2}");
        assert!(field(&json, "exist_fact_well_defined", language).as_object().is_ok());
        assert_eq!(array(field(&json, "witness_obj_well_defined", language)).len(), 1);
        assert_eq!(array(field(&json, "witness_type_checks", language)).len(), 1);
        assert_eq!(array(field(&json, "proof_steps", language)).len(), 2);
        let bodies = array(field(&json, "body_checks", language));
        assert_eq!(bodies.len(), s.obligations.body_checks.len());
        assert_eq!(bodies[0], crate::json_output::project_detailed::project_verify_fact(
            &s.obligations.body_checks[0], &rt,
        ));
        assert_eq!(field(&json, "uniqueness_check", language), &JsonValue::Null);
        assert!(field(&json, "store_and_infer", language).as_object().is_ok());
        assert!(!json.stringify().contains("local_env"));
        assert!(!json.stringify().contains("局部环境"));
    }
}

#[test]
fn dependent_atomic_witness_preserves_each_instantiated_type_check() {
    use crate::execute::execute_witness_stmt::{
        ExecWitnessAtomicFactStmtResult, ExecWitnessStmtResult,
    };
    use crate::execute::ExecStmtResult;
    let language = OutputLanguage::English;
    let mut rt = runtime_language(language);
    let run = rt.run_litex_code(
        "prop copies(a R):\n    exist x R,y {x} st {y=a}\nwitness $copies(2) from 2,2\n$copies(2)\n",
    ).unwrap();
    assert!(run.success && run.session_error.is_none());
    let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessAtomicFact(
        ExecWitnessAtomicFactStmtResult::Success(s),
    )) = &run.statement_results[1] else { panic!("atomic success"); };
    let json = crate::json_output::project_stmt_detailed(&run.statement_results[1], &rt);
    let checks = array(field(&json, "witness_type_checks", language));
    assert_eq!(checks.len(), 2);
    for (actual, checked) in checks.iter().zip(&s.ambient.witness_type_checks) {
        assert_eq!(actual, &crate::json_output::project_detailed::project_verify_fact(checked, &rt));
    }
    assert!(checks[1].stringify().contains("2 $in {2}"));
}

#[test]
fn nonempty_failure_preserves_each_actual_stage_in_both_languages() {
    use crate::execute::execute_witness_stmt::{
        ExecWitnessNonemptySetStmtFailed as F, ExecWitnessNonemptySetStmtResult,
        ExecWitnessStmtResult,
    };
    use crate::execute::ExecStmtResult;
    let cases = [
        ("witness $is_nonempty_set({1}) from 1/0\n", "obj_well_defined"),
        ("witness $is_nonempty_set({1/0}) from 1\n", "set_well_defined"),
        ("witness $is_nonempty_set({1}) from 1:\n    1=1\n    0=1\n", "proof_body"),
        ("witness $is_nonempty_set({1}) from 2\n", "membership"),
    ];
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        for (code, expected_phase) in cases {
            let mut rt = runtime_language(language);
            let run = rt.run_litex_code(code).unwrap();
            assert!(!run.success && run.session_error.is_none());
            let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessNonemptySet(
                ExecWitnessNonemptySetStmtResult::Failed(f),
            )) = &run.statement_results[0] else { panic!("nonempty failure"); };
            let json = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
            let failure = field(&json, "failure", language);
            assert_eq!(field(failure, "phase", language).as_str().unwrap(), expected_phase);
            let expected = match f {
                F::ObjWd(r) | F::SetWd(r) => {
                    crate::json_output::project_detailed::project_verify_obj_wd(r, &rt)
                }
                F::Membership(r) => crate::json_output::project_detailed::project_verify_fact(r, &rt),
                F::ProofBody(r) => crate::json_output::project_stmt_detailed(&r.result, &rt),
            };
            assert_eq!(field(failure, "result", language), &expected);
        }
    }
}

#[test]
fn nonempty_local_proof_failure_retains_exact_step_and_goal() {
    use crate::knowledge_base::JsonValue;
    let language = OutputLanguage::English;
    let mut rt = runtime_language(language);
    let run = rt.run_litex_code(
        "witness $is_nonempty_set({1}) from 1:\n    1=1\n    0=1\n",
    ).unwrap();
    assert!(!run.success && run.session_error.is_none());
    let json = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
    let failure = field(&json, "failure", language);
    assert_eq!(field(failure, "step_index", language), &JsonValue::Number(1.0));
    let child = field(failure, "result", language);
    assert_eq!(field(child, "statement", language).as_str().unwrap(), "0 = 1");
    assert_eq!(field(child, "success", language), &JsonValue::Bool(false));
}

#[test]
fn failed_nonempty_witness_never_publishes_and_valid_reuse_survives() {
    use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
    let mut rt = runtime();
    let direct = VerifyState::new(VerifyStateLevel::Direct);
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("$is_nonempty_set({1})", rt.current_file.clone()).unwrap();
    let crate::ast::stmt::Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact");
    };
    let failed = rt.run_litex_code("witness $is_nonempty_set({1}) from 2\n").unwrap();
    assert!(!failed.success && failed.session_error.is_none());
    let before_json = crate::json_output::project_stmt_detailed(&failed.statement_results[0], &rt);
    assert!(before_json.stringify().contains("2 $in {1}"));
    assert!(rt.verify_fact(&goal, direct.clone()).unwrap().is_failed());
    let valid = rt.run_litex_code("witness $is_nonempty_set({1}) from 1\n").unwrap();
    assert!(valid.success && valid.session_error.is_none());
    assert!(!rt.verify_fact(&goal, direct.clone()).unwrap().is_failed());
    let repeated = rt.run_litex_code("witness $is_nonempty_set({1}) from 2\n").unwrap();
    assert!(!repeated.success && repeated.session_error.is_none());
    assert!(!rt.verify_fact(&goal, direct).unwrap().is_failed());
}
