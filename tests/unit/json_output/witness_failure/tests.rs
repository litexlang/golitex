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
