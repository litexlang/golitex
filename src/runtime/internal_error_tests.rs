//! Internal-conflict diagnostics, distinct from ordinary proof failure.

use super::{Runtime, RuntimeError};
use crate::json_output::{project_run_compact, project_run_detailed, project_run_normal};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::run::{RunLitexCodeResult, RunSessionError};

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn internal_error_merge_collision_returns_explicit_litex_bug() {
    // Deliberately collide two independently valid envs. This is an internal
    // invariant fixture, not evidence that normal Litex source can cause it.
    let mut first = runtime();
    let mut second = runtime();
    assert!(first.run_litex_code("let x = 1").unwrap().success);
    assert!(second.run_litex_code("let x = 2").unwrap().success);
    let error = first
        .top_exec_env_mut()
        .merge_from(second.top_exec_env())
        .unwrap_err();
    assert!(matches!(error, RuntimeError::InternalBug(_)));
    assert!(error
        .to_string()
        .starts_with("internal_bug: Litex internal bug: "));
    assert!(error
        .to_string()
        .contains("identifier `x` already defined in parent"));

    let run = RunLitexCodeResult::new(vec![], Some(RunSessionError::Runtime(error.clone())));
    assert!(run.process_failed());
    for json in [
        project_run_normal(&run, &first, "eval", None),
        project_run_compact(&run, &first, "eval", None),
        project_run_detailed(&run, &first, "eval", None),
    ] {
        let fields = json.as_object().unwrap();
        assert_eq!(
            fields.get("success").unwrap(),
            &crate::knowledge_base::JsonValue::Bool(false)
        );
        assert_eq!(
            fields.get("session_error").unwrap().as_str().unwrap(),
            error.to_string()
        );
    }
    let extracted = crate::run::run_extract::extract_launch_error_json(&error);
    assert!(extracted.contains("internal_bug: Litex internal bug:"));
    assert!(extracted.contains("identifier `x` already defined in parent"));
}

#[test]
fn internal_error_ordinary_user_failures_keep_their_existing_classification() {
    let launch = RuntimeError::InvalidArguments("unknown option".into());
    assert_eq!(launch.to_string(), "launch_error: unknown option");
    assert_eq!(
        RunSessionError::Runtime(launch.clone()).to_string(),
        format!("{:?}", RunSessionError::Runtime(launch))
    );
    assert_eq!(RunSessionError::FailToImport.to_string(), "FailToImport");
    let mut rt = runtime();
    let proof = rt.run_litex_code("0 = 1").unwrap();
    assert!(!proof.success);
    assert!(proof.session_error.is_none());
    let parse = rt.run_litex_code("let broken =").unwrap();
    assert!(!parse.success);
    assert!(!parse
        .session_error
        .unwrap()
        .to_string()
        .contains("Litex internal bug"));
}
