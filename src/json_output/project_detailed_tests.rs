//! Detailed projection is temporarily Normal-fallback while the IR projector
//! is realigned. Keep a smoke that the public entry still returns Success JSON.

use super::project_detailed::project_stmt_detailed;
use super::OutputDetail;
use crate::execute::ExecStmtResult;
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime_with_file_env() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    })
}

fn exec_one(runtime: &mut Runtime, code: &str) -> ExecStmtResult {
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    let stmts = runtime.parse(&tokens).expect("parse");
    assert_eq!(stmts.len(), 1, "expected exactly one stmt in:\n{code}");
    runtime
        .exec_stmt(&stmts[0])
        .expect("exec_stmt RuntimeResult")
}

fn object_field<'a>(value: &'a JsonValue, key: &str) -> &'a JsonValue {
    value
        .as_object()
        .expect("object")
        .get(key)
        .unwrap_or_else(|| panic!("missing field `{key}`"))
}

#[test]
fn output_detail_detailed_label() {
    assert_eq!(OutputDetail::Detailed.as_str(), "detailed");
}

#[test]
fn detailed_entry_falls_back_to_normal_success_shape() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have k N").is_failed());
    let goal = exec_one(&mut runtime, "k >= 0");
    let json = project_stmt_detailed(&goal, &runtime);
    assert_eq!(object_field(&json, "success"), &JsonValue::Bool(true));
    assert!(object_field(&json, "why_verified").as_object().is_ok());
    let stores = object_field(&json, "stores")
        .as_array()
        .expect("stores");
    assert!(!stores.is_empty(), "expected stored facts: {json:?}");
}
