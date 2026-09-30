//! Detailed projection: IR fields except `local_env`.

use super::project_detailed::{project_run_detailed, project_stmt_detailed};
use super::OutputDetail;
use crate::execute::ExecStmtResult;
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::run::run_command_outcome::RunLitexCodeResult;
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime_en() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    })
}

fn runtime_zh() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::Chinese,
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

fn obj_field<'a>(value: &'a JsonValue, key: &str) -> &'a JsonValue {
    value
        .as_object()
        .expect("object")
        .get(key)
        .unwrap_or_else(|| panic!("missing field `{key}`"))
}

fn json_has_no_local_env(value: &JsonValue) -> bool {
    match value {
        JsonValue::Object(map) => {
            if map.get("local_env").is_some() || map.get("局部环境").is_some() {
                return false;
            }
            map.keys_in_order()
                .into_iter()
                .all(|k| json_has_no_local_env(map.get(&k).unwrap()))
        }
        JsonValue::Array(items) => items.iter().all(json_has_no_local_env),
        _ => true,
    }
}

#[test]
fn output_detail_detailed_label() {
    assert_eq!(OutputDetail::Detailed.as_str(), "detailed");
}

#[test]
fn detailed_fact_success_has_verify_and_store_english() {
    let mut runtime = runtime_en();
    assert!(!exec_one(&mut runtime, "have k N").is_failed());
    let goal = exec_one(&mut runtime, "k >= 0");
    let json = project_stmt_detailed(&goal, &runtime);
    assert_eq!(obj_field(&json, "success"), &JsonValue::Bool(true));
    assert_eq!(obj_field(&json, "kind").as_str().ok(), Some("fact"));
    assert!(obj_field(&json, "verify").as_object().is_ok());
    assert!(obj_field(&json, "store_and_infer").as_object().is_ok());
    assert!(json.as_object().unwrap().get("proof_method").is_none());
    assert!(json_has_no_local_env(&json));
}

#[test]
fn detailed_fact_success_chinese_keys() {
    let mut runtime = runtime_zh();
    assert!(!exec_one(&mut runtime, "have k N").is_failed());
    let json = project_stmt_detailed(&exec_one(&mut runtime, "k >= 0"), &runtime);
    assert_eq!(obj_field(&json, "成功"), &JsonValue::Bool(true));
    assert!(obj_field(&json, "验证").as_object().is_ok());
    assert!(obj_field(&json, "存储与推理").as_object().is_ok());
    assert!(json_has_no_local_env(&json));
}

#[test]
fn detailed_run_envelope_detail_and_language() {
    let mut runtime = runtime_zh();
    let stmt = exec_one(&mut runtime, "1 = 1");
    let run = RunLitexCodeResult {
        success: true,
        statement_results: vec![stmt],
        failed_statement_results: None,
        session_error: None,
        normal_json: None,
    };
    let json = project_run_detailed(&run, &runtime, "eval", None);
    assert_eq!(obj_field(&json, "详细度").as_str().ok(), Some("detailed"));
    assert_eq!(obj_field(&json, "语言").as_str().ok(), Some("zh"));
    let stmts = obj_field(&json, "语句结果").as_array().unwrap();
    assert_eq!(stmts.len(), 1);
    assert!(json_has_no_local_env(&json));
}

#[test]
fn detailed_let_has_kind_no_local_env() {
    let mut runtime = runtime_en();
    let json = project_stmt_detailed(&exec_one(&mut runtime, "let a = 1"), &runtime);
    assert_eq!(obj_field(&json, "success"), &JsonValue::Bool(true));
    assert_eq!(obj_field(&json, "kind").as_str().ok(), Some("let_obj"));
    assert!(json_has_no_local_env(&json));
}
