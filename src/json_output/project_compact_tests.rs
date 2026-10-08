//! Unit tests for Compact JSON projection.

use super::{project_run_compact, project_stmt_compact, OutputDetail};
use crate::execute::ExecStmtResult;
use crate::json_output::project_stmt_normal;
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
    assert_eq!(stmts.len(), 1);
    runtime.exec_stmt(&stmts[0]).expect("exec")
}

fn obj_field<'a>(v: &'a JsonValue, key: &str) -> &'a JsonValue {
    v.as_object()
        .expect("object")
        .get(key)
        .unwrap_or_else(|| panic!("missing {key}"))
}

#[test]
fn output_detail_compact_label() {
    assert_eq!(OutputDetail::Compact.as_str(), "compact");
}

#[test]
fn compact_success_only_success_and_statement_english() {
    let mut rt = runtime_en();
    let json = project_stmt_compact(&exec_one(&mut rt, "1 + 1 = 2"), &rt);
    assert_eq!(
        json.as_object().unwrap().keys_in_order(),
        vec!["success", "statement"]
    );
    assert_eq!(obj_field(&json, "success"), &JsonValue::Bool(true));
    assert!(obj_field(&json, "statement")
        .as_str()
        .unwrap()
        .contains("="));
    assert!(json.as_object().unwrap().get("proof_method").is_none());
    assert!(json.as_object().unwrap().get("stores").is_none());
    assert!(json.as_object().unwrap().get("infers").is_none());
}

#[test]
fn compact_success_chinese_keys() {
    let mut rt = runtime_zh();
    let json = project_stmt_compact(&exec_one(&mut rt, "let a = 1"), &rt);
    assert_eq!(
        json.as_object().unwrap().keys_in_order(),
        vec!["成功", "语句"]
    );
    assert_eq!(obj_field(&json, "成功"), &JsonValue::Bool(true));
    assert_eq!(obj_field(&json, "语句").as_str().ok(), Some("let a = 1"));
}

#[test]
fn compact_failure_has_fail_reason_english() {
    let mut rt = runtime_en();
    let _ = exec_one(&mut rt, "have a R");
    let json = project_stmt_compact(&exec_one(&mut rt, "a > 10"), &rt);
    assert_eq!(
        json.as_object().unwrap().keys_in_order(),
        vec!["success", "statement", "fail_reason"]
    );
    assert_eq!(obj_field(&json, "success"), &JsonValue::Bool(false));
    let fail = obj_field(&json, "fail_reason").as_object().unwrap();
    assert_eq!(fail.keys_in_order(), vec!["phase", "goal"]);
    assert_eq!(
        fail.get("phase").and_then(|x| x.as_str().ok()),
        Some("search_proof")
    );
    assert_eq!(
        fail.get("goal").and_then(|x| x.as_str().ok()),
        Some("a > 10")
    );
    assert!(json.as_object().unwrap().get("why_failed").is_none());
    assert!(json.as_object().unwrap().get("stores").is_none());
}

#[test]
fn compact_failure_chinese_keys_and_phase() {
    let mut rt = runtime_zh();
    let _ = exec_one(&mut rt, "have a R");
    let json = project_stmt_compact(&exec_one(&mut rt, "a > 10"), &rt);
    assert_eq!(
        json.as_object().unwrap().keys_in_order(),
        vec!["成功", "语句", "失败原因"]
    );
    let fail = obj_field(&json, "失败原因").as_object().unwrap();
    assert_eq!(
        fail.get("阶段").and_then(|x| x.as_str().ok()),
        Some("搜索证明")
    );
    assert_eq!(
        fail.get("目标命题").and_then(|x| x.as_str().ok()),
        Some("a > 10")
    );
}

#[test]
fn compact_thinner_than_normal_success() {
    let mut rt = runtime_en();
    let stmt = exec_one(&mut rt, "1 + 2 = 3");
    let normal = project_stmt_normal(&stmt, &rt);
    let compact = project_stmt_compact(&stmt, &rt);
    assert!(normal.as_object().unwrap().len() > compact.as_object().unwrap().len());
    assert!(normal.as_object().unwrap().get("proof_method").is_some());
    assert!(compact.as_object().unwrap().get("proof_method").is_none());
}

#[test]
fn compact_run_envelope_detail() {
    let mut rt = runtime_zh();
    let stmt = exec_one(&mut rt, "1 = 1");
    let run = RunLitexCodeResult {
        success: true,
        statement_results: vec![stmt],
        statement_texts: Vec::new(),
        failed_statement_results: None,
        session_error: None,
        normal_json: None,
    };
    let json = project_run_compact(&run, &rt, "eval", None);
    assert_eq!(obj_field(&json, "详细度").as_str().ok(), Some("compact"));
    assert_eq!(obj_field(&json, "语言").as_str().ok(), Some("zh"));
    let stmts = obj_field(&json, "语句结果").as_array().unwrap();
    assert_eq!(stmts.len(), 1);
    assert_eq!(
        stmts[0].as_object().unwrap().keys_in_order(),
        vec!["成功", "语句"]
    );
}
