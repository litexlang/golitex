//! Unit tests for Normal JSON projection.

use super::{project_stmt_normal, OutputDetail};
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
fn output_detail_normal_is_default_label() {
    assert_eq!(OutputDetail::Normal.as_str(), "normal");
}

#[test]
fn normal_json_have_natural_then_nonnegative_by_builtin() {
    let mut runtime = runtime_with_file_env();
    let have = exec_one(&mut runtime, "have k N");
    let have_json = project_stmt_normal(&have, &runtime);
    assert_eq!(object_field(&have_json, "success"), &JsonValue::Bool(true));
    let stores = object_field(&have_json, "stores")
        .as_array()
        .expect("stores array");
    assert!(
        stores.iter().any(|s| s.as_str().unwrap_or("").contains("$in N")),
        "have k N should store membership: {have_json:?}"
    );

    let goal = exec_one(&mut runtime, "k >= 0");
    let goal_json = project_stmt_normal(&goal, &runtime);
    assert_eq!(object_field(&goal_json, "success"), &JsonValue::Bool(true));
    let why = object_field(&goal_json, "why_verified")
        .as_object()
        .expect("why_verified");
    assert_eq!(
        why.get("type").and_then(|v| v.as_str().ok()),
        Some("builtin_rule")
    );
    assert_eq!(
        why.get("rule_name").and_then(|v| v.as_str().ok()),
        Some("From known in N")
    );
    assert_eq!(
        why.get("message").and_then(|v| v.as_str().ok()),
        Some("The goal follows from a known natural-number membership")
    );
    assert!(why.get("rule").is_none(), "Normal JSON must not print rule_id");
    let cite = why.get("cite").and_then(|v| v.as_str().ok()).unwrap_or("");
    assert_eq!(cite, "k $in N");
    assert!(
        !cite.contains('#'),
        "readable cite must not keep #id# wrappers: {cite:?}"
    );
}

#[test]
fn normal_json_calculation_one_plus_two_english() {
    let mut runtime = runtime_with_file_env();
    let goal = exec_one(&mut runtime, "1 + 2 = 3");
    let goal_json = project_stmt_normal(&goal, &runtime);
    assert_eq!(object_field(&goal_json, "success"), &JsonValue::Bool(true));
    let why = object_field(&goal_json, "why_verified")
        .as_object()
        .expect("why_verified");
    assert_eq!(
        why.get("type").and_then(|v| v.as_str().ok()),
        Some("builtin_rule")
    );
    assert_eq!(
        why.get("rule_name").and_then(|v| v.as_str().ok()),
        Some("Calculation")
    );
    assert_eq!(
        why.get("message").and_then(|v| v.as_str().ok()),
        Some("Both sides evaluate to the same number")
    );
    assert!(why.get("rule").is_none());
    assert!(why.get("variant").is_none());
}

#[test]
fn normal_json_calculation_one_plus_two_chinese() {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::Chinese,
    });
    let goal = exec_one(&mut runtime, "1 + 2 = 3");
    let goal_json = project_stmt_normal(&goal, &runtime);
    // Option 2: Chinese session localizes JSON keys as well as rule text.
    assert_eq!(object_field(&goal_json, "成功"), &JsonValue::Bool(true));
    let why = object_field(&goal_json, "证明方法")
        .as_object()
        .expect("证明方法");
    assert_eq!(
        why.get("类型").and_then(|v| v.as_str().ok()),
        Some("builtin_rule")
    );
    assert_eq!(
        why.get("规则名").and_then(|v| v.as_str().ok()),
        Some("计算")
    );
    assert_eq!(
        why.get("说明").and_then(|v| v.as_str().ok()),
        Some("两边都算出同一个数")
    );
}

#[test]
fn normal_json_list_set_have_infers_or() {
    let mut runtime = runtime_with_file_env();
    let have = exec_one(&mut runtime, "have a {1, 2}");
    let json = project_stmt_normal(&have, &runtime);
    assert_eq!(object_field(&json, "success"), &JsonValue::Bool(true));
    let infers = object_field(&json, "infers")
        .as_array()
        .expect("infers array");
    assert!(
        infers.iter().any(|s| {
            let t = s.as_str().unwrap_or("");
            t.contains("or") && t.contains("=")
        }),
        "have a {{1,2}} should infer or-equalities: {json:?}"
    );
}

#[test]
fn normal_json_let_obj_define_why() {
    let mut runtime = runtime_with_file_env();
    let stmt = exec_one(&mut runtime, "let a = 1");
    let json = project_stmt_normal(&stmt, &runtime);
    assert_eq!(object_field(&json, "success"), &JsonValue::Bool(true));
    let why = object_field(&json, "why_verified")
        .as_object()
        .expect("why_verified");
    assert_eq!(
        why.get("type").and_then(|v| v.as_str().ok()),
        Some("define_obj")
    );
    assert_eq!(
        why.get("rule_name").and_then(|v| v.as_str().ok()),
        Some("Let binding")
    );
}

#[test]
fn normal_json_search_proof_failure() {
    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have a R").is_failed());
    let failed = exec_one(&mut runtime, "a > 10");
    let json = project_stmt_normal(&failed, &runtime);
    assert_eq!(object_field(&json, "success"), &JsonValue::Bool(false));
    let why = object_field(&json, "why_failed")
        .as_object()
        .expect("why_failed");
    assert_eq!(
        why.get("phase").and_then(|v| v.as_str().ok()),
        Some("search_proof")
    );
    let stores = object_field(&json, "stores")
        .as_array()
        .expect("stores");
    assert!(stores.is_empty());
}
