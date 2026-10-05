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
fn run_json_preserves_named_declarations_and_complete_theorem_calls() {
    for declaration in ["thm", "axiom"] {
        let mut runtime = runtime_with_file_env();
        let code = format!("{declaration} identity:\n    ? forall x R:\n        x = x\nby thm identity(2) => 2 = 2\nrelease thm identity(3)");
        let run = runtime.run_litex_code(&code).unwrap();
        assert!(run.success, "{code}: {:?}", run.session_error);
        let json = super::project_run_normal(&run, &runtime, "eval", None);
        let statements = object_field(&json, "statement_results").as_array().unwrap();
        assert!(object_field(&statements[0], "statement")
            .as_str()
            .unwrap()
            .starts_with(&format!("{declaration} identity:")));
        assert_eq!(
            object_field(&statements[1], "statement").as_str().unwrap(),
            "by thm identity(2) => 2 = 2"
        );
        assert_eq!(
            object_field(&statements[2], "statement").as_str().unwrap(),
            "release thm identity(3)"
        );
        assert_eq!(
            object_field(&statements[1], "stores"),
            &JsonValue::Array(vec![JsonValue::String("2 = 2".into())])
        );
        if declaration == "axiom" {
            assert_eq!(
                object_field(object_field(&statements[0], "proof_method"), "rule_name")
                    .as_str()
                    .unwrap(),
                "Axiom"
            );
        }
        for projected in [
            super::project_run_compact(&run, &runtime, "eval", None),
            super::project_run_detailed(&run, &runtime, "eval", None),
        ] {
            let projected_statements = object_field(&projected, "statement_results")
                .as_array().unwrap();
            for (normal, projected) in statements.iter().zip(projected_statements) {
                assert_eq!(object_field(normal, "statement"), object_field(projected, "statement"));
            }
        }
    }
}

#[test]
fn run_json_keeps_source_aligned_through_failures_and_locales() {
    for language in OutputLanguage::ALL {
        let mut runtime = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language,
        });
        let run = runtime.run_litex_code("1 / 0 = 0\n1 = 1\nhave").unwrap();
        assert!(!run.success);
        assert!(run.session_error.is_some());
        assert_eq!(run.statement_results.len(), 2);
        assert_eq!(run.statement_texts.len(), 2);
        assert_eq!(run.failed_statement_results, Some(vec![0]));
        let json = super::project_run_normal(&run, &runtime, "eval", None);
        let key = |name| super::json_keys::localize_key(name, language);
        let statements = object_field(&json, &key("statement_results"))
            .as_array()
            .unwrap();
        assert_eq!(
            object_field(&statements[0], &key("statement"))
                .as_str()
                .unwrap(),
            "1 / 0 = 0"
        );
        assert_eq!(
            object_field(&statements[1], &key("statement"))
                .as_str()
                .unwrap(),
            "1 = 1"
        );
        let why = object_field(&statements[0], &key("why_failed"));
        assert_eq!(
            object_field(why, &key("phase")).as_str().unwrap(),
            super::helper::phase_value_well_defined(language)
        );
        assert_eq!(
            object_field(why, &key("message")).as_str().unwrap(),
            super::explain::well_defined_not_proven_message(language)
        );
        assert!(object_field(&statements[0], &key("stores"))
            .as_array()
            .unwrap()
            .is_empty());
        assert!(!object_field(&json, &key("session_error"))
            .as_str()
            .unwrap()
            .contains("Runtime("));
        let without_source = project_stmt_normal(&run.statement_results[0], &runtime);
        assert_eq!(
            object_field(&without_source, &key("statement"))
                .as_str()
                .unwrap(),
            "<well_defined_not_proven>"
        );
        for projected in [
            super::project_run_compact(&run, &runtime, "eval", None),
            super::project_run_detailed(&run, &runtime, "eval", None),
        ] {
            let projected_statements = object_field(&projected, &key("statement_results"))
                .as_array().unwrap();
            for (normal, projected) in statements.iter().zip(projected_statements) {
                assert_eq!(object_field(normal, &key("statement")), object_field(projected, &key("statement")));
            }
        }
    }
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
    let why = object_field(&goal_json, "proof_method")
        .as_object()
        .expect("proof_method");
    assert_eq!(
        why.get("type").and_then(|v| v.as_str().ok()),
        Some("builtin_rule")
    );
    assert_eq!(
        why.get("rule_name").and_then(|v| v.as_str().ok()),
        Some("Known converse order")
    );
    assert_eq!(
        why.get("message").and_then(|v| v.as_str().ok()),
        Some("The opposite-direction comparison is already known")
    );
    assert!(why.get("rule").is_none(), "Normal JSON must not print rule_id");
    let cite = why.get("cite").and_then(|v| v.as_str().ok()).unwrap_or("");
    // `have k N` already inferred the checked opposite-direction comparison.
    assert_eq!(cite, "0 <= k");
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
    let why = object_field(&goal_json, "proof_method")
        .as_object()
        .expect("proof_method");
    assert_eq!(
        why.get("type").and_then(|v| v.as_str().ok()),
        Some("by_closed_calculation")
    );
    assert_eq!(
        why.get("rule_name").and_then(|v| v.as_str().ok()),
        Some("Closed calculation")
    );
    assert_eq!(
        why.get("message").and_then(|v| v.as_str().ok()),
        Some("Exact evaluation of closed expressions without proof search")
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
        Some("封闭计算")
    );
    assert_eq!(
        why.get("规则名").and_then(|v| v.as_str().ok()),
        Some("封闭计算")
    );
    assert_eq!(
        why.get("说明").and_then(|v| v.as_str().ok()),
        Some("精确计算封闭表达式，不递归搜索证明")
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
    let why = object_field(&json, "proof_method")
        .as_object()
        .expect("proof_method");
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
