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

#[test]
fn detailed_by_def_preserves_definition_route() {
    let mut rt = runtime_en();
    assert!(!exec_one(&mut rt, "prop above_zero(x R):\n    x > 0").is_failed());
    assert!(!exec_one(&mut rt, "$above_zero(1)").is_failed());
    let result = exec_one(&mut rt, "by def $above_zero(1)");
    let detailed = project_stmt_detailed(&result, &rt);
    assert_eq!(obj_field(&detailed, "success"), &JsonValue::Bool(true));
    let proof = obj_field(&detailed, "proof");
    let searched = obj_field(proof, "searched_proof");
    assert_eq!(obj_field(searched, "type").as_str().ok(), Some("by_definition"));
    assert_eq!(obj_field(searched, "requirement_facts").as_array().unwrap().len(), 2);
    assert_eq!(obj_field(searched, "proof_of_requirement_facts").as_array().unwrap().len(), 2);
    assert!(json_has_no_local_env(&detailed));

    let result = exec_one(&mut rt, "by def 1 $in {x R: x > 0}");
    let normal = super::project_stmt_normal(&result, &rt);
    assert_eq!(obj_field(&normal, "success"), &JsonValue::Bool(false));
    assert!(obj_field(&normal, "stores").as_array().unwrap().is_empty());
    assert!(obj_field(&normal, "infers").as_array().unwrap().is_empty());
}

#[test]
fn detailed_atomic_builtin_rewrite_preserves_citation_and_residual() {
    let code = "forall n N:\n    n=16\n    =>:\n        $prime(n+1)\n";
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: code.to_string(), session: false, strict: true, language,
        });
        let run = rt.run_litex_code(code).expect("run");
        assert!(run.success);
        let detailed = project_run_detailed(&run, &rt, "eval", None);
        let english = language == OutputLanguage::English;
        let statements = obj_field(&detailed, if english { "statement_results" } else { "语句结果" })
            .as_array().unwrap();
        let verify = obj_field(&statements[0], if english { "verify" } else { "验证" });
        let then = obj_field(verify, "proved_then_facts").as_array().unwrap();
        let verified = obj_field(&then[0], "verify_result");
        let rewrite = obj_field(verified, if english { "searched_proof" } else { "搜索证明" });
        assert_eq!(obj_field(rewrite, if english { "type" } else { "类型" }).as_str().ok(), Some("by_builtin_rewrite"));
        assert_eq!(obj_field(rewrite, if english { "rule" } else { "规则" }).as_str().ok(), Some("ClosedNumericEqualSubstitution"));
        assert!(obj_field(rewrite, "rewritten_fact").as_str().unwrap().contains("16 + 1"));
        let cites = obj_field(rewrite, "cited_equal_fact_ids").as_array().unwrap();
        assert_eq!(cites.len(), 1);
        let dom = obj_field(verify, "assumed_dom_facts").as_array().unwrap();
        let dom_store = obj_field(&dom[0], if english { "store_and_infer" } else { "存储与推理" });
        let stored = obj_field(dom_store, if english { "stores" } else { "存储" }).as_array().unwrap();
        let id_key = if english { "fact_id" } else { "命题编号" };
        assert_eq!(obj_field(&cites[0], id_key), obj_field(&stored[0], id_key));
        let residual = obj_field(rewrite, "proof_of_rewritten_fact");
        assert_eq!(obj_field(residual, if english { "success" } else { "成功" }), &JsonValue::Bool(true));
        let child = obj_field(residual, if english { "searched_proof" } else { "搜索证明" });
        assert_eq!(obj_field(child, if english { "rule" } else { "规则" }).as_str().ok(), Some("PrimeByComputation"));
        assert_eq!(obj_field(child, "resolved_value").as_str().ok(), Some("17"));
        assert!(json_has_no_local_env(&detailed));
    }
    let false_code = "forall n N:\n    n=8\n    =>:\n        $prime(n+1)\n";
    let mut rt = runtime_en();
    assert!(!rt.run_litex_code(false_code).expect("false run").success);
}

#[test]
fn detailed_register_preserves_checked_law_in_both_languages() {
    for (property, law) in [
        ("reflexive", "forall x set:\n        $same(x,x)"),
        ("symmetric", "forall x,y set:\n        $same(x,y)\n        =>:\n            $same(y,x)"),
        ("transitive", "forall x,y,z set:\n        $same(x,y)\n        $same(y,z)\n        =>:\n            $same(x,z)"),
    ] {
        let code = format!("prop same(x,y set):\n    x=y\nregister {property}:\n    ? {law}\n");
        for language in [OutputLanguage::English, OutputLanguage::Chinese] {
            let mut rt = Runtime::new(LaunchCommand::Eval {
                code: code.clone(), session: false, strict: true, language,
            });
            let run = rt.run_litex_code(&code).expect("run");
            assert!(run.success, "{code}");
            let json = project_stmt_detailed(run.statement_results.last().unwrap(), &rt);
            assert_eq!(obj_field(&json, "property").as_str().ok(), Some(property));
            assert_eq!(obj_field(&json, "prop").as_str().ok(), Some("same"));
            let proof = obj_field(&json, "forall_proof");
            let success = if language == OutputLanguage::English { "success" } else { "成功" };
            assert_eq!(obj_field(proof, success), &JsonValue::Bool(true));
            assert!(!obj_field(proof, "proved_then_facts").as_array().unwrap().is_empty());
            assert!(json_has_no_local_env(&json));
        }
    }
}

#[test]
fn detailed_register_preserves_actual_failure_stage_in_both_languages() {
    for (property, law) in [
        ("reflexive", "forall x set:\n        $bad(x,x)"),
        ("symmetric", "forall x,y set:\n        $bad(x,y)\n        =>:\n            $bad(y,x)"),
        ("transitive", "forall x,y,z set:\n        $bad(x,y)\n        $bad(y,z)\n        =>:\n            $bad(x,z)"),
    ] {
        let false_setup = if property == "symmetric" {
            "prop bad(x,y set):\n    x={}\n    y={1}\n"
        } else {
            "prop bad(x,y set):\n    x!=y\n"
        };
        for (setup, goal, phase) in [
            ("prop bad(x,y set):\n    x=y\n", "forall x set:\n        x=x", "shape"),
            ("", law, "prop_not_defined"),
            ("prop bad(x set):\n    x=x\n", law, "wrong_arity"),
            (false_setup, law, "forall"),
        ] {
            let code = format!("{setup}register {property}:\n    ? {goal}\n");
            for language in [OutputLanguage::English, OutputLanguage::Chinese] {
                let mut rt = Runtime::new(LaunchCommand::Eval {
                    code: code.clone(), session: false, strict: true, language,
                });
                let run = rt.run_litex_code(&code).expect("run");
                assert!(!run.success, "{code}");
                if phase == "shape" {
                    assert!(run.session_error.is_some());
                    assert!(!matches!(run.statement_results.last(), Some(ExecStmtResult::Register(_))));
                    continue;
                }
                assert!(run.session_error.is_none(), "{code}");
                let json = project_stmt_detailed(run.statement_results.last().unwrap(), &rt);
                assert_eq!(obj_field(&json, "property").as_str().ok(), Some(property));
                let english = language == OutputLanguage::English;
                let failure = obj_field(&json, if english { "failure" } else { "失败详情" });
                assert_eq!(obj_field(failure, if english { "phase" } else { "阶段" }).as_str().ok(), Some(phase));
                if phase == "forall" {
                    let proof = obj_field(failure, "forall_proof");
                    assert_eq!(obj_field(proof, if english { "success" } else { "成功" }), &JsonValue::Bool(false));
                }
                assert!(json_has_no_local_env(&json));
            }
        }
    }
}
