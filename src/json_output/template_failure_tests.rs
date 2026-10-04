//! Real transactional template failures must retain their nested obligation.

use super::{project_stmt_detailed, project_stmt_normal};
use crate::execute::ExecStmtResult;
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}

fn exec_one(runtime: &mut Runtime, code: &str) -> ExecStmtResult {
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .unwrap();
    let statements = runtime.parse(&tokens).unwrap();
    assert_eq!(statements.len(), 1, "{code}");
    runtime.exec_stmt(&statements[0]).unwrap()
}

fn assert_failure_outputs(runtime: &Runtime, result: &ExecStmtResult, phases: &[&str], goal: &str) {
    assert!(result.is_failed());
    for output in [
        project_stmt_normal(result, runtime),
        project_stmt_detailed(result, runtime),
    ] {
        let text = output.stringify();
        for phase in phases {
            assert!(text.contains(phase), "missing {phase}: {text}");
        }
        assert!(text.contains(goal), "missing {goal}: {text}");
        assert!(!text.contains("local_env"), "{text}");
    }
}

#[test]
fn template_failure_stages_show_the_checked_child_goal() {
    for (code, phases, goal) in [
        (
            "template<f fn(x R: $is_set(1 / 0)) R>:\n    have item R = 0\n",
            vec!["parameter_type"],
            "0 != 0",
        ),
        (
            "template<a R: $is_set(1 / 0)>:\n    have item R = 0\n",
            vec!["domain_fact_well_defined"],
            "0 != 0",
        ),
        (
            "template<S set>:\n    have item S\n",
            vec!["body_have_in_nonempty", "nonempty_check"],
            "S",
        ),
        (
            "template<a R>:\n    have item Z = a\n",
            vec!["body_have_equal", "membership"],
            "a $in Z",
        ),
        (
            "template<a R>:\n    have fn item(x R) R = 1 / x\n",
            vec!["body_have_fn_equal", "anonymous_fn_well_defined"],
            "x != 0",
        ),
    ] {
        let rt = &mut runtime(OutputLanguage::English);
        let result = exec_one(rt, code);
        assert_failure_outputs(rt, &result, &phases, goal);
    }
}

#[test]
fn invalid_closure_tuple_template_preserves_struct_membership_goal() {
    let rt = &mut runtime(OutputLanguage::English);
    assert!(!exec_one(rt, "struct Box:\n    op fn(x R) R\n    tag N\n").is_failed());
    assert!(!exec_one(rt, "forall f fn(x R) R:\n    (f, 0) $in &Box\n").is_failed());
    let result = exec_one(
        rt,
        "template<a R>:\n    have box &Box = (fn(x R) R {x + a}, -1)\n",
    );
    assert_failure_outputs(
        rt,
        &result,
        &["body_have_equal", "membership", "search_proof"],
        "$in &Box",
    );
}

#[test]
fn template_existential_wd_failure_keeps_the_inner_reason() {
    let rt = &mut runtime(OutputLanguage::English);
    let result = exec_one(
        rt,
        "template<S set>:\n    have item R:\n        1 / 0 = item\n",
    );
    assert_failure_outputs(
        rt,
        &result,
        &["body_have_by_exist", "well_defined", "failed_body"],
        "0 != 0",
    );
}

#[test]
fn failed_template_is_unpublished_and_later_definition_succeeds() {
    let rt = &mut runtime(OutputLanguage::English);
    let bad = exec_one(rt, "template<a R>:\n    have selected Z = a\n");
    assert_failure_outputs(rt, &bad, &["membership"], "a $in Z");
    let normal = project_stmt_normal(&bad, rt);
    assert!(normal
        .as_object()
        .unwrap()
        .get("stores")
        .unwrap()
        .as_array()
        .unwrap()
        .is_empty());
    assert!(exec_one(rt, "\\selected<2> = 2").is_failed());
    // Parsing reserves declaration names even when execution fails.
    let good = exec_one(rt, "template<a R>:\n    have recovered R = a\n");
    assert!(!good.is_failed());
    assert!(!exec_one(rt, "\\recovered<2> = 2").is_failed());
    for output in [
        project_stmt_normal(&good, rt),
        project_stmt_detailed(&good, rt),
    ] {
        assert_eq!(
            output.as_object().unwrap().get("success"),
            Some(&JsonValue::Bool(true))
        );
        assert!(output.as_object().unwrap().get("failure").is_none());
    }
}

#[test]
fn template_failure_children_use_the_selected_output_language() {
    let rt = &mut runtime(OutputLanguage::Chinese);
    let failed = exec_one(rt, "template<a R>:\n    have selected Z = a\n");
    let normal = project_stmt_normal(&failed, rt);
    let detail = project_stmt_detailed(&failed, rt);
    assert!(normal
        .as_object()
        .unwrap()
        .get("失败原因")
        .unwrap()
        .as_object()
        .unwrap()
        .get("失败详情")
        .is_some());
    assert!(detail.as_object().unwrap().get("失败详情").is_some());
    assert_failure_outputs(rt, &failed, &["body_have_equal", "membership"], "a $in Z");
}
