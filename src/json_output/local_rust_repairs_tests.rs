use super::{project_stmt_detailed, project_stmt_normal};
use crate::execute::ExecStmtResult;
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn run(code: &str) -> (Runtime, ExecStmtResult) {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let mut result = rt.run_litex_code(code).unwrap();
    assert!(
        result.session_error.is_none(),
        "{code}: {:?}",
        result.session_error
    );
    (
        rt,
        result.statement_results.pop().expect("statement result"),
    )
}

fn field<'a>(value: &'a JsonValue, key: &str) -> &'a JsonValue {
    value
        .as_object()
        .unwrap()
        .get(key)
        .unwrap_or_else(|| panic!("missing {key}: {value:?}"))
}

fn failure(value: &JsonValue) -> &JsonValue {
    assert_eq!(field(value, "success"), &JsonValue::Bool(false));
    field(field(value, "why_failed"), "failure")
}

#[test]
fn let_and_named_fn_failures_show_existing_wd_obligations() {
    for (code, obligation) in [
        ("let bad = 1 / 0", "0 != 0"),
        ("have fn reciprocal(x R) R = 1 / x", "x != 0"),
    ] {
        let (rt, result) = run(code);
        assert!(result.is_failed());
        let normal = project_stmt_normal(&result, &rt);
        let text = failure(&normal).stringify();
        assert!(text.contains(obligation), "{text}");
        if code.starts_with("let") {
            let detail = project_stmt_detailed(&result, &rt);
            assert!(field(&detail, "value_well_defined")
                .stringify()
                .contains(obligation));
        }
    }
    for code in [
        "let good = 1 / 1",
        "have fn reciprocal(x R: x != 0) R = 1 / x",
    ] {
        let (_, result) = run(code);
        assert!(!result.is_failed(), "{code}");
    }
}

#[test]
fn sketch_failure_identifies_the_actual_nested_step() {
    let (rt, result) = run("sketch:\n    1 = 1\n    0 = 1\n");
    let normal = project_stmt_normal(&result, &rt);
    let failed = failure(&normal);
    assert_eq!(field(failed, "step_index"), &JsonValue::Number(1.0));
    let nested = field(failed, "result");
    assert_eq!(field(nested, "success"), &JsonValue::Bool(false));
    assert_eq!(field(nested, "statement").as_str().unwrap(), "0 = 1");
    let (_, result) = run("sketch:\n    1 = 1\n    0 = 0\n");
    assert!(!result.is_failed());
}

#[test]
fn detailed_compound_labels_retain_actual_goals_on_success_and_failure() {
    for code in [
        "0 = 0 and 1 = 1",
        "0 = 1 and 1 = 1",
        "0 <= 0 < 1",
        "0 = 0 and 1 = 1 or 0 = 1 and 1 = 2",
        "forall x R:\n    x = x\n",
    ] {
        let (rt, result) = run(code);
        let normal = project_stmt_normal(&result, &rt);
        let detailed = project_stmt_detailed(&result, &rt);
        assert_eq!(
            field(&detailed, "statement"),
            field(&normal, "statement"),
            "{code}"
        );
        assert!(!field(&detailed, "statement")
            .as_str()
            .unwrap()
            .contains('…'));
    }
}

#[test]
fn symbolic_eval_reports_unsupported_without_accepting_it() {
    let (rt, result) = run("have x R\neval x");
    let normal = project_stmt_normal(&result, &rt);
    assert_eq!(
        field(failure(&normal), "cause").as_str().unwrap(),
        "unsupported_expression"
    );
    let (rt, result) = run("eval 1 + 1");
    assert!(!result.is_failed());
    let detailed = project_stmt_detailed(&result, &rt);
    assert_eq!(field(&detailed, "evaluated_object").as_str().unwrap(), "2");
}

#[test]
fn detailed_nonempty_witness_preserves_checked_membership_and_body() {
    let (rt, result) = run("witness $is_nonempty_set({1, 2}) from 1:\n    1 $in {1, 2}\n");
    assert!(!result.is_failed());
    let detailed = project_stmt_detailed(&result, &rt);
    for key in ["obj_well_defined", "set_well_defined", "membership_check"] {
        assert_eq!(
            field(field(&detailed, key), "success"),
            &JsonValue::Bool(true)
        );
    }
    let body = field(&detailed, "proof_steps").as_array().unwrap();
    assert_eq!(body.len(), 1);
    assert_eq!(field(&body[0], "success"), &JsonValue::Bool(true));
    assert!(field(&detailed, "membership_check")
        .stringify()
        .contains("$in"));
    let (_, rejected) = run("witness $is_nonempty_set({1, 2}) from 3:\n    3 $in {1, 2}\n");
    assert!(rejected.is_failed());
}

#[test]
fn detailed_existential_witness_preserves_ambient_and_body_evidence() {
    let (rt, result) = run("witness exist x N st {x = 1} from 1:\n    1 = 1\n");
    assert!(!result.is_failed());
    let detailed = project_stmt_detailed(&result, &rt);
    field(&detailed, "exist_fact_well_defined");
    for key in [
        "witness_obj_well_defined",
        "witness_type_checks",
        "proof_steps",
        "body_checks",
    ] {
        let checks = field(&detailed, key).as_array().unwrap();
        assert_eq!(checks.len(), 1, "{key}");
        assert_eq!(
            field(&checks[0], "success"),
            &JsonValue::Bool(true),
            "{key}"
        );
    }
    assert_eq!(field(&detailed, "uniqueness_check"), &JsonValue::Null);
    assert!(field(&detailed, "witness_type_checks")
        .stringify()
        .contains("$in N"));
    assert!(field(&detailed, "body_checks")
        .stringify()
        .contains("1 = 1"));
    let (rt, result) = run("witness exist! x N st {x = 1} from 1:\n    1 = 1\n");
    assert!(!result.is_failed());
    let unique = project_stmt_detailed(&result, &rt);
    assert_eq!(
        field(field(&unique, "uniqueness_check"), "success"),
        &JsonValue::Bool(true)
    );
    for code in [
        "witness exist x N st {x = 1} from (-1):\n    1 = 1\n",
        "witness exist x N st {x = 2} from 1:\n    1 = 1\n",
    ] {
        let (_, rejected) = run(code);
        assert!(rejected.is_failed(), "{code}");
    }
}
