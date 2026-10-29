use crate::prelude::*;

#[test]
fn negated_order_composes_all_four_positive_complements() {
    for (premise, goal) in [
        ("x <= 900", "not x > 1070"),
        ("x >= 1260", "not x < 1250"),
        ("x <= 900", "not x >= 1070"),
        ("x >= 1260", "not x <= 1250"),
    ] {
        let mut rt = runtime();
        let source = format!("forall x R:\n    {premise}\n    =>:\n        {goal}\n");
        let result = rt.run_litex_code(&source).unwrap();
        let output = crate::json_output::emit_run_detailed(&result, &rt, "eval", None);
        assert!(
            result.success,
            "{source}: {}",
            crate::json_output::emit_run_normal(&result, &rt, "eval", None)
        );
        assert!(
            output.contains("\"strategy\": \"NegatedOrder\""),
            "{output}"
        );
        assert!(output.contains("proof_of_requirement_facts"));
        assert!(output.contains("$in R"));
    }
}

#[test]
fn negated_order_rejects_false_missing_nonstrict_and_nonreal_premises() {
    for source in [
        "forall x R:\n    x <= 900\n    =>:\n        not x > 899\n",
        "forall x R:\n    x >= 1260\n    =>:\n        not x < 1261\n",
        "forall x R:\n    x <= 1070\n    =>:\n        not x >= 1070\n",
        "forall x R:\n    x >= 1250\n    =>:\n        not x <= 1250\n",
        "forall x R:\n    not x > 1070\n",
        "forall x C:\n    not x > 1070\n",
        "forall x R:\n    1 / (x - x) <= 900\n    =>:\n        not 1 / (x - x) > 1070\n",
    ] {
        let mut rt = runtime();
        let result = rt.run_litex_code(source).unwrap();
        assert!(
            !result.success && result.session_error.is_none(),
            "{source}"
        );
    }
}

#[test]
fn negated_order_closes_integer_product_contradictions() {
    let mut rt = runtime();
    let source =
        std::fs::read_to_string(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(
            "examples/proof_nodes/atomic/by_builtin_strategy/contra_integer_product_order.lit",
        ))
        .unwrap();
    let result = rt.run_litex_code(&source).unwrap();
    let output = crate::json_output::emit_run_detailed(&result, &rt, "eval", None);
    assert!(
        result.success,
        "{}",
        crate::json_output::emit_run_normal(&result, &rt, "eval", None)
    );
    assert!(output.contains("\"strategy\": \"NegatedOrder\""));
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn negated_order_does_not_manufacture_a_contradiction() {
    let mut rt = runtime();
    let source = "claim:\n    ? forall n N+:\n        7*n > 190\n        =>:\n            n >= 29\n    by contra:\n        ? n >= 29\n        n < 29\n        n <= 28\n        7*n <= 196\n        impossible 7*n > 190\n";
    let result = rt.run_litex_code(source).unwrap();
    assert!(!result.success && result.session_error.is_none());
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(!rt.run_litex_code("n < 29").unwrap().success);
}

#[test]
fn negated_order_keeps_certificates_in_reading() {
    let reading = crate::reading::build_reading(
        &crate::reading::ReadingInput::Source(
            "forall x R:\n    x <= 900\n    =>:\n        not x > 1070\n".into(),
        ),
        true,
        OutputLanguage::English,
    );
    assert!(reading.success);
    let output = reading.document.stringify();
    assert!(output.contains("NegatedOrderStrategySingleStep"));
    assert!(output.contains("requirement_facts"));
    assert!(output.contains("proof_of_requirement_facts"));
}

#[test]
fn negated_order_lean_replay_stays_explicitly_unsupported() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code("forall x R:\n    x <= 900\n    =>:\n        not x > 1070\n")
        .unwrap();
    assert!(run.success);
    let error = crate::compile_to_lean::LitexToLeanCompiler::new(rt)
        .compile_run(&run, "negated_order")
        .unwrap_err();
    assert_eq!(error.route, "Atomic/BuiltinStrategy");
}

fn runtime() -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    )
}
