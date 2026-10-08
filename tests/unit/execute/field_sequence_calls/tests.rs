use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn field_sequence_calls_use_declared_exact_signatures() {
    let mut runtime = runtime();
    let run = runtime
        .run_litex_code(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/wd/field_sequence_calls.lit"
        )))
        .unwrap();
    assert!(run.success && run.session_error.is_none());
}

#[test]
fn field_sequence_calls_reject_wrong_indices_and_continue_after_failure() {
    let mut runtime = runtime();
    assert!(
        runtime
            .run_litex_code(
                "struct SequenceFields<n N+>:\n    finite finite_seq(R,n)\n    infinite seq(R)\n"
            )
            .unwrap()
            .success
    );
    for code in [
        "claim:\n    ? forall value &SequenceFields<2>:\n        value.finite(0) $in R\n",
        "claim:\n    ? forall value &SequenceFields<2>:\n        value.finite(3) $in R\n",
        "claim:\n    ? forall value &SequenceFields<2>:\n        value.infinite(0) $in R\n",
    ] {
        let run = runtime.run_litex_code(code).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{code}");
        assert!(runtime.run_litex_code("claim:\n    ? forall value &SequenceFields<2>:\n        value.finite(1) $in R\n        value.infinite(1) $in R\n").unwrap().success);
    }
}

#[test]
fn field_sequence_calls_do_not_make_scalar_fields_callable() {
    let mut runtime = runtime();
    let run = runtime.run_litex_code("struct NonFunctions:\n    first R\n    second R\nhave fn bad(value &NonFunctions) R = value.first(1)\n").unwrap();
    assert!(!run.success && run.session_error.is_none());
}
