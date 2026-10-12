use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn cartesian_field_coordinates_use_checked_finite_function_evidence() {
    let mut runtime = runtime();
    assert!(
        runtime
            .run_litex_code(include_str!("../examples/wd/field_sequence_calls.lit"))
            .unwrap()
            .success
    );
    let run = runtime
        .run_litex_code(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/wd/cartesian_field_coordinates.lit"
        )))
        .unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{:#?}",
        run.session_error
    );
}

#[test]
fn cartesian_field_coordinates_reject_invalid_indices_values_and_scalar_calls() {
    let mut runtime = runtime();
    let prefix = "struct Pointed:\n    point R × R\n    tag R\n(0, 0) $in R × R\nrelease thm struct_member(((0, 0), 0), &Pointed)\nhave item &Pointed = ((0, 0), 0)\nitem.point = (0, 0)\n";
    assert!(runtime.run_litex_code(prefix).unwrap().success);
    for code in [
        "item.point(0) = 0",
        "item.point(3) = 0",
        "item.point(1 / 2) = 0",
        "item.point(2) = 1",
        "item.tag(1) = 0",
    ] {
        let run = runtime.run_litex_code(code).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{code}");
        assert!(runtime.run_litex_code("item.point(2) = 0").unwrap().success);
    }
}
