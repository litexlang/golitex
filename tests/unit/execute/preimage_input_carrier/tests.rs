use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn preimage_input_carrier_checks_the_guarded_tuple_and_family_tracer() {
    let run = runtime().run_litex_code(
        include_str!("../../../../examples/wd/preimage_input_carrier.lit"),
    ).unwrap();
    assert!(run.success && run.session_error.is_none());
}

#[test]
fn preimage_input_carrier_rejects_other_carriers_and_keeps_domain_checks() {
    let mut rt = runtime();
    assert!(rt.run_litex_code("have fn square(x R) R = x^2\nhave fn reciprocal(x R: x != 0) R = 1 / x\n").unwrap().success);
    for code in [
        "preimage(square, 4) $subset N",
        "preimage_set(square, {4}) $in power_set(N)",
        "preimage_set(square, {4}) $subset {2}",
        "preimage_set(1, {}) $subset R",
        "preimage(square, 1 / 0) $subset R",
        "0 $in preimage(reciprocal, 0)",
        "0 $in preimage_set(reciprocal, {0})",
    ] {
        let run = rt.run_litex_code(code).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{code}");
        assert!(rt.run_litex_code("preimage_set(square, {4}) $in power_set(R)").unwrap().success);
    }
}

#[test]
fn preimage_input_carrier_projects_construction_and_matching_evidence() {
    let mut rt = runtime();
    let run = rt.run_litex_code("have fn square(x R) R = x^2\npreimage_set(square, {4}) $subset R\n").unwrap();
    assert!(run.success);
    let output = crate::json_output::project_run_normal(&run, &rt, "eval", None).stringify();
    assert!(output.contains("FunctionPreimageSubsetOfInputCarrier"));
    assert!(output.contains("construction"));
    assert!(output.contains("carrier_match"));
}
