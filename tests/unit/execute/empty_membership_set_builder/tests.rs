use crate::prelude::*;

fn run(code: &str) -> RunLitexCodeResult {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    runtime.run_litex_code(code).unwrap()
}

#[test]
fn empty_membership_set_builder_exact_positive_tracer() {
    let result = run(include_str!(
        "../../../../examples/proof_nodes/equal/by_builtin_rule/set_builder_empty_membership.lit"
    ));
    assert!(result.success && result.session_error.is_none());
    assert!(run("{x N: x < 0} = {}").success);
}

#[test]
fn empty_membership_set_builder_keeps_nonempty_and_partial_boundaries() {
    for code in [
        "{x {0}: x $in {0}} = {}",
        "{x {0}: not x $in {}} = {}",
        "{x {0}: x $in {} or x = 0} = {}",
        "{x N: 1 / 0 $in {}} = {}",
        "{x R: x < 0} = {}",
    ] {
        let result = run(code);
        assert!(!result.success, "{code}");
        assert!(
            result.session_error.is_none(),
            "{code}: {:?}",
            result.session_error
        );
    }
}
