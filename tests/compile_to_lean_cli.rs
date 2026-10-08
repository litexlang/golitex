use std::process::Command;

#[test]
fn lean_cli_emits_the_complete_canonical_source_without_json_wrapping() {
    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args([
            "-strict",
            "-lean",
            "-f",
            "lean/examples/one_equals_itself/statement.lit",
        ])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert_eq!(
        output.stdout,
        std::fs::read("lean/examples/one_equals_itself/statement.lean").unwrap()
    );
}

#[test]
fn lean_cli_failures_emit_only_phase_diagnostics() {
    for (path, message) in [
        (
            "tests/fixtures/compile_to_lean/failed_fact.lit",
            "phase=verify: statement 1 failed Litex verification",
        ),
        (
            "tests/fixtures/compile_to_lean/unsupported_constructor.lit",
            "phase=compile:",
        ),
        (
            "tests/fixtures/compile_to_lean/missing.lit",
            "phase=verify: cannot read",
        ),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_litex"))
            .args(["-lean", "-f", path])
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        assert!(String::from_utf8(output.stderr).unwrap().contains(message));
    }
}

#[test]
fn invalid_lean_launches_use_the_common_argument_error_path() {
    for args in [
        vec!["-lean", "-f", "identity.lit", "-lean"],
        vec!["-lean", "-f", "identity.lit", "-session"],
        vec!["-lean", "-latex", "-f", "identity.lit"],
        vec!["-lean", "-e", "1 = 1"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_litex"))
            .args(&args)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2), "{args:?}: {output:?}");
        assert!(output.stdout.is_empty(), "{args:?}: {output:?}");
        assert!(!output.stderr.is_empty(), "{args:?}");
    }
}
