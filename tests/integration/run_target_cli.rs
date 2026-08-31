use std::process::Command;

#[test]
fn unsupported_combinations_are_rejected_before_dispatch() {
    for args in [
        vec!["-isolated", "-e", "1 = 1"],
        vec!["-isolated", "-r", "."],
        vec!["-isolated", "-defgraph", "-r", "."],
        vec!["-f", "missing.lit", "extra"],
        vec!["-e", "1 = 1", "extra"],
        vec!["-help", "extra"],
        vec!["-strict", "-help"],
        vec!["-e", "1 = 1", "-strict"],
        vec!["-strict", "-strict", "-e", "1 = 1"],
        vec!["-strict", "-compact", "-e", "1 = 1"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_litex"))
            .args(args)
            .output()
            .expect("run Litex CLI");

        assert_eq!(output.status.code(), Some(2));
        let stderr = String::from_utf8(output.stderr).expect("stderr is UTF-8");
        assert!(
            stderr.contains("unsupported CLI command combination"),
            "{stderr}"
        );
    }
}

#[test]
fn strict_execute_uses_the_canonical_prefix_position() {
    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-strict", "-e", "1 = 1"])
        .output()
        .expect("run strict Litex CLI");

    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("stdout is UTF-8");
    assert!(stdout.contains("\"outcome\": \"success\""), "{stdout}");
}

#[test]
fn retired_commands_are_no_longer_cli_combinations() {
    for args in [
        vec!["-upgrade"],
        vec!["-runner", "-e", "1 = 1"],
        vec!["-runner", "-f", "main.lit"],
        vec!["-runner", "-r", "."],
        vec!["-lean-ledger", "notes.md", "notes.lean"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_litex"))
            .args(args)
            .output()
            .expect("run Litex CLI");

        assert_eq!(output.status.code(), Some(2));
        let stderr = String::from_utf8(output.stderr).expect("stderr is UTF-8");
        assert!(
            stderr.contains("unsupported CLI command combination"),
            "{stderr}"
        );
    }
}

#[test]
fn retired_session_before_target_is_rejected() {
    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-session", "-before", "chapter.lit"])
        .output()
        .expect("run Litex CLI");

    assert_eq!(output.status.code(), Some(2));
    let stderr = String::from_utf8(output.stderr).expect("stderr is UTF-8");
    assert!(
        stderr.contains("unsupported CLI command combination"),
        "{stderr}"
    );
}

#[test]
fn eval_graph_uses_the_canonical_eval_source_label() {
    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-factgraph", "-e", "1 = 1"])
        .output()
        .expect("run Litex CLI");

    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("stdout is UTF-8");
    assert!(stdout.contains("fact:eval:1:1 = 1"), "{stdout}");
    assert!(!stdout.contains("<-e>"), "{stdout}");
}
