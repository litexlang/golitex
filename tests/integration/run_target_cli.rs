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
        let stdout = String::from_utf8(output.stdout).expect("stdout is UTF-8");
        assert!(
            stdout.contains("\"kind\": \"cli_error\"")
                && stdout.contains("\"ok\": false")
                && stdout.contains("unsupported CLI command combination"),
            "{stdout}"
        );
        assert!(output.stderr.is_empty(), "CLI errors belong to stdout JSON");
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
    assert!(stdout.contains("\"kind\": \"run\""), "{stdout}");
    assert!(stdout.contains("\"ok\": true"), "{stdout}");
    assert!(stdout.contains("\"outcome\": \"success\""), "{stdout}");
}

#[test]
fn batch_execute_handler_preserves_target_specific_output() {
    for (args, expected_status, target, path) in [
        (["-e", "1 = 1"], 0, "eval", None),
        (
            ["-f", "missing-batch-command-file.lit"],
            1,
            "file",
            Some("missing-batch-command-file.lit"),
        ),
        (
            ["-r", "missing-batch-command-repository"],
            1,
            "repository",
            Some("missing-batch-command-repository"),
        ),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_litex"))
            .args(args)
            .output()
            .expect("run Litex batch command");

        assert_eq!(output.status.code(), Some(expected_status));
        let stdout = String::from_utf8(output.stdout).expect("stdout is UTF-8");
        assert!(stdout.contains("\"kind\": \"run\""), "{stdout}");
        assert!(
            stdout.contains(format!("\"target\": \"{target}\"").as_str()),
            "{stdout}"
        );
        match path {
            Some(path) => assert!(
                stdout.contains(format!("\"path\": \"{path}\"").as_str()),
                "{stdout}"
            ),
            None => assert!(stdout.contains("\"path\": null"), "{stdout}"),
        }
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn retired_commands_are_no_longer_cli_combinations() {
    for args in [
        vec!["-upgrade"],
        vec!["-runner", "-e", "1 = 1"],
        vec!["-runner", "-f", "main.lit"],
        vec!["-runner", "-r", "."],
        vec!["-lean-ledger", "notes.md", "notes.lean"],
        vec!["-compact", "-e", "1 = 1"],
        vec!["-detail", "-e", "1 = 1"],
        vec!["-summarize", "-e", "1 = 1"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_litex"))
            .args(args)
            .output()
            .expect("run Litex CLI");

        assert_eq!(output.status.code(), Some(2));
        let stdout = String::from_utf8(output.stdout).expect("stdout is UTF-8");
        assert!(
            stdout.contains("\"kind\": \"cli_error\"")
                && stdout.contains("unsupported CLI command combination"),
            "{stdout}"
        );
        assert!(output.stderr.is_empty(), "CLI errors belong to stdout JSON");
    }
}

#[test]
fn retired_session_before_target_is_rejected() {
    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-session", "-before", "chapter.lit"])
        .output()
        .expect("run Litex CLI");

    assert_eq!(output.status.code(), Some(2));
    let stdout = String::from_utf8(output.stdout).expect("stdout is UTF-8");
    assert!(
        stdout.contains("\"kind\": \"cli_error\"")
            && stdout.contains("unsupported CLI command combination"),
        "{stdout}"
    );
    assert!(output.stderr.is_empty(), "CLI errors belong to stdout JSON");
}

#[test]
fn eval_graph_uses_the_canonical_eval_source_label() {
    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-factgraph", "-e", "1 = 1"])
        .output()
        .expect("run Litex CLI");

    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("stdout is UTF-8");
    assert!(stdout.contains("\"kind\": \"artifact\""), "{stdout}");
    assert!(stdout.contains("\"artifact\": \"fact_graph\""), "{stdout}");
    assert!(stdout.contains("\"content\": {"), "{stdout}");
    assert!(stdout.contains("fact:eval:1:1 = 1"), "{stdout}");
    assert!(!stdout.contains("<-e>"), "{stdout}");
}

#[test]
fn isolated_file_graph_preserves_the_file_target_error_contract() {
    let path = "missing-isolated-graph-file.lit";
    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-isolated", "-factgraph", "-f", path])
        .output()
        .expect("run isolated file graph");

    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).expect("stdout is UTF-8");
    assert!(stdout.contains("\"kind\": \"artifact\""), "{stdout}");
    assert!(stdout.contains("\"ok\": false"), "{stdout}");
    assert!(stdout.contains("\"artifact\": \"fact_graph\""), "{stdout}");
    assert!(stdout.contains("\"target\": \"file\""), "{stdout}");
    assert!(
        stdout.contains(format!("\"path\": \"{path}\"").as_str()),
        "{stdout}"
    );
    assert!(output.stderr.is_empty());
}

#[test]
fn help_version_and_unknown_option_use_minimal_json_envelopes() {
    let help = Command::new(env!("CARGO_BIN_EXE_litex"))
        .arg("-help")
        .output()
        .expect("run help");
    assert!(help.status.success());
    let help_stdout = String::from_utf8(help.stdout).expect("help stdout is UTF-8");
    assert!(help_stdout.contains("\"kind\": \"help\""), "{help_stdout}");
    assert!(help_stdout.contains("\"ok\": true"), "{help_stdout}");
    assert!(help_stdout.contains("\"entries\": ["), "{help_stdout}");
    assert!(help.stderr.is_empty());

    let version = Command::new(env!("CARGO_BIN_EXE_litex"))
        .arg("-version")
        .output()
        .expect("run version");
    assert!(version.status.success());
    let version_stdout = String::from_utf8(version.stdout).expect("version stdout is UTF-8");
    assert!(
        version_stdout.contains("\"kind\": \"version\"")
            && version_stdout.contains("\"ok\": true")
            && version_stdout.contains("\"version\":"),
        "{version_stdout}"
    );
    assert!(version.stderr.is_empty());

    let unknown = Command::new(env!("CARGO_BIN_EXE_litex"))
        .arg("-j")
        .output()
        .expect("run unknown option");
    assert_eq!(unknown.status.code(), Some(2));
    let unknown_stdout = String::from_utf8(unknown.stdout).expect("error stdout is UTF-8");
    assert!(
        unknown_stdout.contains("\"kind\": \"cli_error\"")
            && unknown_stdout.contains("\"ok\": false")
            && unknown_stdout.contains("\"message\":"),
        "{unknown_stdout}"
    );
    assert!(unknown.stderr.is_empty());
}

#[test]
fn language_selection_keeps_machine_keys_stable() {
    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-lang", "zh", "-e", "1 = 0"])
        .output()
        .expect("run localized verifier error");

    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).expect("stdout is UTF-8");
    assert!(stdout.contains("\"kind\": \"run\""), "{stdout}");
    assert!(stdout.contains("\"statement_results\": ["), "{stdout}");
    assert!(stdout.contains("\"error\": {"), "{stdout}");
    assert!(stdout.contains("\"kind\": \"verify_error\""), "{stdout}");
    assert!(stdout.contains("\"previous_error\":"), "{stdout}");
    assert!(!stdout.contains("\"错误\":"), "{stdout}");
    assert!(output.stderr.is_empty());
}
