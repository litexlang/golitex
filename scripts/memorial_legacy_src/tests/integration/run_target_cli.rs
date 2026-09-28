use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn cli_fixture_dir(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!("litex-cli-{}-{}", name, std::process::id()))
}

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
fn plain_file_auto_selects_isolated_or_project_context_and_exits() {
    let standalone = cli_fixture_dir("auto-standalone-file");
    let _ = fs::remove_dir_all(&standalone);
    let standalone_parent = standalone.join("nested");
    fs::create_dir_all(&standalone_parent).expect("create standalone fixture");
    fs::write(
        standalone.join("litex.config"),
        "ancestor configuration must not be discovered\n",
    )
    .expect("write ignored ancestor config");
    let standalone_file = standalone_parent.join("scratch.lit");
    fs::write(&standalone_file, "have standalone_value R = 1\n").expect("write standalone file");

    let standalone_output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-f", standalone_file.to_string_lossy().as_ref()])
        .output()
        .expect("run auto-isolated file");
    assert!(standalone_output.status.success());
    let standalone_stdout =
        String::from_utf8(standalone_output.stdout).expect("standalone stdout is UTF-8");
    assert!(standalone_stdout.contains("\"kind\": \"run\""));
    assert!(standalone_stdout.contains("\"ok\": true"));
    assert!(standalone_stdout.contains("standalone_value"));
    assert!(
        !standalone_stdout.contains("\"kind\":\"stream\"")
            && !standalone_stdout.contains("\"kind\": \"stream\""),
        "plain -f must exit after its run document: {standalone_stdout}"
    );
    assert!(standalone_output.stderr.is_empty());

    let project = cli_fixture_dir("auto-project-file");
    let _ = fs::remove_dir_all(&project);
    fs::create_dir_all(&project).expect("create project fixture");
    fs::write(
        project.join("litex.config"),
        "[hierarchy]\nmodule\n\n[export]\nbefore = \"./before.lit\"\ntarget = \"./target.lit\"\n",
    )
    .expect("write project config");
    fs::write(project.join("before.lit"), "have configured_value R = 2\n")
        .expect("write project prefix");
    let project_file = project.join("target.lit");
    fs::write(&project_file, "before::configured_value = 2\n").expect("write project target");

    let project_output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-f", project_file.to_string_lossy().as_ref()])
        .output()
        .expect("run configured file");
    assert!(project_output.status.success());
    let project_stdout = String::from_utf8(project_output.stdout).expect("project stdout is UTF-8");
    assert!(project_stdout.contains("\"kind\": \"run\""));
    assert!(project_stdout.contains("\"ok\": true"));
    assert!(project_stdout.contains("before::configured_value = 2"));
    assert!(!project_stdout.contains("\"kind\": \"stream\""));
    assert!(project_output.stderr.is_empty());

    let _ = fs::remove_dir_all(&standalone);
    let _ = fs::remove_dir_all(&project);
}

#[test]
fn present_invalid_config_is_an_error_but_explicit_isolation_bypasses_it() {
    let directory = cli_fixture_dir("invalid-config-boundary");
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir_all(&directory).expect("create invalid-config fixture");
    fs::write(
        directory.join("litex.config"),
        "not a valid project config\n",
    )
    .expect("write invalid config");
    let file = directory.join("scratch.lit");
    fs::write(&file, "have isolated_value R = 3\n").expect("write standalone source");

    let project_output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-f", file.to_string_lossy().as_ref()])
        .output()
        .expect("run file beside invalid config");
    assert_eq!(project_output.status.code(), Some(1));
    let project_stdout = String::from_utf8(project_output.stdout).expect("project stdout is UTF-8");
    assert!(project_stdout.contains("\"ok\": false"), "{project_stdout}");
    assert!(project_stdout.contains("litex.config"), "{project_stdout}");

    let isolated_output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-isolated", "-f", file.to_string_lossy().as_ref()])
        .output()
        .expect("force isolated file run");
    assert!(isolated_output.status.success());
    let isolated_stdout =
        String::from_utf8(isolated_output.stdout).expect("isolated stdout is UTF-8");
    assert!(isolated_stdout.contains("\"kind\": \"run\""));
    assert!(isolated_stdout.contains("\"ok\": true"));
    assert!(isolated_stdout.contains("isolated_value"));
    assert!(
        !isolated_stdout.contains("\"kind\":\"stream\"")
            && !isolated_stdout.contains("\"kind\": \"stream\""),
        "explicit isolated -f must be batch-only: {isolated_stdout}"
    );
    assert!(isolated_output.stderr.is_empty());

    let _ = fs::remove_dir_all(&directory);
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
