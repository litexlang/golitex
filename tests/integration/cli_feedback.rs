//! Exercise the binary's argv, output streams, exit codes and REPL feedback.

use litex::knowledge_base::JsonValue;
use litex::launch_command::OutputLanguage;
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);

struct FixtureDir(PathBuf);

impl FixtureDir {
    fn new() -> Self {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "litex-cli-feedback-{}-{unique}-{}",
            std::process::id(),
            NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn run(&self, args: &[&str], input: Option<&str>) -> Output {
        let mut child = Command::new(env!("CARGO_BIN_EXE_litex"))
            .args(args)
            .current_dir(&self.0)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        if let Some(input) = input {
            child
                .stdin
                .take()
                .unwrap()
                .write_all(input.as_bytes())
                .unwrap();
        }
        child.wait_with_output().unwrap()
    }
}

impl Drop for FixtureDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn field<'a>(value: &'a JsonValue, name: &str) -> &'a JsonValue {
    value.as_object().unwrap().get(name).unwrap()
}

fn batch(output: &Output, exit: i32, success: bool) -> JsonValue {
    assert_eq!(output.status.code(), Some(exit), "{:?}", output);
    assert!(output.stderr.is_empty(), "{:?}", output);
    let json = JsonValue::parse(std::str::from_utf8(&output.stdout).unwrap()).unwrap();
    assert_eq!(field(&json, "success"), &JsonValue::Bool(success));
    json
}

#[test]
fn normal_json_retains_mathematical_content_for_custom_views() {
    let dir = FixtureDir::new();
    let code = "have x R = 2\nx > 0";
    let json = batch(
        &dir.run(&["-lang", "en", "-strict", "-e", code], None),
        0,
        true,
    );
    assert_eq!(field(&json, "kind").as_str().unwrap(), "run");
    assert_eq!(field(&json, "session_error"), &JsonValue::Null);
    let statements = field(&json, "statement_results").as_array().unwrap();
    assert_eq!(statements.len(), 2);
    assert_eq!(
        field(&statements[0], "statement").as_str().unwrap(),
        "have x R = 2"
    );
    assert_eq!(
        field(&statements[0], "infers").as_array().unwrap()[0]
            .as_str()
            .unwrap(),
        "x = 2"
    );
    assert_eq!(
        field(&statements[1], "stores").as_array().unwrap()[0]
            .as_str()
            .unwrap(),
        "x > 0"
    );
    assert_eq!(
        field(field(&statements[1], "proof_method"), "type")
            .as_str()
            .unwrap(),
        "builtin_rewrite"
    );
}

#[test]
fn removed_graph_flags_are_rejected_and_do_not_claim_operand_text() {
    let dir = FixtureDir::new();
    for flag in ["-graph", "--graph"] {
        for args in [vec![flag, "-e", "1 = 1"], vec!["-e", "1 = 1", flag]] {
            let output = dir.run(&args, None);
            assert_eq!(output.status.code(), Some(2));
            assert!(output.stdout.is_empty());
            assert!(std::str::from_utf8(&output.stderr)
                .unwrap()
                .starts_with("launch_error:"));
        }
    }
    let help = dir.run(&["-help"], None);
    assert!(help.status.success());
    assert!(!std::str::from_utf8(&help.stdout)
        .unwrap()
        .contains("-graph"));
    // An operand with this spelling still reaches the source parser.
    let ordinary = batch(&dir.run(&["-e", "-graph"], None), 1, false);
    assert_eq!(field(&ordinary, "kind").as_str().unwrap(), "run");
}

#[test]
fn negative_source_and_option_spellings_reach_the_source_parser() {
    let dir = FixtureDir::new();
    for command in ["-e", "-extractpython", "-extractc"] {
        let json = batch(&dir.run(&[command, "-2 < 0", "-lang", "en"], None), 0, true);
        if command == "-e" {
            assert_eq!(field(&json, "session_error"), &JsonValue::Null);
        }
        let json = batch(&dir.run(&[command, "-strict"], None), 1, false);
        let error = if command == "-e" {
            field(&json, "session_error")
        } else {
            field(&json, "error")
        };
        assert!(error.stringify().contains("strict"), "{json:?}");
        assert!(!error.stringify().contains("launch_error"));
    }
}

#[test]
fn dash_leading_paths_work_for_verification_and_both_extractors() {
    let dir = FixtureDir::new();
    fs::write(dir.0.join("-strict"), "1 = 1\n").unwrap();
    batch(&dir.run(&["-f", "-strict"], None), 0, true);
    fs::write(
        dir.0.join("-lang"),
        "# [-extract]\nhave a R = 1\n# [end of -extract]\n",
    )
    .unwrap();
    fs::create_dir(dir.0.join("-session")).unwrap();
    fs::write(
        dir.0.join("-session/litex.config"),
        "[export]\nmain = \"./main.lit\"\n",
    )
    .unwrap();
    fs::write(dir.0.join("-session/main.lit"), "have a R = 1\n").unwrap();
    batch(&dir.run(&["-r", "-session", "-strict"], None), 0, true);
    for command in ["-extractpython", "-extractc"] {
        batch(&dir.run(&[command, "-f", "-lang"], None), 0, true);
        batch(&dir.run(&[command, "-r", "-session"], None), 0, true);
    }
}

#[test]
fn batch_tokenizer_parser_and_io_errors_all_emit_json() {
    let dir = FixtureDir::new();
    for code in ["\"", "have"] {
        let json = batch(&dir.run(&["-strict", "-e", code], None), 1, false);
        let error = field(&json, "session_error").as_str().unwrap();
        assert!(error.contains("parse_error"), "{json:?}");
        assert!(!error.contains("Runtime(ParseError"));
        assert!(field(&json, "statement_results")
            .as_array()
            .unwrap()
            .is_empty());
    }
    let json = batch(&dir.run(&["-f", "missing.lit"], None), 1, false);
    assert_eq!(field(&json, "target").as_str().unwrap(), "file");
    assert_eq!(field(&json, "path").as_str().unwrap(), "missing.lit");
    assert_ne!(field(&json, "session_error"), &JsonValue::Null);
    let output = dir.run(&["-lang", "zh", "-e", "\""], None);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty());
    let json = JsonValue::parse(std::str::from_utf8(&output.stdout).unwrap()).unwrap();
    // This locale intentionally translates keys, as on successful runs.
    assert_eq!(field(&json, "成功"), &JsonValue::Bool(false));
}

#[test]
fn invalid_command_shapes_remain_launch_errors_with_exit_two() {
    let dir = FixtureDir::new();
    for args in [
        &["-e"][..],
        &["-extractpython", "-f"][..],
        &["-extractc", "-2 < 0", "extra"][..],
    ] {
        let output = dir.run(args, None);
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains("launch_error"));
    }
}

#[test]
fn repl_explains_well_definedness_failure_and_continues() {
    let dir = FixtureDir::new();
    for (args, message) in [
        (
            vec!["-strict"],
            "Could not prove that the statement is well-defined.",
        ),
        (
            vec!["-strict", "-lang", "zh"],
            "未能证明该语句中的表达式有定义。",
        ),
    ] {
        let output = dir.run(&args, Some("1 / 0 = 0\n1 = 1\nexit\n"));
        assert_eq!(output.status.code(), Some(0));
        assert!(output.stderr.is_empty());
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("1 / 0 = 0"), "{stdout}");
        assert!(stdout.contains(message), "{stdout}");
        assert!(!stdout.contains("<wd_failed>"));
        assert!(
            stdout.contains("litex> success"),
            "later statements remain usable: {stdout}"
        );
    }
}

#[test]
fn eval_still_publishes_checked_equality() {
    let dir = FixtureDir::new();
    let json = batch(
        &dir.run(&["-strict", "-e", "eval 1 + 1\n2 = 1 + 1"], None),
        0,
        true,
    );
    let results = field(&json, "statement_results").as_array().unwrap();
    assert_eq!(
        field(&results[0], "stores"),
        &JsonValue::Array(vec![JsonValue::String("1 + 1 = 2".into())])
    );
    assert_eq!(
        field(field(&results[1], "proof_method"), "type")
            .as_str()
            .unwrap(),
        "equivalence_class"
    );
}

#[test]
fn file_session_errors_retain_the_original_declaration() {
    let dir = FixtureDir::new();
    fs::write(
        dir.0.join("main.lit"),
        "thm identity:\n    ? forall x R:\n        x = x\nhave k N\nk >= 0\n",
    )
    .unwrap();
    for export in [
        None,
        Some("main = \"./main.lit\""),
        Some("other = \"./other.lit\""),
    ] {
        if let Some(export) = export {
            fs::write(dir.0.join("litex.config"), format!("[export]\n{export}\n")).unwrap();
        }
        fs::write(dir.0.join("other.lit"), "1 = 1\n").unwrap();
        let initial = batch(&dir.run(&["-strict", "-f", "main.lit"], None), 0, true);
        assert_eq!(field(&initial, "path").as_str().unwrap(), "main.lit");
        let initial_results = field(&initial, "statement_results").as_array().unwrap();
        assert!(!field(&initial_results[1], "stores")
            .as_array()
            .unwrap()
            .is_empty());
        assert!(field(&initial_results[2], "proof_method")
            .as_object()
            .unwrap()
            .get("cite")
            .is_some());
        let output = dir.run(&["-strict", "-f", "main.lit", "-session"], Some("have\n"));
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stderr.is_empty(), "{output:?}");
        let stdout = std::str::from_utf8(&output.stdout).unwrap();
        let start = stdout
            .rfind("{\n  \"kind\": \"run\"")
            .expect("final batch JSON");
        let json = JsonValue::parse(&stdout[start..]).unwrap();
        assert_eq!(field(&json, "success"), &JsonValue::Bool(false));
        assert!(field(&json, "session_error")
            .as_str()
            .unwrap()
            .contains("<repl>"));
        let results = field(&json, "statement_results").as_array().unwrap();
        assert!(field(&results[0], "statement")
            .as_str()
            .unwrap()
            .contains("thm identity:"));
        assert_eq!(
            field(&json, "statement_results"),
            field(&initial, "statement_results")
        );
        let output = dir.run(&["-strict", "-f", "main.lit", "-session"], Some("exit\n"));
        assert_eq!(output.status.code(), Some(0));
        assert!(output.stderr.is_empty());
        let stdout = std::str::from_utf8(&output.stdout).unwrap();
        let start = stdout.rfind("{\n  \"kind\": \"run\"").unwrap();
        let json = JsonValue::parse(&stdout[start..]).unwrap();
        assert_eq!(field(&json, "success"), &JsonValue::Bool(true));
        assert_eq!(
            field(&json, "statement_results"),
            field(&initial, "statement_results")
        );
    }
}

#[test]
fn eval_session_hard_errors_retain_the_initial_proof_and_report_once() {
    let dir = FixtureDir::new();
    let code = "thm identity:\n    ? forall x R:\n        x = x\nhave k N\nk >= 0";
    let initial = batch(&dir.run(&["-strict", "-e", code], None), 0, true);
    for input in [
        "have\n",
        "\"\n",
        "trust 1 = 2\n",
        "$is_finite_set(1, 2)\n",
        "$fn_eq(1, 2)\n",
    ] {
        let output = dir.run(&["-strict", "-session", "-e", code], Some(input));
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        let stdout = std::str::from_utf8(&output.stdout).unwrap();
        let start = stdout.rfind("{\n  \"kind\": \"run\"").unwrap();
        let json = JsonValue::parse(&stdout[start..]).unwrap();
        assert_eq!(field(&json, "success"), &JsonValue::Bool(false));
        let error = field(&json, "session_error").as_str().unwrap();
        if input != "trust 1 = 2\n" {
            assert!(error.contains("<repl>"), "{error}");
        }
        let results = field(&json, "statement_results").as_array().unwrap();
        assert_eq!(results.len(), 3);
        assert!(field(&results[0], "statement")
            .as_str()
            .unwrap()
            .starts_with("thm identity:"));
        assert_eq!(
            field(&json, "statement_results"),
            field(&initial, "statement_results")
        );
    }
    let output = dir.run(
        &["-strict", "-session", "-e", code],
        Some("by thm identity(2) => 2 = 2\nexit\n"),
    );
    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    assert!(String::from_utf8_lossy(&output.stdout).contains("litex> success"));
}

#[test]
fn bare_repl_reports_hard_errors_once() {
    let dir = FixtureDir::new();
    for input in ["have\n", "\"\n"] {
        let output = dir.run(&[], Some(input));
        assert_eq!(output.status.code(), Some(1));
        let stderr = std::str::from_utf8(&output.stderr).unwrap();
        assert_eq!(stderr.matches("parse_error:").count(), 1, "{stderr}");
        assert!(stderr.contains("<repl>"));
        assert!(!String::from_utf8_lossy(&output.stdout).contains("parse_error:"));
    }
}

#[cfg(unix)]
#[test]
fn non_utf8_argv_is_a_launch_error_without_panicking() {
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;
    let dir = FixtureDir::new();
    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .arg("-e")
        .arg(OsStr::from_bytes(&[0xff]))
        .current_dir(&dir.0)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let stderr = std::str::from_utf8(&output.stderr).unwrap();
    assert!(stderr.contains("argument 2 must be valid UTF-8"));
    assert!(!stderr.contains("panicked"));
}

#[test]
fn extraction_success_and_errors_share_localized_command_metadata() {
    let dir = FixtureDir::new();
    for language in OutputLanguage::ALL {
        let key = |name| litex::json_output::json_keys::localize_key(name, language);
        for (command, format) in [("-extractpython", "python"), ("-extractc", "c")] {
            let mut schemas = Vec::new();
            for (code, exit, success) in [("have a R = 1", 0, true), ("have", 1, false)] {
                let output = dir.run(&["-lang", language.as_str(), command, code], None);
                assert_eq!(output.status.code(), Some(exit), "{output:?}");
                assert!(output.stderr.is_empty(), "{output:?}");
                let json = JsonValue::parse(std::str::from_utf8(&output.stdout).unwrap()).unwrap();
                assert_eq!(field(&json, &key("success")), &JsonValue::Bool(success));
                assert_eq!(field(&json, &key("format")).as_str().unwrap(), format);
                assert_eq!(field(&json, &key("target")).as_str().unwrap(), "eval");
                assert_eq!(
                    field(&json, &key("language")).as_str().unwrap(),
                    language.as_str()
                );
                assert_eq!(field(&json, &key("path")), &JsonValue::Null);
                assert_eq!(field(&json, &key("output_path")), &JsonValue::Null);
                if success {
                    assert_eq!(field(&json, &key("error")), &JsonValue::Null);
                    assert!(!field(&json, &key("content")).as_str().unwrap().is_empty());
                } else {
                    assert_eq!(field(&json, &key("content")), &JsonValue::Null);
                    assert_eq!(
                        field(field(&json, &key("error")), &key("kind"))
                            .as_str()
                            .unwrap(),
                        "extraction_error"
                    );
                }
                schemas.push(
                    json.as_object()
                        .unwrap()
                        .keys_in_order()
                        .into_iter()
                        .map(str::to_string)
                        .collect::<Vec<_>>(),
                );
            }
            assert_eq!(schemas[0], schemas[1]);
            for (mode, target) in [("-f", "file"), ("-r", "repository")] {
                let output = dir.run(
                    &["-lang", language.as_str(), command, mode, "missing"],
                    None,
                );
                assert_eq!(output.status.code(), Some(1), "{output:?}");
                assert!(output.stderr.is_empty());
                let json = JsonValue::parse(std::str::from_utf8(&output.stdout).unwrap()).unwrap();
                assert_eq!(field(&json, &key("target")).as_str().unwrap(), target);
                assert_eq!(field(&json, &key("format")).as_str().unwrap(), format);
                assert_eq!(field(&json, &key("path")).as_str().unwrap(), "missing");
                assert_eq!(
                    field(&json, &key("language")).as_str().unwrap(),
                    language.as_str()
                );
                assert_eq!(field(&json, &key("success")), &JsonValue::Bool(false));
            }
        }
    }
}

#[test]
fn help_lists_repository_extraction_and_all_notes() {
    let dir = FixtureDir::new();
    let output = dir.run(&["-help"], None);
    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    let stdout = std::str::from_utf8(&output.stdout).unwrap();
    for text in [
        "-extractpython -r <repository>",
        "-extractc -r <repository>",
        "-session keeps",
        "-strict forbids",
        "selects JSON output language",
        "emit verified numeric/algo fragments",
    ] {
        assert!(stdout.contains(text), "missing {text}: {stdout}");
    }
}

#[test]
fn closed_stdout_keeps_command_exit_status_without_panicking() {
    let dir = FixtureDir::new();
    for (args, exit) in [
        (&["-e", "1 = 1"][..], 0),
        (&["-e", "1 = 2"][..], 1),
        (&["-e", "\""][..], 1),
        (&["-extractpython", "have a R = 1"][..], 0),
        (&["-help"][..], 0),
        (&["-version"][..], 0),
        (&[][..], 0),
    ] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_litex"))
            .args(args)
            .current_dir(&dir.0)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        drop(child.stdout.take());
        let output = child.wait_with_output().unwrap();
        assert_eq!(output.status.code(), Some(exit), "{args:?}: {output:?}");
        assert!(output.stderr.is_empty(), "{args:?}: {output:?}");
    }
}
