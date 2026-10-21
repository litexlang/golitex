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

fn batch(output: &Output, exit: i32, succeeded: bool) -> JsonValue {
    assert_eq!(output.status.code(), Some(exit), "{:?}", output);
    assert!(output.stderr.is_empty(), "{:?}", output);
    let json = JsonValue::parse(std::str::from_utf8(&output.stdout).unwrap()).unwrap();
    match field(&json, "kind").as_str().unwrap() {
        "run" => assert_eq!(
            field(&json, "run_result").as_str().ok(),
            Some(if succeeded { "success" } else { "failure" })
        ),
        "artifact" => assert_eq!(
            field(&json, "artifact_result").as_str().ok(),
            Some(if succeeded { "success" } else { "failure" })
        ),
        kind => panic!("unexpected batch kind {kind}"),
    }
    json
}

fn assert_session_state(json: &JsonValue, terminated: bool) {
    assert_eq!(
        field(json, "session_terminated"),
        &JsonValue::Bool(terminated)
    );
    assert_eq!(field(json, "termination") == &JsonValue::Null, !terminated);
}

fn assert_no_generic_success_key(value: &JsonValue) {
    match value {
        JsonValue::Array(items) => items.iter().for_each(assert_no_generic_success_key),
        JsonValue::Object(object) => {
            for (key, value) in object.iter() {
                assert_ne!(key, "success", "generic result key leaked in {value:?}");
                assert_no_generic_success_key(value);
            }
        }
        _ => {}
    }
}

#[test]
fn import_diagnostics_preserve_missing_paths_cycles_and_rejected_exports() {
    let dir = FixtureDir::new();
    fs::create_dir(dir.0.join("a")).unwrap();
    fs::create_dir(dir.0.join("b")).unwrap();
    for path in ["main.lit", "a/main.lit", "b/main.lit"] {
        fs::write(dir.0.join(path), "1 = 1\n").unwrap();
    }
    fs::write(
        dir.0.join("litex.config"),
        "[export]\nmain = \"./main.lit\"\n[import]\nA = \"./a\"\n",
    )
    .unwrap();
    fs::write(
        dir.0.join("a/litex.config"),
        "[export]\nmain = \"./main.lit\"\n[import]\nMissing = \"../missing\"\n",
    )
    .unwrap();
    let missing = batch(&dir.run(&["-lang", "en", "-e", "1 = 1"], None), 1, false);
    assert_session_state(&missing, true);
    let termination = field(&missing, "termination");
    assert_eq!(field(termination, "phase").as_str(), Ok("import"));
    assert_eq!(
        field(termination, "cause").as_str(),
        Ok("missing_directory")
    );
    assert!(field(termination, "path")
        .as_str()
        .unwrap()
        .ends_with("missing"));
    assert_eq!(
        field(termination, "import_chain").as_array().unwrap().len(),
        3
    );

    fs::write(
        dir.0.join("a/litex.config"),
        "[export]\nmain = \"./main.lit\"\n[import]\nB = \"../b\"\n",
    )
    .unwrap();
    fs::write(
        dir.0.join("b/litex.config"),
        "[export]\nmain = \"./main.lit\"\n[import]\nA = \"../a\"\n",
    )
    .unwrap();
    let cycle = batch(&dir.run(&["-lang", "en", "-r", "."], None), 1, false);
    assert_session_state(&cycle, true);
    let termination = field(&cycle, "termination");
    assert_eq!(field(termination, "cause").as_str(), Ok("cycle"));
    let chain = field(termination, "import_chain").as_array().unwrap();
    assert_eq!(chain.len(), 4);
    assert_eq!(chain[1], chain[3]);
    assert!(chain[1].as_str().unwrap().ends_with("/a"));
    assert!(chain[2].as_str().unwrap().ends_with("/b"));

    fs::write(
        dir.0.join("a/litex.config"),
        "[export]\nbad = \"./bad.lit\"\n",
    )
    .unwrap();
    fs::write(dir.0.join("a/bad.lit"), "1 = 2\n").unwrap();
    fs::write(dir.0.join("target.lit"), "1 = 1\n").unwrap();
    for args in [
        vec!["-lang", "en", "-e", "1 = 1"],
        vec!["-lang", "en", "-f", "target.lit"],
    ] {
        let rejected = batch(&dir.run(&args, None), 1, false);
        assert_session_state(&rejected, true);
        let termination = field(&rejected, "termination");
        assert_eq!(field(termination, "cause").as_str(), Ok("rejected_export"));
        assert!(field(termination, "path")
            .as_str()
            .unwrap()
            .ends_with("bad.lit"));
        assert_eq!(
            field(termination, "failed_statements").as_array().unwrap()[0].as_str(),
            Ok("1 = 2")
        );
    }
    fs::write(dir.0.join("a/bad.lit"), "1 = 1\n").unwrap();
    batch(&dir.run(&["-lang", "en", "-e", "1 = 1"], None), 0, true);
}

#[test]
fn definition_and_eval_diagnostics_reach_the_cli_without_terminating_session() {
    let dir = FixtureDir::new();
    let code = "prop positive(x R):\n    x > 0\nby def $positive(0)\nby def $positive(1)\n";
    let json = batch(
        &dir.run(&["-lang", "en", "-strict", "-e", code], None),
        1,
        false,
    );
    assert_session_state(&json, false);
    let statements = field(&json, "statement_results").as_array().unwrap();
    let failure = &field(&json, "errors").as_array().unwrap()[0];
    assert_eq!(
        field(failure, "phase").as_str(),
        Ok("definition_requirement")
    );
    assert_eq!(field(failure, "goal").as_str(), Ok("0 > 0"));
    assert_eq!(
        field(&statements[2], "statement_result").as_str(),
        Ok("accepted")
    );

    let json = batch(
        &dir.run(
            &[
                "-lang",
                "en",
                "-strict",
                "-e",
                "eval sum(1,1025,fn(k Z) Z {1})\neval 1 + 1",
            ],
            None,
        ),
        1,
        false,
    );
    assert_session_state(&json, false);
    let statements = field(&json, "statement_results").as_array().unwrap();
    let reason = &field(&json, "errors").as_array().unwrap()[0];
    assert_eq!(field(reason, "category").as_str(), Ok("aggregate_budget"));
    assert_eq!(
        field(reason, "cause").as_str(),
        Ok("aggregate_budget_exceeded")
    );
    assert_eq!(
        field(&statements[1], "statement_result").as_str(),
        Ok("accepted")
    );
}

#[test]
fn nested_failure_source_location_reaches_file_output() {
    let dir = FixtureDir::new();
    fs::write(
        dir.0.join("nested.lit"),
        "claim:\n    ? 1 = 1\n    sketch:\n        have x {1} = 2\n",
    )
    .unwrap();
    let json = batch(
        &dir.run(&["-lang", "en", "-strict", "-f", "nested.lit"], None),
        1,
        false,
    );
    assert_session_state(&json, false);
    let failure = &field(&json, "errors").as_array().unwrap()[0];
    assert_eq!(
        field(failure, "failed_statement").as_str(),
        Ok("have x {1} = 2")
    );
    let source = field(failure, "source_location");
    assert_eq!(field(source, "line"), &JsonValue::Number(4.0));
    assert!(field(source, "path")
        .as_str()
        .unwrap()
        .ends_with("nested.lit"));
}

#[test]
fn run_result_and_session_termination_are_orthogonal() {
    let dir = FixtureDir::new();

    let accepted = batch(&dir.run(&["-lang", "en", "-e", "1 = 1"], None), 0, true);
    assert_session_state(&accepted, false);

    let rejected = batch(&dir.run(&["-lang", "en", "-e", "1 = 2"], None), 1, false);
    assert_session_state(&rejected, false);

    let malformed = batch(&dir.run(&["-lang", "en", "-e", "have"], None), 1, false);
    assert_session_state(&malformed, false);
    assert_eq!(
        field(&field(&malformed, "errors").as_array().unwrap()[0], "phase").as_str(),
        Ok("parse")
    );
    let terminated = batch(
        &dir.run(&["-lang", "en", "-f", "missing.lit"], None),
        1,
        false,
    );
    assert_session_state(&terminated, true);
    assert_eq!(
        field(field(&terminated, "termination"), "phase").as_str(),
        Ok("io")
    );

    for value in [&accepted, &rejected, &terminated] {
        assert_no_generic_success_key(value);
    }
}

#[test]
fn positive_integer_alias_normalizes_output_and_preserves_domain() {
    let dir = FixtureDir::new();
    let code = "Z+ = N+\nℤ+ = ℕ+\nhave n Z+ = 2\nn $in N+\nhave fn successor(k N+) Z+ = k + 1\nsuccessor(n) $in N+\nhave fn identity(k Z+) N+ = k\nidentity(n) = n\n";
    let json = batch(
        &dir.run(&["-lang", "en", "-strict", "-e", code], None),
        0,
        true,
    );
    assert_session_state(&json, false);
    let statements = field(&json, "statement_results").as_array().unwrap();
    for index in [0, 1] {
        assert_eq!(
            field(&statements[index], "statement").as_str().unwrap(),
            "N+ = N+"
        );
    }
    assert_eq!(
        field(&statements[2], "statement").as_str().unwrap(),
        "have n N+ = 2"
    );
    for statement in statements {
        let text = field(statement, "statement").as_str().unwrap();
        assert!(!text.contains("Z+"), "{text}");
        assert!(!text.contains("ℤ+"), "{text}");
    }
    for domain in ["N+", "Z+", "ℕ+", "ℤ+"] {
        for value in ["0", "-1", "0.5"] {
            let code = format!("have invalid {domain} = {value}");
            let json = batch(
                &dir.run(&["-lang", "en", "-strict", "-e", &code], None),
                1,
                false,
            );
            assert_session_state(&json, false);
        }
    }
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
    assert_session_state(&json, false);
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
            assert_session_state(&json, false);
        }
        let json = batch(&dir.run(&[command, "-strict"], None), 1, false);
        let error = if command == "-e" {
            field(&json, "errors")
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
        assert_session_state(&json, false);
        let failure = &field(&json, "errors").as_array().unwrap()[0];
        assert_eq!(field(failure, "phase").as_str(), Ok("parse"));
        let error = field(failure, "message").as_str().unwrap();
        assert!(!error.is_empty(), "{json:?}");
        assert!(!error.contains("Runtime(ParseError"));
        assert_eq!(
            field(&json, "statement_results").as_array().unwrap().len(),
            1
        );
    }
    let json = batch(&dir.run(&["-f", "missing.lit"], None), 1, false);
    assert_eq!(field(&json, "target").as_str().unwrap(), "file");
    assert_eq!(field(&json, "path").as_str().unwrap(), "missing.lit");
    assert_session_state(&json, true);
    let output = dir.run(&["-lang", "zh", "-e", "\""], None);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty());
    let json = JsonValue::parse(std::str::from_utf8(&output.stdout).unwrap()).unwrap();
    // This locale intentionally translates keys, as on successful runs.
    assert_eq!(field(&json, "运行结果").as_str().ok(), Some("failure"));
    assert_eq!(field(&json, "会话已终止"), &JsonValue::Bool(false));
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
        let output = dir.run(&args, Some("(1 / 0) = 0\n1 = 1\nexit\n"));
        assert_eq!(output.status.code(), Some(0));
        assert!(output.stderr.is_empty());
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("(1 / 0) = 0"), "{stdout}");
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
        &JsonValue::Array(vec![JsonValue::String("(1 + 1) = 2".into())])
    );
    assert_eq!(
        field(field(&results[1], "proof_method"), "type")
            .as_str()
            .unwrap(),
        "equivalence_class"
    );
}

#[test]
fn file_session_recovers_parse_errors_and_retains_the_original_declaration() {
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
        let output = dir.run(
            &["-strict", "-f", "main.lit", "-session"],
            Some("have\nby thm identity(2) => 2 = 2\nexit\n"),
        );
        assert_eq!(output.status.code(), Some(0));
        assert!(output.stderr.is_empty(), "{output:?}");
        let stdout = std::str::from_utf8(&output.stdout).unwrap();
        let start = stdout
            .rfind("{\n  \"kind\": \"run\"")
            .expect("final batch JSON");
        let json = JsonValue::parse(&stdout[start..]).unwrap();
        assert_eq!(field(&json, "run_result").as_str().ok(), Some("success"));
        assert_session_state(&json, false);
        assert!(stdout.contains("<repl>"));
        assert!(stdout.contains("litex> success"), "{stdout}");
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
        assert_eq!(field(&json, "run_result").as_str().ok(), Some("success"));
        assert_session_state(&json, false);
        assert_eq!(
            field(&json, "statement_results"),
            field(&initial, "statement_results")
        );
    }
}

#[test]
fn file_session_preserves_context_and_reports_a_soft_failure() {
    let dir = FixtureDir::new();
    fs::write(dir.0.join("main.lit"), "have k N\nk >= 0\n").unwrap();
    let output = dir.run(
        &["-strict", "-f", "main.lit", "-session"],
        Some("k >= 0\n1 = 2\nk >= 0\nexit\n"),
    );
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let stdout = std::str::from_utf8(&output.stdout).unwrap();
    assert_eq!(stdout.matches("litex> success").count(), 2, "{stdout}");
    assert!(stdout.contains("\"run_result\": \"failure\""), "{stdout}");
    let start = stdout.rfind("{\n  \"kind\": \"run\"").unwrap();
    let json = JsonValue::parse(&stdout[start..]).unwrap();
    assert_eq!(field(&json, "path").as_str().unwrap(), "main.lit");
    assert_eq!(field(&json, "run_result").as_str().ok(), Some("success"));
    assert_session_state(&json, false);
}

#[test]
fn eval_session_hard_errors_retain_the_initial_proof_and_report_once() {
    let dir = FixtureDir::new();
    let code = "thm identity:\n    ? forall x R:\n        x = x\nhave k N\nk >= 0";
    let initial = batch(&dir.run(&["-strict", "-e", code], None), 0, true);
    for input in ["trust 1 = 2\n"] {
        let output = dir.run(&["-strict", "-session", "-e", code], Some(input));
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        let stdout = std::str::from_utf8(&output.stdout).unwrap();
        let start = stdout.rfind("{\n  \"kind\": \"run\"").unwrap();
        let json = JsonValue::parse(&stdout[start..]).unwrap();
        assert_eq!(field(&json, "run_result").as_str().ok(), Some("failure"));
        assert_session_state(&json, true);
        let error = field(field(&json, "termination"), "message")
            .as_str()
            .unwrap();
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
fn parse_feedback_keeps_source_and_location_without_terminating() {
    let dir = FixtureDir::new();
    let code = "have a R = (1 + 2";
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        let output = dir.run(&["-lang", language.as_str(), "-e", code], None);
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stderr.is_empty());
        let json = JsonValue::parse(std::str::from_utf8(&output.stdout).unwrap()).unwrap();
        let key = |name| litex::json_output::json_keys::localize_key(name, language);
        assert_eq!(
            field(&json, &key("session_terminated")),
            &JsonValue::Bool(false)
        );
        let failure = &field(&json, &key("errors")).as_array().unwrap()[0];
        assert_eq!(field(failure, &key("statement")).as_str(), Ok(code));
        assert_eq!(
            field(failure, &key("message")).as_str(),
            Ok("expected `)`, reached end of line")
        );
        let source = field(failure, &key("source_location"));
        assert_eq!(field(source, &key("path")).as_str(), Ok("<eval>"));
        assert_eq!(field(source, &key("line")), &JsonValue::Number(1.0));
        assert_eq!(field(source, &key("column")), &JsonValue::Number(18.0));
    }
    fs::write(dir.0.join("example.lit"), format!("let kept = 1\n{code}\n")).unwrap();
    let json = batch(&dir.run(&["-f", "example.lit"], None), 1, false);
    assert_session_state(&json, false);
    assert_eq!(
        field(&json, "statement_results").as_array().unwrap().len(),
        2
    );
    let source = field(
        &field(&json, "errors").as_array().unwrap()[0],
        "source_location",
    );
    assert_eq!(field(source, "line"), &JsonValue::Number(2.0));
    assert_eq!(field(source, "column"), &JsonValue::Number(18.0));
    assert_eq!(field(source, "path").as_str(), Ok("example.lit"));
}

#[test]
fn session_recovers_incomplete_functions_tokenizer_errors_and_proof_misses() {
    let dir = FixtureDir::new();
    let input = "have fn incomplete_function(x R) R = x +\na $in R\n\"\na = 3\nhave fn incomplete_function(x R) R = x + 1\nincomplete_function(2) = 3\na = a\nexit\n";
    for (args, input, successes) in [
        (vec!["-strict"], format!("have a R\n{input}"), 5),
        (
            vec!["-strict", "-session", "-e", "have a R"],
            input.to_string(),
            4,
        ),
    ] {
        let output = dir.run(&args, Some(&input));
        assert_eq!(output.status.code(), Some(0), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert_eq!(
            stdout.matches("litex> success").count(),
            successes,
            "{stdout}"
        );
        assert_eq!(
            stdout.matches("\"run_result\": \"failure\"").count(),
            3,
            "{stdout}"
        );
        assert!(!stdout.contains("\"session_terminated\": true"), "{stdout}");
        assert!(!stdout.contains("\"verification\""), "{stdout}");
        assert!(stdout.contains("expected object"), "{stdout}");
        assert!(stdout.contains("<repl>"), "{stdout}");
        if args.contains(&"-session") {
            let start = stdout.rfind("{\n  \"kind\": \"run\"").unwrap();
            let final_json = JsonValue::parse(&stdout[start..]).unwrap();
            assert_eq!(field(&final_json, "run_result").as_str(), Ok("success"));
            assert!(field(&final_json, "errors").as_array().unwrap().is_empty());
        }
    }
}

#[test]
fn default_errors_summarize_each_rejected_statement_and_missing_condition() {
    let dir = FixtureDir::new();
    let output = dir.run(
        &[
            "-strict",
            "-e",
            "have a R = 2\na = 3\nforall x R => 1 / x = 1 / x\na + 1 = 3",
        ],
        None,
    );
    let json = batch(&output, 1, false);
    assert_session_state(&json, false);
    let errors = field(&json, "errors").as_array().unwrap();
    assert_eq!(errors.len(), 2);
    assert_eq!(
        field(&errors[0], "statement_index"),
        &JsonValue::Number(1.0)
    );
    assert_eq!(
        field(&errors[1], "statement_index"),
        &JsonValue::Number(2.0)
    );
    assert_eq!(field(&errors[1], "expression").as_str(), Ok("(1 / x)"));
    assert_eq!(field(&errors[1], "obligation").as_str(), Ok("x != 0"));
    let statements = field(&json, "statement_results").as_array().unwrap();
    assert_eq!(
        field(&statements[3], "statement_result").as_str(),
        Ok("accepted")
    );
    assert_eq!(
        statements[1].as_object().unwrap().keys_in_order(),
        vec!["statement_result", "statement"]
    );
    let text = json.stringify();
    assert!(!text.contains("\"verification\""), "{text}");
    assert!(!text.contains("\"diagnostic\""), "{text}");
    assert!(
        text.len() < 2500,
        "feedback unexpectedly large: {}",
        text.len()
    );
}

#[test]
fn lean_rejects_malformed_source_without_emitting_a_partial_artifact() {
    let dir = FixtureDir::new();
    fs::write(
        dir.0.join("malformed.lit"),
        "have a R\nhave fn incomplete_function(x R) R = x +\n",
    )
    .unwrap();
    let output = dir.run(&["-lean", "-strict", "-f", "malformed.lit"], None);
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(error.contains("phase=verify"), "{error}");
    assert!(
        error.contains("expected object at line 2 in malformed.lit"),
        "{error}"
    );
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
            for (code, exit, succeeded) in [("have a R = 1", 0, true), ("have", 1, false)] {
                let output = dir.run(&["-lang", language.as_str(), command, code], None);
                assert_eq!(output.status.code(), Some(exit), "{output:?}");
                assert!(output.stderr.is_empty(), "{output:?}");
                let json = JsonValue::parse(std::str::from_utf8(&output.stdout).unwrap()).unwrap();
                assert_eq!(
                    field(&json, &key("artifact_result")).as_str().ok(),
                    Some(if succeeded { "success" } else { "failure" })
                );
                assert_eq!(field(&json, &key("format")).as_str().unwrap(), format);
                assert_eq!(field(&json, &key("target")).as_str().unwrap(), "eval");
                assert_eq!(
                    field(&json, &key("language")).as_str().unwrap(),
                    language.as_str()
                );
                assert_eq!(field(&json, &key("path")), &JsonValue::Null);
                assert_eq!(field(&json, &key("output_path")), &JsonValue::Null);
                if succeeded {
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
                assert_eq!(
                    field(&json, &key("artifact_result")).as_str().ok(),
                    Some("failure")
                );
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
