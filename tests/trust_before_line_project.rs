use litex::prelude::*;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

#[test]
fn trust_before_line_scopes_registered_run_to_the_selected_file() {
    run_with_large_stack(
        "trust_before_line_scopes_registered_run_to_the_selected_file",
        || {
            let fixture = Fixture::new("registered-scope");
            let root = fixture.path("root");
            let dependency = fixture.path("dependency");
            let dependency_source = dependency.join("main.lit");
            let preceding_source = root.join("before.lit");
            let target_source = root.join("target.lit");

            write_file(
                &dependency.join("litex.config"),
                r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
            );
            write_file(&dependency_source, "have imported_value R = 1\n1 = 0\n");
            write_file(
                &root.join("litex.config"),
                r#"[hierarchy]
module

[import]
Dependency = "../dependency"

[export]
before = "./before.lit"
target = "./target.lit"
"#,
            );
            write_file(&preceding_source, "have preceding_value R = 1\n1 = 0\n");
            write_file(&target_source, "have target_prefix_value R = 1\n\n1 = 1\n");

            let target_path = path_string(&target_source);
            let mut runtime = Runtime::new();
            let (stmt_results, runtime_error) = run_file_with_project_context_and_trusted_prefix(
                target_path.as_str(),
                &mut runtime,
                false,
                Some(3),
            );

            assert!(
                runtime_error.is_none(),
                "registered trusted-prefix fixture failed: {runtime_error:?}"
            );
            let report = runtime
                .trusted_prefix_report
                .as_ref()
                .expect("the selected file should produce a trusted-prefix report");
            assert_eq!(report.file, target_path);
            assert_eq!(report.before_line, 3);
            assert_eq!(report.trusted_top_level_statements, 1);
            assert_eq!(report.first_verified_statement_line, 3);

            let dependency_path = path_string(&dependency_source);
            let preceding_path = path_string(&preceding_source);
            let imported_results = results_for_file(&stmt_results, dependency_path.as_str());
            let preceding_results = results_for_file(&stmt_results, preceding_path.as_str());
            let target_results = results_for_file(&stmt_results, target_path.as_str());

            assert_eq!(imported_results.len(), 2);
            assert_eq!(preceding_results.len(), 2);
            assert_eq!(target_results.len(), 2);
            for result in imported_results
                .iter()
                .chain(preceding_results.iter())
                .copied()
            {
                let trace = result
                    .execution_trace()
                    .expect("successful project-prefix statements should have a trace");
                assert_eq!(
                    trace.verification_status, None,
                    "ordinary project imports and exports must retain their old status"
                );
                assert!(
                    !trace.trust_summary.contains_kind("cli_trusted_prefix"),
                    "cutoff provenance must not leak into preceding files"
                );
            }

            let prefix_trace = target_results[0]
                .execution_trace()
                .expect("trusted target statement should have a trace");
            assert_eq!(
                prefix_trace.verification_status.as_deref(),
                Some("trusted_prefix")
            );
            assert!(prefix_trace
                .trust_summary
                .contains_kind("cli_trusted_prefix"));

            let suffix_trace = target_results[1]
                .execution_trace()
                .expect("verified target statement should have a trace");
            assert_eq!(
                suffix_trace.verification_status.as_deref(),
                Some("verified")
            );
            assert!(!suffix_trace
                .trust_summary
                .contains_kind("cli_trusted_prefix"));
            assert!(runtime
                .unverified_imports
                .iter()
                .any(|entry| entry.kind == "project_import"));
            assert!(runtime
                .unverified_imports
                .iter()
                .any(|entry| entry.kind == "project_export"));
        },
    );
}

#[test]
fn trust_before_line_flagless_registered_run_keeps_verifying_the_file() {
    run_with_large_stack(
        "trust_before_line_flagless_registered_run_keeps_verifying_the_file",
        || {
            let fixture = Fixture::new("flagless");
            let root = fixture.path("root");
            let target_source = root.join("target.lit");
            write_file(
                &root.join("litex.config"),
                r#"[hierarchy]
module

[export]
target = "./target.lit"
"#,
            );
            write_file(&target_source, "1 = 0\n\n1 = 1\n");

            let mut runtime = Runtime::new();
            let (stmt_results, runtime_error) = run_file_with_project_context(
                path_string(&target_source).as_str(),
                &mut runtime,
                false,
            );
            let (_, output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                runtime_error.is_some(),
                "without the flag, the invalid first proof must still be verified"
            );
            assert!(runtime.trusted_prefix_report.is_none());
            assert!(runtime.trusted_prefix_setup_error.is_none());
            assert!(!output.contains("trusted_prefix"));
            assert!(!output.contains("cli_trusted_prefix"));
            assert!(!output.contains("\"verification_status\""));
        },
    );
}

#[test]
fn trust_before_line_rejects_a_registered_non_header_before_running_the_prefix() {
    let fixture = Fixture::new("registered-invalid-boundary");
    let root = fixture.path("root");
    let preceding_source = root.join("before.lit");
    let target_source = root.join("target.lit");
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[export]
before = "./before.lit"
target = "./target.lit"
"#,
    );
    write_file(&preceding_source, "7 = 8\n");
    write_file(&target_source, "1 = 1\n\n2 = 2\n");

    let mut runtime = Runtime::new();
    let (stmt_results, runtime_error) = run_file_with_project_context_and_trusted_prefix(
        path_string(&target_source).as_str(),
        &mut runtime,
        false,
        Some(2),
    );

    assert!(stmt_results.is_empty());
    assert!(runtime_error.is_some());
    assert!(runtime.trusted_prefix_report.is_none());
    assert!(runtime.trusted_prefix_setup_error.is_some());

    let (probe_results, probe_error) = run_source_code("7 = 8", &mut runtime);
    assert!(
        probe_results.is_empty() && probe_error.is_some(),
        "an invalid boundary must be rejected before preceding exports write facts"
    );
}

#[test]
fn trust_before_line_cli_emits_boundary_first_and_summary_last_once() {
    let fixture = Fixture::new("cli-output");
    let root = fixture.path("root");
    let target_source = root.join("target.lit");
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[export]
target = "./target.lit"
"#,
    );
    write_file(
        &target_source,
        "have target_prefix_value R = 1\n\ntarget_prefix_value = 1\n",
    );

    let target_path = path_string(&target_source);
    let cutoff_output = Command::new(litex_binary())
        .args([
            "-compact",
            "-summarize",
            "-f",
            target_path.as_str(),
            "-trust-before-line",
            "3",
        ])
        .output()
        .expect("run release Litex CLI with a trusted prefix");
    assert!(
        cutoff_output.status.success(),
        "trusted-prefix CLI failed:\n{}",
        String::from_utf8_lossy(&cutoff_output.stderr)
    );
    let cutoff_stdout =
        String::from_utf8(cutoff_output.stdout).expect("Litex output should be UTF-8");
    let cutoff_objects = top_level_json_objects(cutoff_stdout.as_str());

    assert!(
        cutoff_objects
            .first()
            .is_some_and(|value| value.contains("\"type\": \"trusted_prefix\"")),
        "the boundary report must be the first JSON object:\n{cutoff_stdout}"
    );
    assert_eq!(
        cutoff_objects
            .iter()
            .filter(|value| value.contains("\"type\": \"trusted_prefix\""))
            .count(),
        1,
        "the boundary report must be emitted once:\n{cutoff_stdout}"
    );
    assert_eq!(
        cutoff_objects
            .iter()
            .filter(|value| value.contains("\"output_type\": \"run summary\""))
            .count(),
        1,
        "the automatic summary must be emitted once:\n{cutoff_stdout}"
    );
    let summary = cutoff_objects
        .last()
        .expect("trusted-prefix output should contain a summary");
    assert!(
        summary.contains("\"output_type\": \"run summary\""),
        "the summary must be the final JSON object:\n{cutoff_stdout}"
    );
    assert!(summary.contains("\"execution_ok\": true"));
    assert!(summary.contains("\"verification_status\": \"trusted_prefix\""));

    let flagless_output = Command::new(litex_binary())
        .args(["-compact", "-f", target_path.as_str()])
        .output()
        .expect("run release Litex CLI without a trusted prefix");
    assert!(
        flagless_output.status.success(),
        "flagless CLI failed:\n{}",
        String::from_utf8_lossy(&flagless_output.stderr)
    );
    let flagless_stdout =
        String::from_utf8(flagless_output.stdout).expect("Litex output should be UTF-8");
    assert!(!flagless_stdout.contains("\"type\": \"trusted_prefix\""));
    assert!(!flagless_stdout.contains("\"output_type\": \"run summary\""));
    assert!(!flagless_stdout.contains("\"verification_status\""));
}

#[test]
fn trust_before_line_cli_reports_the_boundary_when_a_preceding_export_fails() {
    let fixture = Fixture::new("cli-prefix-error");
    let root = fixture.path("root");
    let preceding_source = root.join("before.lit");
    let target_source = root.join("target.lit");
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[export]
before = "./before.lit"
target = "./target.lit"
"#,
    );
    write_file(
        &preceding_source,
        "have repeated_object R\nhave repeated_object R\n",
    );
    write_file(&target_source, "1 = 1\n");
    let target_path = path_string(&target_source);

    let output = Command::new(litex_binary())
        .args([
            "-compact",
            "-f",
            target_path.as_str(),
            "-trust-before-line",
            "1",
        ])
        .output()
        .expect("run trusted-prefix CLI with a failing preceding export");
    let stdout = String::from_utf8(output.stdout).expect("Litex output should be UTF-8");
    let objects = top_level_json_objects(stdout.as_str());
    assert!(
        objects
            .first()
            .is_some_and(|value| value.contains("\"type\": \"trusted_prefix\"")),
        "the preflight boundary must be the first event:\n{stdout}"
    );
    let summary = objects
        .last()
        .expect("a valid cutoff must end with a summary");
    assert!(summary.contains("\"output_type\": \"run summary\""));
    assert!(summary.contains("\"execution_ok\": false"));
    assert!(summary.contains("\"verification_status\": \"trusted_prefix\""));
}

#[test]
fn trust_before_line_isolated_cli_finishes_after_the_summary() {
    let fixture = Fixture::new("isolated-cli-output");
    let target_source = fixture.path("standalone.lit");
    write_file(&target_source, "1 = 2\n\n1 = 2\n");
    let target_path = path_string(&target_source);

    let output = Command::new(litex_binary())
        .args([
            "-compact",
            "-isolated",
            "-f",
            target_path.as_str(),
            "-trust-before-line",
            "3",
        ])
        .output()
        .expect("run isolated Litex CLI with a trusted prefix");
    assert!(
        output.status.success(),
        "isolated trusted-prefix CLI failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).expect("Litex output should be UTF-8");
    assert!(!stdout.contains("Continuing isolated REPL"));
    let objects = top_level_json_objects(stdout.as_str());
    assert!(
        objects
            .last()
            .is_some_and(|value| value.contains("\"output_type\": \"run summary\"")),
        "the summary must remain the final output event:\n{stdout}"
    );
}

#[test]
fn trust_before_line_cli_rejects_invalid_values_and_incompatible_commands() {
    let fixture = Fixture::new("cli-errors");
    let target_source = fixture.path("standalone.lit");
    write_file(&target_source, "1 = 1\n");
    let target_path = path_string(&target_source);

    let commands = vec![
        vec![
            "-isolated".to_string(),
            "-f".to_string(),
            target_path.clone(),
            "-trust-before-line".to_string(),
            "0".to_string(),
        ],
        vec![
            "-isolated".to_string(),
            "-f".to_string(),
            target_path.clone(),
            "-trust-before-line".to_string(),
            "-1".to_string(),
        ],
        vec![
            "-isolated".to_string(),
            "-f".to_string(),
            target_path.clone(),
            "-trust-before-line".to_string(),
            "abc".to_string(),
        ],
        vec![
            "-isolated".to_string(),
            "-f".to_string(),
            target_path.clone(),
            "-trust-before-line".to_string(),
        ],
        vec![
            "-strict".to_string(),
            "-isolated".to_string(),
            "-f".to_string(),
            target_path.clone(),
            "-trust-before-line".to_string(),
            "1".to_string(),
        ],
        vec![
            "-r".to_string(),
            fixture.path("unused").to_string_lossy().to_string(),
            "-trust-before-line".to_string(),
            "1".to_string(),
        ],
    ];

    for args in commands {
        let output = Command::new(litex_binary())
            .args(args.iter())
            .output()
            .expect("run Litex CLI error case");
        assert_eq!(
            output.status.code(),
            Some(2),
            "unexpected status for {args:?}"
        );
        let stderr = String::from_utf8(output.stderr).expect("Litex stderr should be UTF-8");
        assert!(
            stderr.contains("-trust-before-line"),
            "missing trusted-prefix diagnostic for {args:?}:\n{stderr}"
        );
    }
}

fn results_for_file<'a>(stmt_results: &'a [StmtResult], file: &str) -> Vec<&'a StmtResult> {
    stmt_results
        .iter()
        .filter(|result| result.line_file().1.as_ref() == file)
        .collect()
}

fn top_level_json_objects(output: &str) -> Vec<&str> {
    let mut objects = Vec::new();
    let mut start = None;
    let mut depth = 0usize;
    let mut inside_string = false;
    let mut escaped = false;
    for (index, byte) in output.bytes().enumerate() {
        if inside_string {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                inside_string = false;
            }
            continue;
        }
        if byte == b'"' {
            inside_string = true;
            continue;
        }
        if byte == b'{' {
            if depth == 0 {
                start = Some(index);
            }
            depth += 1;
        } else if byte == b'}' {
            assert!(depth > 0, "unexpected closing brace in CLI output");
            depth -= 1;
            if depth == 0 {
                let start = start.take().expect("top-level JSON object should start");
                objects.push(&output[start..=index]);
            }
        }
    }
    assert_eq!(depth, 0, "unterminated JSON object in CLI output");
    objects
}

fn litex_binary() -> PathBuf {
    if let Some(path) = option_env!("CARGO_BIN_EXE_litex") {
        return PathBuf::from(path);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/release/litex")
}

fn path_string(path: &Path) -> String {
    fs::canonicalize(path)
        .expect("fixture path should exist")
        .to_str()
        .expect("fixture path should be UTF-8")
        .to_string()
}

fn write_file(path: &Path, source: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("create fixture directory");
    }
    fs::write(path, source).expect("write fixture file");
}

fn run_with_large_stack(name: &str, test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name(name.to_string())
        .stack_size(8 * 1024 * 1024)
        .spawn(test)
        .expect("spawn trusted-prefix test")
        .join()
        .unwrap();
}

struct Fixture {
    root: PathBuf,
}

impl Fixture {
    fn new(name: &str) -> Self {
        static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
        let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "litex-trust-before-line-{name}-{}-{id}",
            std::process::id()
        ));
        if root.exists() {
            fs::remove_dir_all(&root).expect("remove stale fixture");
        }
        fs::create_dir_all(&root).expect("create fixture root");
        Fixture { root }
    }

    fn path(&self, name: &str) -> PathBuf {
        self.root.join(name)
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}
