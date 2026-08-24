use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

fn litex_binary() -> &'static str {
    env!("CARGO_BIN_EXE_litex")
}

fn run_litex(args: &[&str]) -> (bool, String, String) {
    let output = Command::new(litex_binary())
        .args(args)
        .output()
        .expect("run Litex CLI");
    (
        output.status.success(),
        String::from_utf8(output.stdout).expect("Litex stdout is UTF-8"),
        String::from_utf8(output.stderr).expect("Litex stderr is UTF-8"),
    )
}

#[test]
fn trace_pipeline_shows_the_major_rust_path_without_changing_normal_output() {
    let (normal_ok, normal_stdout, normal_stderr) = run_litex(&["-e", "1 + 1 = 2"]);
    assert!(normal_ok, "{normal_stderr}");

    let (trace_ok, trace_stdout, trace_stderr) = run_litex(&["-trace-pipeline", "-e", "1 + 1 = 2"]);
    assert!(trace_ok, "{trace_stderr}");
    let (ordinary_output, trace) = trace_stdout
        .split_once("Rust pipeline trace:\n")
        .expect("pipeline trace follows ordinary output");
    assert_eq!(ordinary_output.trim_end(), normal_stdout.trim_end());

    let ordered_functions = [
        "main — src/main.rs",
        "cli::run_cli — src/cli/command_dispatch.rs",
        "pipeline::run — src/pipeline/run.rs",
        "pipeline::execute_source — src/pipeline/source_execution.rs",
        "Tokenizer::parse_blocks — src/parse/tokenizer.rs",
        "Runtime::parse_statement — src/parse/statement_parsing.rs",
        "pipeline::execute_top_level_statement — src/pipeline/top_level_statement_execution.rs",
        "Runtime::execute_statement — src/execute/statement_execution.rs",
        "Runtime::verify_fact_or_error — src/verify/dispatch.rs",
        "Runtime::finish_statement_execution — src/execute/statement_execution.rs",
        "pipeline::render_run_output — src/pipeline/output_rendering.rs",
    ];
    let mut previous = 0;
    for function in ordered_functions {
        let position = trace
            .find(function)
            .unwrap_or_else(|| panic!("missing {function} in:\n{trace}"));
        assert!(position >= previous, "{function} is out of order:\n{trace}");
        previous = position;
    }
    assert!(trace.contains("Lean compiler: not executed"));
}

#[test]
fn runner_exposes_the_pipeline_trace_as_structured_json() {
    let (ok, stdout, stderr) = run_litex(&["-trace-pipeline", "-runner", "-e", "1 + 1 = 2"]);
    assert!(ok, "{stderr}");
    assert!(stdout.contains("\"pipeline_trace\": {"), "{stdout}");
    assert!(stdout.contains("\"function\": \"main\""), "{stdout}");
    assert!(
        stdout.contains("\"function\": \"runner::run_runner\""),
        "{stdout}"
    );
    assert!(
        stdout.contains("\"lean_compiler_executed\": false"),
        "{stdout}"
    );
}

#[test]
fn lean_file_compilation_is_marked_as_executed() {
    let fixture = TraceFixture::new();
    let input = fixture.root.join("input.lit");
    let output = fixture.root.join("output.lean");
    fs::write(&input, "1 + 1 = 2\n").expect("write trace input");

    let input = input.to_str().expect("temporary input path is UTF-8");
    let output = output.to_str().expect("temporary output path is UTF-8");
    let (ok, stdout, stderr) =
        run_litex(&["-trace-pipeline", "-isolated", "-f", input, "-lean", output]);

    assert!(ok, "{stderr}\n{stdout}");
    assert!(stdout.contains("Lean compiler: executed"), "{stdout}");
    assert!(
        stdout.contains("compile_litex_source_to_lean_source"),
        "{stdout}"
    );
    assert!(PathBuf::from(output).is_file());
}

struct TraceFixture {
    root: PathBuf,
}

impl TraceFixture {
    fn new() -> Self {
        static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
        let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "litex-execution-pipeline-trace-{}-{id}",
            std::process::id()
        ));
        fs::create_dir_all(&root).expect("create trace fixture");
        Self { root }
    }
}

impl Drop for TraceFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}
