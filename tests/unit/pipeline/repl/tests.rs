use super::{
    initialize_isolated_repl_runtime, run_isolated_repl_with_runtime_and_readers,
    run_latex_repl_loop_with_readers, run_repl_loop_with_readers_and_mode, ReplOutputMode,
};
use crate::pipeline::execute_isolated_file_in_runtime;
use crate::prelude::{OutputDetail, OutputLanguage};
use crate::runtime::{RuntimeOptions, Runtime, SummaryOption, VerifyStrictnessPolicy};
use crate::test_support::execute_source;
use std::fs;
use std::io::{self, BufRead, Cursor, Write};

fn run_repl_loop_with_readers(
    version_banner: &str,
    output_detail: OutputDetail,
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
) -> io::Result<()> {
    run_repl_loop_with_readers_and_mode(
        version_banner,
        RuntimeOptions::new(
            VerifyStrictnessPolicy::Ordinary,
            output_detail,
            OutputLanguage::English,
            SummaryOption::None,
        ),
        stdin_reader,
        stdout_writer,
        ReplOutputMode::Json,
    )
}

#[test]
fn repl_accepts_multiline_block_after_blank_line() {
    let input = b"sketch:\n    1 = 1\n    2 = 2\n\n";
    let mut stdin_reader = Cursor::new(input.as_slice());
    let mut stdout_writer = Vec::new();

    run_repl_loop_with_readers(
        "test",
        OutputDetail::Normal,
        &mut stdin_reader,
        &mut stdout_writer,
    )
    .unwrap();

    let output_text = String::from_utf8(stdout_writer).unwrap();
    assert!(output_text.contains("\"event\":\"prompt\""));
    assert!(output_text.contains("\"content\":\"... \""));
    assert!(output_text.contains("\"event\":\"result\""));
    assert!(output_text.contains("\"outcome\":\"success\""));
    assert!(!output_text.contains("block header missing body"));
    assert!(!output_text.contains("unexpected indent"));
}

#[test]
fn repl_still_executes_single_line_input_immediately() {
    let input = b"1 = 1\n";
    let mut stdin_reader = Cursor::new(input.as_slice());
    let mut stdout_writer = Vec::new();

    run_repl_loop_with_readers(
        "test",
        OutputDetail::Normal,
        &mut stdin_reader,
        &mut stdout_writer,
    )
    .unwrap();

    let output_text = String::from_utf8(stdout_writer).unwrap();
    assert!(output_text.contains("\"kind\":\"stream\""));
    assert!(output_text.contains("\"stream\":\"repl\""));
    assert!(output_text.contains("\"outcome\":\"success\""));
}

#[test]
fn isolated_repl_uses_the_explicit_repl_source_label() {
    let mut runtime = Runtime::default();
    initialize_isolated_repl_runtime(&mut runtime);

    assert_eq!(runtime.current_file_path_rc().as_ref(), "repl");
}

#[test]
fn repl_routes_import_to_its_interactive_module_manifest_before_source_parsing() {
    let directory =
        std::env::temp_dir().join(format!("litex-terminal-import-repl-{}", std::process::id()));
    let _ = fs::remove_dir_all(&directory);
    let module = directory.join("library");
    fs::create_dir_all(&module).expect("create terminal import module");
    fs::write(
        module.join("litex.config"),
        "[hierarchy]\nmodule\n\n[export]\nmain = \"./main.lit\"\n",
    )
    .expect("write module config");
    fs::write(module.join("main.lit"), "have value R = 7\n").expect("write module source");

    let command = format!(
        "import \"{}\" as Library\nLibrary::main::value = 7\n",
        module.to_string_lossy()
    );
    let mut stdin_reader = Cursor::new(command.into_bytes());
    let mut stdout_writer = Vec::new();
    run_repl_loop_with_readers(
        "test",
        OutputDetail::Normal,
        &mut stdin_reader,
        &mut stdout_writer,
    )
    .unwrap();

    let output = String::from_utf8(stdout_writer).expect("UTF-8 REPL output");
    assert!(output.contains("\"event\":\"result\""), "{output}");
    assert!(output.contains("\"type\":\"terminal import\""), "{output}");
    assert!(output.contains("\"outcome\":\"success\""), "{output}");
    assert!(
        !output.contains("not a Litex statement"),
        "REPL import must bypass source parsing: {output}"
    );

    let _ = fs::remove_dir_all(&directory);
}

#[test]
fn repl_startup_shows_version_without_a_retired_upgrade_command() {
    let input = b"";
    let mut stdin_reader = Cursor::new(input.as_slice());
    let mut stdout_writer = Vec::new();

    run_repl_loop_with_readers(
        "test-version",
        OutputDetail::Normal,
        &mut stdin_reader,
        &mut stdout_writer,
    )
    .unwrap();

    let output_text = String::from_utf8(stdout_writer).unwrap();
    assert!(output_text.contains("\"event\":\"ready\""));
    assert!(output_text.contains("\"version\":\"test-version\""));
    assert!(!output_text.contains("litex -upgrade"));
}

#[test]
fn latex_repl_outputs_latex_for_single_line_input() {
    let input = b"1 = 1\n";
    let mut stdin_reader = Cursor::new(input.as_slice());
    let mut stdout_writer = Vec::new();

    run_latex_repl_loop_with_readers("test", &mut stdin_reader, &mut stdout_writer).unwrap();

    let output_text = String::from_utf8(stdout_writer).unwrap();
    assert!(output_text.contains("\"stream\":\"latex_repl\""));
    assert!(output_text.contains("\"event\":\"result\""));
    assert!(output_text.contains(r"\["));
    assert!(output_text.contains(r"\]"));
    assert!(output_text.contains("1 = 1"));
    assert!(!output_text.contains(r"\documentclass{article}"));
    assert!(!output_text.contains(r"\paragraph{Stmt 1}"));
    assert!(!output_text.contains(r#""result": "success""#));
}

#[test]
fn isolated_file_continues_in_the_same_repl_runtime() {
    let directory =
        std::env::temp_dir().join(format!("litex-isolated-file-repl-{}", std::process::id()));
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir_all(&directory).expect("create isolated file directory");
    let file = directory.join("session.lit");
    fs::write(&file, "have from_file R = 1\n").expect("write isolated source file");

    let mut runtime = Runtime::default();
    let (_, file_error) =
        execute_isolated_file_in_runtime(file.to_str().expect("file path is UTF-8"), &mut runtime);
    assert!(file_error.is_none(), "{file_error:?}");
    let mut input = Cursor::new(b"from_file = 1\nhave from_repl R = 2\n".as_slice());
    let mut output = Vec::new();
    run_isolated_repl_with_runtime_and_readers("test", &mut runtime, &mut input, &mut output)
        .expect("continue isolated REPL");
    let output = String::from_utf8(output).expect("UTF-8 REPL output");
    assert!(output.contains("\"mode\":\"continued\""));
    assert!(output.contains("\"outcome\":\"success\""), "{output}");

    let (_, continuation_error) = execute_source("from_repl = 2", &mut runtime);
    assert!(continuation_error.is_none(), "{continuation_error:?}");

    let _ = fs::remove_dir_all(&directory);
}

#[test]
fn isolated_file_rejects_inline_import_before_repl_continuation() {
    let directory =
        std::env::temp_dir().join(format!("litex-isolated-file-import-{}", std::process::id()));
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir_all(&directory).expect("create isolated file directory");
    let file = directory.join("inline-import.lit");
    fs::write(&file, "import std basics\n").expect("write isolated source file");

    let mut runtime = Runtime::default();
    let (results, error) =
        execute_isolated_file_in_runtime(file.to_str().expect("file path is UTF-8"), &mut runtime);
    assert!(results.is_empty());
    let error = error.expect("-isolated -f must reject inline import");
    assert!(
        error
            .trace_message()
            .contains("`import` is a terminal command, not a Litex statement"),
        "{}",
        error.trace_message()
    );

    let _ = fs::remove_dir_all(&directory);
}
