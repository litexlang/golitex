use super::{
    run_isolated_repl_with_runtime_and_readers, run_latex_repl_loop_with_readers,
    run_repl_loop_with_readers_and_mode, ReplOutputMode,
};
use crate::pipeline::{run_file_with_project_context, run_source_code};
use crate::prelude::OutputLanguage;
use crate::runtime::{OutputStyle, Runtime};
use std::fs;
use std::io::{self, BufRead, Cursor, Write};

fn run_repl_loop_with_readers(
    version_banner: &str,
    output_style: OutputStyle,
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
) -> io::Result<()> {
    run_repl_loop_with_readers_and_mode(
        version_banner,
        output_style,
        false,
        OutputLanguage::English,
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
        OutputStyle::Normal,
        &mut stdin_reader,
        &mut stdout_writer,
    )
    .unwrap();

    let output_text = String::from_utf8(stdout_writer).unwrap();
    assert!(output_text.contains("... "));
    assert!(output_text.contains("\"outcome\": \"success\""));
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
        OutputStyle::Normal,
        &mut stdin_reader,
        &mut stdout_writer,
    )
    .unwrap();

    let output_text = String::from_utf8(stdout_writer).unwrap();
    assert!(output_text.contains("\"outcome\": \"success\""));
}

#[test]
fn repl_startup_shows_version_and_upgrade_hint() {
    let input = b"";
    let mut stdin_reader = Cursor::new(input.as_slice());
    let mut stdout_writer = Vec::new();

    run_repl_loop_with_readers(
        "test-version",
        OutputStyle::Normal,
        &mut stdin_reader,
        &mut stdout_writer,
    )
    .unwrap();

    let output_text = String::from_utf8(stdout_writer).unwrap();
    assert!(output_text.contains("Litex version test-version"));
    assert!(output_text.contains("litex -upgrade"));
}

#[test]
fn latex_repl_outputs_latex_for_single_line_input() {
    let input = b"1 = 1\n";
    let mut stdin_reader = Cursor::new(input.as_slice());
    let mut stdout_writer = Vec::new();

    run_latex_repl_loop_with_readers("test", &mut stdin_reader, &mut stdout_writer).unwrap();

    let output_text = String::from_utf8(stdout_writer).unwrap();
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

    let mut runtime = Runtime::new();
    let (_, file_error) = run_file_with_project_context(
        file.to_str().expect("file path is UTF-8"),
        &mut runtime,
        true,
    );
    assert!(file_error.is_none(), "{file_error:?}");
    assert!(runtime.current_source_allows_inline_imports());

    let mut input = Cursor::new(b"from_file = 1\nhave from_repl R = 2\n".as_slice());
    let mut output = Vec::new();
    run_isolated_repl_with_runtime_and_readers("test", &mut runtime, &mut input, &mut output)
        .expect("continue isolated REPL");
    let output = String::from_utf8(output).expect("UTF-8 REPL output");
    assert!(output.contains("Continuing isolated REPL."));
    assert!(output.contains("\"outcome\": \"success\""), "{output}");

    let (_, continuation_error) = run_source_code("from_repl = 2", &mut runtime);
    assert!(continuation_error.is_none(), "{continuation_error:?}");

    let _ = fs::remove_dir_all(&directory);
}
