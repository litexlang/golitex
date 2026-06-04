use crate::prelude::*;
use crate::to_latex::to_latex;
use std::io::{self, BufRead, Write};

#[derive(Clone, Copy)]
enum ReplOutputMode {
    Json,
    Latex,
}

pub fn run_repl(version: &str) {
    return run_repl_with_detail_output(version, false);
}

pub fn run_repl_with_detail_output(version: &str, detail_output: bool) {
    return run_repl_loop_internal(version, detail_output, false);
}

pub fn run_repl_with_detail_output_and_strict(
    version: &str,
    detail_output: bool,
    strict_mode: bool,
) {
    return run_repl_loop_internal(version, detail_output, strict_mode);
}

pub fn run_latex_repl(version: &str) {
    return run_latex_repl_loop_internal(version);
}

fn run_repl_loop_internal(version_banner: &str, detail_output: bool, strict_mode: bool) {
    let stdin_handle = io::stdin();
    let stdout_handle = io::stdout();
    let mut stdin_locked = stdin_handle.lock();
    let mut stdout_locked = stdout_handle.lock();
    let result = if strict_mode {
        run_repl_loop_with_readers_and_strict(
            version_banner,
            detail_output,
            true,
            &mut stdin_locked,
            &mut stdout_locked,
        )
    } else {
        run_repl_loop_with_readers(
            version_banner,
            detail_output,
            &mut stdin_locked,
            &mut stdout_locked,
        )
    };
    match result {
        Ok(()) => {}
        Err(write_error) => {
            eprintln!("repl output error: {}", write_error);
        }
    }
}

fn run_latex_repl_loop_internal(version_banner: &str) {
    let stdin_handle = io::stdin();
    let stdout_handle = io::stdout();
    let mut stdin_locked = stdin_handle.lock();
    let mut stdout_locked = stdout_handle.lock();
    match run_latex_repl_loop_with_readers(version_banner, &mut stdin_locked, &mut stdout_locked) {
        Ok(()) => {}
        Err(write_error) => {
            eprintln!("repl output error: {}", write_error);
        }
    }
}

fn run_repl_loop_with_readers(
    version_banner: &str,
    detail_output: bool,
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
) -> io::Result<()> {
    run_repl_loop_with_readers_and_strict(
        version_banner,
        detail_output,
        false,
        stdin_reader,
        stdout_writer,
    )
}

fn run_repl_loop_with_readers_and_strict(
    version_banner: &str,
    detail_output: bool,
    strict_mode: bool,
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
) -> io::Result<()> {
    run_repl_loop_with_readers_and_mode(
        version_banner,
        detail_output,
        strict_mode,
        stdin_reader,
        stdout_writer,
        ReplOutputMode::Json,
    )
}

fn run_latex_repl_loop_with_readers(
    version_banner: &str,
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
) -> io::Result<()> {
    run_repl_loop_with_readers_and_mode(
        version_banner,
        false,
        false,
        stdin_reader,
        stdout_writer,
        ReplOutputMode::Latex,
    )
}

fn run_repl_loop_with_readers_and_mode(
    version_banner: &str,
    detail_output: bool,
    strict_mode: bool,
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
    output_mode: ReplOutputMode,
) -> io::Result<()> {
    writeln!(stdout_writer, "Litex version {}", version_banner)?;
    writeln!(
        stdout_writer,
        "Upgrade Litex? Run `litex -upgrade` for platform instructions."
    )?;
    writeln!(stdout_writer, "Copyright (C) 2024-2026 Jiachen Shen")?;
    writeln!(stdout_writer, "website: https://litexlang.com")?;
    writeln!(
        stdout_writer,
        "github: https://github.com/litexlang/golitex"
    )?;
    writeln!(stdout_writer, "Ctrl+D to exit.")?;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("repl");
    runtime.detail_output = detail_output;
    runtime.strict_mode = strict_mode;

    let mut line_buffer = String::new();
    let mut source_buffer = String::new();
    let mut collecting_multiline = false;

    loop {
        if collecting_multiline {
            write!(stdout_writer, "... ")?;
        } else {
            write!(stdout_writer, ">>> ")?;
        }
        stdout_writer.flush()?;

        line_buffer.clear();
        let bytes_read = match stdin_reader.read_line(&mut line_buffer) {
            Ok(byte_count) => byte_count,
            Err(read_error) => {
                writeln!(stdout_writer, "stdin read error: {}", read_error)?;
                break;
            }
        };

        if bytes_read == 0 {
            let output_text =
                run_repl_source_if_not_empty(&source_buffer, &mut runtime, output_mode);
            if !output_text.is_empty() {
                writeln!(stdout_writer, "{}", output_text)?;
            }
            writeln!(stdout_writer)?;
            break;
        }

        let trimmed_line = line_buffer.trim();
        if trimmed_line.is_empty() {
            if collecting_multiline {
                let output_text =
                    run_repl_source_if_not_empty(&source_buffer, &mut runtime, output_mode);
                if !output_text.is_empty() {
                    writeln!(stdout_writer, "{}", output_text)?;
                }
                source_buffer.clear();
                collecting_multiline = false;
            }
            continue;
        }

        if collecting_multiline {
            source_buffer.push_str(&line_buffer);
            continue;
        }

        if repl_line_starts_block(trimmed_line) {
            source_buffer.push_str(trimmed_line);
            source_buffer.push('\n');
            collecting_multiline = true;
            continue;
        }

        let output_text = run_repl_source_if_not_empty(trimmed_line, &mut runtime, output_mode);
        if !output_text.is_empty() {
            writeln!(stdout_writer, "{}", output_text)?;
        }
    }

    Ok(())
}

fn run_repl_source_if_not_empty(
    source: &str,
    runtime: &mut Runtime,
    output_mode: ReplOutputMode,
) -> String {
    if source.trim().is_empty() {
        return String::new();
    }

    let normalized_source = remove_windows_carriage_return(source);
    match output_mode {
        ReplOutputMode::Json => {
            let (stmt_results, runtime_error) =
                run_source_code(normalized_source.as_str(), runtime);
            let (_, output_text) =
                render_run_source_code_output(runtime, &stmt_results, &runtime_error, true);
            output_text.trim().to_string()
        }
        ReplOutputMode::Latex => match to_latex(normalized_source.as_str(), runtime) {
            Ok(output_text) => output_text.trim().to_string(),
            Err(error) => display_runtime_error_json(runtime, &error, true)
                .trim()
                .to_string(),
        },
    }
}

fn repl_line_starts_block(line: &str) -> bool {
    line.trim_end().ends_with(':')
}

#[cfg(test)]
mod tests {
    use super::{run_latex_repl_loop_with_readers, run_repl_loop_with_readers};
    use std::io::Cursor;

    #[test]
    fn repl_accepts_multiline_block_after_blank_line() {
        let input = b"prove:\n    1 = 1\n    2 = 2\n\n";
        let mut stdin_reader = Cursor::new(input.as_slice());
        let mut stdout_writer = Vec::new();

        run_repl_loop_with_readers("test", false, &mut stdin_reader, &mut stdout_writer).unwrap();

        let output_text = String::from_utf8(stdout_writer).unwrap();
        assert!(output_text.contains("... "));
        assert!(output_text.contains("\"result\": \"success\""));
        assert!(!output_text.contains("block header missing body"));
        assert!(!output_text.contains("unexpected indent"));
    }

    #[test]
    fn repl_still_executes_single_line_input_immediately() {
        let input = b"1 = 1\n";
        let mut stdin_reader = Cursor::new(input.as_slice());
        let mut stdout_writer = Vec::new();

        run_repl_loop_with_readers("test", false, &mut stdin_reader, &mut stdout_writer).unwrap();

        let output_text = String::from_utf8(stdout_writer).unwrap();
        assert!(output_text.contains("\"result\": \"success\""));
    }

    #[test]
    fn repl_startup_shows_version_and_upgrade_hint() {
        let input = b"";
        let mut stdin_reader = Cursor::new(input.as_slice());
        let mut stdout_writer = Vec::new();

        run_repl_loop_with_readers("test-version", false, &mut stdin_reader, &mut stdout_writer)
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
}
