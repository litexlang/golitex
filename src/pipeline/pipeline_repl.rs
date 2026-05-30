use crate::prelude::*;
use std::io::{self, BufRead, Write};

pub fn run_repl(version: &str) {
    return run_repl_with_detail_output(version, false);
}

pub fn run_repl_with_detail_output(version: &str, detail_output: bool) {
    return run_repl_loop_internal(version, detail_output);
}

fn run_repl_loop_internal(version_banner: &str, detail_output: bool) {
    let stdin_handle = io::stdin();
    let stdout_handle = io::stdout();
    let mut stdin_locked = stdin_handle.lock();
    let mut stdout_locked = stdout_handle.lock();
    match run_repl_loop_with_readers(
        version_banner,
        detail_output,
        &mut stdin_locked,
        &mut stdout_locked,
    ) {
        Ok(()) => {}
        Err(write_error) => {
            eprintln!("repl output error: {}", write_error);
        }
    }
}

fn run_repl_loop_with_readers<R, W>(
    version_banner: &str,
    detail_output: bool,
    stdin_reader: &mut R,
    stdout_writer: &mut W,
) -> io::Result<()>
where
    R: BufRead,
    W: Write,
{
    writeln!(stdout_writer, "Litex version {}", version_banner)?;
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
            let output_text = run_repl_source_if_not_empty(&source_buffer, &mut runtime);
            if !output_text.is_empty() {
                writeln!(stdout_writer, "{}", output_text)?;
            }
            writeln!(stdout_writer)?;
            break;
        }

        let trimmed_line = line_buffer.trim();
        if trimmed_line.is_empty() {
            if collecting_multiline {
                let output_text = run_repl_source_if_not_empty(&source_buffer, &mut runtime);
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

        let output_text = run_repl_source_if_not_empty(trimmed_line, &mut runtime);
        if !output_text.is_empty() {
            writeln!(stdout_writer, "{}", output_text)?;
        }
    }

    Ok(())
}

fn run_repl_source_if_not_empty(source: &str, runtime: &mut Runtime) -> String {
    if source.trim().is_empty() {
        return String::new();
    }

    let normalized_source = remove_windows_carriage_return(source);
    let (stmt_results, runtime_error) = run_source_code(normalized_source.as_str(), runtime);
    let (_, output_text) =
        render_run_source_code_output(runtime, &stmt_results, &runtime_error, true);
    output_text.trim().to_string()
}

fn repl_line_starts_block(line: &str) -> bool {
    line.trim_end().ends_with(':')
}

#[cfg(test)]
mod tests {
    use super::run_repl_loop_with_readers;
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
}
