use crate::pipeline::display::{display_runtime_error_json, display_stmt_exec_result_json};
use crate::pipeline::render_run_source_code_output;
use crate::pipeline::run_source_code;
use crate::pipeline::run_stmt_at_global_env;
use crate::prelude::*;
use std::io::{self, BufRead, Write};

pub fn run_repl(version: &str) {
    return run_repl_loop_internal(version);
}

fn run_repl_loop_internal(version_banner: &str) {
    let stdin_handle = io::stdin();
    let stdout_handle = io::stdout();
    let mut stdin_locked = stdin_handle.lock();
    let mut stdout_locked = stdout_handle.lock();
    match run_repl_loop_with_readers(version_banner, &mut stdin_locked, &mut stdout_locked) {
        Ok(()) => {}
        Err(write_error) => {
            eprintln!("repl output error: {}", write_error);
        }
    }
}

fn run_repl_loop_with_readers<R, W>(
    version_banner: &str,
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
    writeln!(stdout_writer, "Ctrl+D to exit.")?;

    let mut runtime = Runtime::new();

    let (builtin_stmt_results, builtin_error) =
        run_source_code(builtin_code().as_str(), &mut runtime);
    let (ok, msg) = render_run_source_code_output(&runtime, &builtin_stmt_results, &builtin_error);
    if !ok {
        eprintln!("builtin code execution failed: {}", msg);
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "builtin code execution failed",
        ));
    }
    runtime.new_file_path_new_env_new_name_scope("repl");

    let mut line_buffer = String::new();

    loop {
        write!(stdout_writer, ">>> ")?;
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
            writeln!(stdout_writer)?;
            break;
        }

        let trimmed_line = line_buffer.trim();
        if trimmed_line.is_empty() {
            continue;
        }

        let normalized_source = remove_windows_carriage_return(trimmed_line);

        let blocks = match TokenBlock::parse_blocks(
            normalized_source.as_str(),
            runtime.module_manager.current_file_path_rc(),
        ) {
            Ok(parsed_blocks) => parsed_blocks,
            Err(parse_block_error) => {
                let error_string = display_runtime_error_json(&runtime, &parse_block_error);
                writeln!(stdout_writer)?;
                writeln!(stdout_writer, "{}", error_string)?;
                writeln!(stdout_writer)?;
                break;
            }
        };

        let mut output_chunk = String::new();
        for mut block in blocks {
            let stmt: Stmt = match runtime.parse_stmt(&mut block) {
                Ok(statement) => statement,
                Err(parse_stmt_error) => {
                    let message = display_runtime_error_json(&runtime, &parse_stmt_error);
                    output_chunk.push_str(&format!("\n{}\n", message));
                    break;
                }
            };

            let exec_result = match run_stmt_at_global_env(&stmt, &mut runtime) {
                Ok(result) => result,
                Err(exec_error) => {
                    let message = display_runtime_error_json(&runtime, &exec_error);
                    output_chunk.push_str(&format!("\n{}\n", message));
                    break;
                }
            };

            output_chunk.push('\n');
            output_chunk.push_str(display_stmt_exec_result_json(&runtime, &exec_result).as_str());
            output_chunk.push('\n');
        }

        let trimmed_output = output_chunk.trim();
        if !trimmed_output.is_empty() {
            writeln!(stdout_writer, "{}", trimmed_output)?;
        }
    }

    Ok(())
}
