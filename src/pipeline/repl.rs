use crate::latex_renderer::to_latex;
use crate::prelude::*;
use std::io::{self, BufRead, Write};

#[derive(Clone, Copy)]
enum ReplOutputMode {
    Json,
    Latex,
}

pub fn run_repl(version: &str, options: RunOptions) {
    let stdin_handle = io::stdin();
    let stdout_handle = io::stdout();
    let mut stdin_locked = stdin_handle.lock();
    let mut stdout_locked = stdout_handle.lock();
    let result = run_repl_loop_with_readers_and_mode(
        version,
        options,
        &mut stdin_locked,
        &mut stdout_locked,
        ReplOutputMode::Json,
    );
    match result {
        Ok(()) => {}
        Err(write_error) => {
            eprintln!(
                "{}",
                repl_io_error("repl", "output_error", write_error.to_string().as_str())
            );
        }
    }
}

pub fn run_latex_repl(version: &str) {
    let stdin_handle = io::stdin();
    let stdout_handle = io::stdout();
    let mut stdin_locked = stdin_handle.lock();
    let mut stdout_locked = stdout_handle.lock();
    match run_latex_repl_loop_with_readers(version, &mut stdin_locked, &mut stdout_locked) {
        Ok(()) => {}
        Err(write_error) => {
            eprintln!(
                "{}",
                repl_io_error(
                    "latex_repl",
                    "output_error",
                    write_error.to_string().as_str(),
                )
            );
        }
    }
}

fn run_latex_repl_loop_with_readers(
    version_banner: &str,
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
) -> io::Result<()> {
    run_repl_loop_with_readers_and_mode(
        version_banner,
        RunOptions::default(),
        stdin_reader,
        stdout_writer,
        ReplOutputMode::Latex,
    )
}

fn run_repl_loop_with_readers_and_mode(
    version_banner: &str,
    options: RunOptions,
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
    output_mode: ReplOutputMode,
) -> io::Result<()> {
    let mut runtime = Runtime::new(options);
    initialize_isolated_repl_runtime(&mut runtime);
    let stream = output_mode.stream_name();
    let content = JsonValue::Object(vec![
        (
            "version".to_string(),
            JsonValue::JsonString(version_banner.to_string()),
        ),
        (
            "mode".to_string(),
            JsonValue::JsonString("isolated".to_string()),
        ),
    ]);
    writeln!(
        stdout_writer,
        "{}",
        render_stream_output(stream, "ready", true, None, &[], content, JsonValue::Null)
    )?;

    run_repl_prompt_loop_with_runtime(&mut runtime, stdin_reader, stdout_writer, output_mode)
}

pub fn run_isolated_repl_with_runtime(version_banner: &str, runtime: &mut Runtime) {
    let stdin_handle = io::stdin();
    let stdout_handle = io::stdout();
    let mut stdin_locked = stdin_handle.lock();
    let mut stdout_locked = stdout_handle.lock();
    let result = run_isolated_repl_with_runtime_and_readers(
        version_banner,
        runtime,
        &mut stdin_locked,
        &mut stdout_locked,
    );
    if let Err(write_error) = result {
        eprintln!(
            "{}",
            repl_io_error("repl", "output_error", write_error.to_string().as_str())
        );
    }
}

fn run_isolated_repl_with_runtime_and_readers(
    version_banner: &str,
    runtime: &mut Runtime,
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
) -> io::Result<()> {
    let content = JsonValue::Object(vec![
        (
            "version".to_string(),
            JsonValue::JsonString(version_banner.to_string()),
        ),
        (
            "mode".to_string(),
            JsonValue::JsonString("continued".to_string()),
        ),
    ]);
    writeln!(
        stdout_writer,
        "{}",
        render_stream_output("repl", "ready", true, None, &[], content, JsonValue::Null,)
    )?;
    run_repl_prompt_loop_with_runtime(runtime, stdin_reader, stdout_writer, ReplOutputMode::Json)
}

fn run_repl_prompt_loop_with_runtime(
    runtime: &mut Runtime,
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
    output_mode: ReplOutputMode,
) -> io::Result<()> {
    let mut line_buffer = String::new();
    let mut source_buffer = String::new();
    let mut collecting_multiline = false;
    let stream = output_mode.stream_name();

    loop {
        let prompt = if collecting_multiline { "... " } else { ">>> " };
        writeln!(
            stdout_writer,
            "{}",
            render_stream_output(
                stream,
                "prompt",
                true,
                None,
                &[],
                JsonValue::JsonString(prompt.to_string()),
                JsonValue::Null,
            )
        )?;
        stdout_writer.flush()?;

        line_buffer.clear();
        let bytes_read = match stdin_reader.read_line(&mut line_buffer) {
            Ok(byte_count) => byte_count,
            Err(read_error) => {
                writeln!(
                    stdout_writer,
                    "{}",
                    repl_io_error(stream, "input_error", read_error.to_string().as_str())
                )?;
                break;
            }
        };

        if bytes_read == 0 {
            write_repl_source_if_not_empty(&source_buffer, runtime, stdout_writer, output_mode)?;
            writeln!(
                stdout_writer,
                "{}",
                render_stream_output(
                    stream,
                    "closed",
                    true,
                    None,
                    &[],
                    JsonValue::Null,
                    JsonValue::Null,
                )
            )?;
            break;
        }

        let trimmed_line = line_buffer.trim();
        if trimmed_line.is_empty() {
            if collecting_multiline {
                write_repl_source_if_not_empty(
                    &source_buffer,
                    runtime,
                    stdout_writer,
                    output_mode,
                )?;
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

        write_repl_source_if_not_empty(trimmed_line, runtime, stdout_writer, output_mode)?;
    }

    Ok(())
}

fn write_repl_source_if_not_empty(
    source: &str,
    runtime: &mut Runtime,
    stdout_writer: &mut dyn Write,
    output_mode: ReplOutputMode,
) -> io::Result<()> {
    if source.trim().is_empty() {
        return Ok(());
    }

    let normalized_source = remove_windows_carriage_from_str(source);
    if super::terminal_import::terminal_input_starts_with_import(normalized_source.as_str()) {
        let (ok, output) =
            super::terminal_import::run_terminal_import(normalized_source.as_str(), runtime);
        let (content, error) = if ok {
            (JsonValue::RawJson(output), JsonValue::Null)
        } else {
            (JsonValue::Null, JsonValue::RawJson(output))
        };
        return writeln!(
            stdout_writer,
            "{}",
            render_stream_output(
                output_mode.stream_name(),
                "result",
                ok,
                None,
                &[],
                content,
                error,
            )
        );
    }
    match output_mode {
        ReplOutputMode::Json => {
            let (stmt_results, runtime_error) = runtime
                .execute_source(normalized_source.as_str())
                .into_parts();
            let ok = runtime_error.is_none();
            let error = runtime_error
                .as_ref()
                .map(|error| JsonValue::RawJson(render_runtime_error_json(runtime, error, true)))
                .unwrap_or(JsonValue::Null);
            writeln!(
                stdout_writer,
                "{}",
                render_stream_output(
                    "repl",
                    "result",
                    ok,
                    None,
                    stmt_results.as_slice(),
                    JsonValue::Null,
                    error,
                )
            )
        }
        ReplOutputMode::Latex => match to_latex(normalized_source.as_str(), runtime) {
            Ok(output_text) => writeln!(
                stdout_writer,
                "{}",
                render_stream_output(
                    "latex_repl",
                    "result",
                    true,
                    None,
                    &[],
                    JsonValue::JsonString(output_text.trim().to_string()),
                    JsonValue::Null,
                )
            ),
            Err(error) => writeln!(
                stdout_writer,
                "{}",
                render_stream_output(
                    "latex_repl",
                    "result",
                    false,
                    None,
                    &[],
                    JsonValue::Null,
                    JsonValue::RawJson(render_runtime_error_json(runtime, &error, true)),
                )
            ),
        },
    }
}

impl ReplOutputMode {
    fn stream_name(self) -> &'static str {
        match self {
            Self::Json => "repl",
            Self::Latex => "latex_repl",
        }
    }
}

fn repl_io_error(stream: &str, event: &str, message: &str) -> String {
    render_stream_output(
        stream,
        event,
        false,
        None,
        &[],
        JsonValue::Null,
        JsonValue::Object(vec![
            (
                "kind".to_string(),
                JsonValue::JsonString("io_error".to_string()),
            ),
            (
                "message".to_string(),
                JsonValue::JsonString(message.to_string()),
            ),
        ]),
    )
}

fn initialize_isolated_repl_runtime(runtime: &mut Runtime) {
    runtime.start_virtual_source(VirtualSource::Repl);
}

fn repl_line_starts_block(line: &str) -> bool {
    line.trim_end().ends_with(':')
}

#[cfg(test)]
#[path = "../../tests/unit/pipeline/repl/tests.rs"]
mod tests;
