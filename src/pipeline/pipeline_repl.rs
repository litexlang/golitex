use crate::prelude::*;
use crate::to_latex::to_latex;
use std::io::{self, BufRead, Write};

#[derive(Clone, Copy)]
enum ReplOutputMode {
    Json,
    Latex,
}

fn output_style_from_detail_output(detail_output: bool) -> OutputStyle {
    if detail_output {
        OutputStyle::Detailed
    } else {
        OutputStyle::Normal
    }
}

pub fn run_repl(version: &str) {
    return run_repl_with_detail_output(version, false);
}

pub fn run_repl_with_detail_output(version: &str, detail_output: bool) {
    return run_repl_loop_internal(
        version,
        output_style_from_detail_output(detail_output),
        false,
        OutputLanguage::English,
        false,
    );
}

pub fn run_repl_with_detail_output_and_strict(
    version: &str,
    detail_output: bool,
    strict_mode: bool,
) {
    return run_repl_loop_internal(
        version,
        output_style_from_detail_output(detail_output),
        strict_mode,
        OutputLanguage::English,
        false,
    );
}

pub fn run_repl_with_detail_output_and_strict_and_language(
    version: &str,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
) {
    return run_repl_loop_internal(
        version,
        output_style_from_detail_output(detail_output),
        strict_mode,
        output_language,
        false,
    );
}

pub fn run_repl_with_output_style_and_strict_and_language(
    version: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
) {
    return run_repl_loop_internal(version, output_style, strict_mode, output_language, false);
}

pub fn run_repl_with_output_style_and_strict_and_language_and_isolation(
    version: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    _force_isolated: bool,
) {
    return run_repl_loop_internal(version, output_style, strict_mode, output_language, false);
}

pub fn run_latex_repl(version: &str) {
    return run_latex_repl_loop_internal(version);
}

fn run_repl_loop_internal(
    version_banner: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    _force_isolated: bool,
) {
    let stdin_handle = io::stdin();
    let stdout_handle = io::stdout();
    let mut stdin_locked = stdin_handle.lock();
    let mut stdout_locked = stdout_handle.lock();
    let result = run_repl_loop_with_readers_and_mode(
        version_banner,
        output_style,
        strict_mode,
        output_language,
        &mut stdin_locked,
        &mut stdout_locked,
        ReplOutputMode::Json,
    );
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

fn run_latex_repl_loop_with_readers(
    version_banner: &str,
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
) -> io::Result<()> {
    run_repl_loop_with_readers_and_mode(
        version_banner,
        OutputStyle::Normal,
        false,
        OutputLanguage::English,
        stdin_reader,
        stdout_writer,
        ReplOutputMode::Latex,
    )
}

fn run_repl_loop_with_readers_and_mode(
    version_banner: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
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

    let mut runtime = Runtime::new();
    runtime.set_output_style(output_style);
    runtime.strict_mode = strict_mode;
    runtime.output_language = output_language;
    initialize_isolated_repl_runtime(&mut runtime);
    writeln!(stdout_writer, "Isolated REPL.")?;

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
        eprintln!("repl output error: {}", write_error);
    }
}

fn run_isolated_repl_with_runtime_and_readers(
    version_banner: &str,
    runtime: &mut Runtime,
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
) -> io::Result<()> {
    writeln!(stdout_writer, "Litex version {}", version_banner)?;
    writeln!(stdout_writer, "Continuing isolated REPL. Ctrl+D to exit.")?;
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
            let output_text = run_repl_source_if_not_empty(&source_buffer, runtime, output_mode);
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
                    run_repl_source_if_not_empty(&source_buffer, runtime, output_mode);
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

        let output_text = run_repl_source_if_not_empty(trimmed_line, runtime, output_mode);
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

fn initialize_isolated_repl_runtime(runtime: &mut Runtime) {
    runtime.start_isolated_source("repl");
    runtime.set_current_source_allows_inline_imports(true);
}

fn repl_line_starts_block(line: &str) -> bool {
    line.trim_end().ends_with(':')
}

#[cfg(test)]
#[path = "../../tests/unit/pipeline/pipeline_repl/tests.rs"]
mod tests;
