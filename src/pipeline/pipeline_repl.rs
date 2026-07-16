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

#[cfg(test)]
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
    runtime.isolated = true;
    runtime.new_file_path_new_env_new_name_scope("repl");
}

fn repl_line_starts_block(line: &str) -> bool {
    line.trim_end().ends_with(':')
}

#[cfg(test)]
mod tests {
    use super::{
        run_isolated_repl_with_runtime_and_readers, run_latex_repl_loop_with_readers,
        run_repl_loop_with_readers,
    };
    use crate::pipeline::{run_file_with_project_context, run_source_code};
    use crate::runtime::{OutputStyle, Runtime};
    use std::fs;
    use std::io::Cursor;

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
        assert!(output_text.contains("\"result\": \"success\""));
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
        assert!(output_text.contains("\"result\": \"success\""));
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
            false,
        );
        assert!(file_error.is_none(), "{file_error:?}");
        assert!(runtime.isolated);

        let mut input = Cursor::new(b"from_file = 1\nhave from_repl R = 2\n".as_slice());
        let mut output = Vec::new();
        run_isolated_repl_with_runtime_and_readers("test", &mut runtime, &mut input, &mut output)
            .expect("continue isolated REPL");
        let output = String::from_utf8(output).expect("UTF-8 REPL output");
        assert!(output.contains("Continuing isolated REPL."));
        assert!(output.contains("\"result\": \"success\""), "{output}");

        let (_, continuation_error) = run_source_code("from_repl = 2", &mut runtime);
        assert!(continuation_error.is_none(), "{continuation_error:?}");

        let _ = fs::remove_dir_all(&directory);
    }
}
