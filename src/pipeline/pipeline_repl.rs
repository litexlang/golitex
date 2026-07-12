use crate::prelude::*;
use crate::to_latex::to_latex;
use std::io::{self, BufRead, Write};
use std::path::Path;

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
    force_isolated: bool,
) {
    return run_repl_loop_internal(
        version,
        output_style,
        strict_mode,
        output_language,
        force_isolated,
    );
}

pub fn run_latex_repl(version: &str) {
    return run_latex_repl_loop_internal(version);
}

fn run_repl_loop_internal(
    version_banner: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    force_isolated: bool,
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
        !force_isolated,
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
        false,
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
        false,
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
    discover_project_from_current_directory: bool,
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
    runtime.set_output_style(output_style);
    runtime.strict_mode = strict_mode;
    runtime.output_language = output_language;

    let startup = if discover_project_from_current_directory {
        match std::env::current_dir() {
            Ok(directory) => {
                match initialize_repl_runtime_for_directory(&mut runtime, &directory) {
                    Ok(startup) => startup,
                    Err(error) => {
                        writeln!(stdout_writer, "Project REPL could not start.")?;
                        writeln!(
                            stdout_writer,
                            "{}",
                            display_runtime_error_json(&runtime, &error, true).trim()
                        )?;
                        return Ok(());
                    }
                }
            }
            Err(error) => {
                writeln!(
                    stdout_writer,
                    "Could not inspect the current directory ({}); starting isolated REPL.",
                    error
                )?;
                initialize_isolated_repl_runtime(&mut runtime);
                ReplStartup::Isolated
            }
        }
    } else {
        initialize_isolated_repl_runtime(&mut runtime);
        ReplStartup::Isolated
    };

    match startup {
        ReplStartup::Isolated => writeln!(stdout_writer, "Isolated REPL.")?,
        ReplStartup::Project { root } => writeln!(stdout_writer, "Project REPL: {}", root)?,
    }

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

enum ReplStartup {
    Isolated,
    Project { root: String },
}

fn initialize_isolated_repl_runtime(runtime: &mut Runtime) {
    runtime.new_file_path_new_env_new_name_scope("repl");
}

fn initialize_repl_runtime_for_directory(
    runtime: &mut Runtime,
    directory: &Path,
) -> Result<ReplStartup, RuntimeError> {
    if !directory.join("litex.config").is_file() {
        initialize_isolated_repl_runtime(runtime);
        return Ok(ReplStartup::Isolated);
    }

    let root = directory.to_string_lossy().into_owned();
    discover_repository(runtime, root.as_str())?;
    runtime.prepare_current_repository_for_repl(format!("{}/<repl>", root).as_str());
    Ok(ReplStartup::Project { root })
}

fn repl_line_starts_block(line: &str) -> bool {
    line.trim_end().ends_with(':')
}

#[cfg(test)]
mod tests {
    use super::{
        initialize_repl_runtime_for_directory, run_latex_repl_loop_with_readers,
        run_repl_loop_with_readers, ReplStartup,
    };
    use crate::pipeline::run_source_code;
    use crate::runtime::{OutputStyle, Runtime};
    use std::fs;
    use std::io::Cursor;
    use std::path::PathBuf;

    fn repl_test_dir(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!("litex-repl-{}-{}", name, std::process::id()))
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
    fn project_repl_loads_root_exports_without_running_entrance() {
        let root = repl_test_dir("project");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("create project fixture");
        fs::write(
            root.join("litex.config"),
            "[entrance]\nfile = \"./main.lit\"\n\n[export]\nfacts = \"./facts.lit\"\n",
        )
        .expect("write config");
        fs::write(root.join("main.lit"), "have entrance_value R = 9\n").expect("write entrance");
        fs::write(root.join("facts.lit"), "have x R = 1\n").expect("write export");

        let mut runtime = Runtime::new_with_builtin_code();
        let startup = initialize_repl_runtime_for_directory(&mut runtime, &root)
            .expect("discover project for REPL");
        assert!(matches!(startup, ReplStartup::Project { .. }));
        assert!(runtime.current_file_path_rc().ends_with("/<repl>"));
        assert!(
            !runtime
                .current_module()
                .main_environment
                .defined_identifiers
                .contains_key("entrance_value"),
            "the entrance file must not run when the REPL starts"
        );

        let (_, import_error) = run_source_code("local import facts", &mut runtime);
        assert!(import_error.is_none(), "{import_error:?}");
        let (_, fact_error) = run_source_code("facts::x = 1", &mut runtime);
        assert!(fact_error.is_none(), "{fact_error:?}");
        let (_, save_error) = run_source_code("have saved R = facts::x", &mut runtime);
        assert!(save_error.is_none(), "{save_error:?}");
        let (_, persistent_error) = run_source_code("saved = 1", &mut runtime);
        assert!(persistent_error.is_none(), "{persistent_error:?}");

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn repl_without_current_directory_config_stays_isolated() {
        let root = repl_test_dir("isolated");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("create isolated fixture");

        let mut runtime = Runtime::new_with_builtin_code();
        let startup = initialize_repl_runtime_for_directory(&mut runtime, &root)
            .expect("start isolated REPL");
        assert!(matches!(startup, ReplStartup::Isolated));
        let (_, error) = run_source_code("local import facts", &mut runtime);
        assert!(error.is_some());

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn project_repl_rejects_invalid_current_directory_config() {
        let root = repl_test_dir("invalid-config");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("create invalid project fixture");
        fs::write(
            root.join("litex.config"),
            "[export]\nfacts = \"./facts.lit\"\n",
        )
        .expect("write invalid config");

        let mut runtime = Runtime::new_with_builtin_code();
        let result = initialize_repl_runtime_for_directory(&mut runtime, &root);
        assert!(
            result.is_err(),
            "invalid project configuration must stop startup"
        );

        let _ = fs::remove_dir_all(&root);
    }
}
