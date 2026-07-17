use crate::prelude::*;
use std::env;
use std::io::{self, BufRead, Write};
use std::path::Path;

/// Run a machine-readable, one-process Litex session.
///
/// Input frames are `run <id> <utf8-byte-count>`, followed by exactly that
/// many source bytes, or `artifacts <id>`. Each response is one JSON line.
/// The length frame keeps arbitrary multiline Litex source out of terminal
/// prompt parsing while preserving the same project-local-import semantics as
/// the interactive REPL.
pub fn run_session_with_output_style_and_strict_and_language(
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    force_isolated: bool,
) {
    let stdin_handle = io::stdin();
    let stdout_handle = io::stdout();
    let mut stdin_locked = stdin_handle.lock();
    let mut stdout_locked = stdout_handle.lock();
    let directory = match env::current_dir() {
        Ok(directory) => directory,
        Err(error) => {
            let _ = write_session_event(
                &mut stdout_locked,
                "startup_error",
                None,
                &[('e', error.to_string())],
            );
            return;
        }
    };

    if let Err(error) = run_session_loop_with_readers(
        &mut stdin_locked,
        &mut stdout_locked,
        &directory,
        output_style,
        strict_mode,
        output_language,
        force_isolated,
    ) {
        eprintln!("session output error: {}", error);
    }
}

fn run_session_loop_with_readers(
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
    directory: &Path,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    force_isolated: bool,
) -> io::Result<()> {
    let mut runtime = Runtime::new();
    runtime.set_output_style(output_style);
    runtime.strict_mode = strict_mode;
    runtime.output_language = output_language;

    let startup_mode = match initialize_session_runtime(&mut runtime, directory, force_isolated) {
        Ok(mode) => mode,
        Err(error) => {
            write_session_event(
                stdout_writer,
                "startup_error",
                None,
                &[('e', display_runtime_error_json(&runtime, &error, true))],
            )?;
            return Ok(());
        }
    };
    write_session_event(
        stdout_writer,
        "ready",
        None,
        &[('m', startup_mode.to_string())],
    )?;

    let mut all_results: Vec<StmtResult> = Vec::new();
    let mut has_failed = false;
    let mut header = String::new();

    loop {
        header.clear();
        if stdin_reader.read_line(&mut header)? == 0 {
            return Ok(());
        }
        let header = header.trim_end_matches(['\n', '\r']);
        if header.is_empty() {
            continue;
        }

        let mut fields = header.split_ascii_whitespace();
        let command = fields.next().unwrap_or_default();
        let id = fields.next().unwrap_or_default();

        match command {
            "run" => {
                let source_byte_count = fields.next().and_then(|value| value.parse::<usize>().ok());
                if id.is_empty() || source_byte_count.is_none() || fields.next().is_some() {
                    write_session_event(
                        stdout_writer,
                        "protocol_error",
                        if id.is_empty() { None } else { Some(id) },
                        &[('e', "run requires: run <id> <utf8-byte-count>".to_string())],
                    )?;
                    continue;
                }
                let mut source_bytes = vec![0; source_byte_count.unwrap()];
                if let Err(error) = stdin_reader.read_exact(source_bytes.as_mut_slice()) {
                    write_session_event(
                        stdout_writer,
                        "protocol_error",
                        Some(id),
                        &[('e', format!("could not read source frame: {}", error))],
                    )?;
                    return Ok(());
                }
                let source = match String::from_utf8(source_bytes) {
                    Ok(source) => source,
                    Err(error) => {
                        write_session_event(
                            stdout_writer,
                            "protocol_error",
                            Some(id),
                            &[('e', format!("source frame must be UTF-8: {}", error))],
                        )?;
                        continue;
                    }
                };

                if has_failed {
                    write_session_event(
                        stdout_writer,
                        "skipped",
                        Some(id),
                        &[('e', "an earlier block failed".to_string())],
                    )?;
                    continue;
                }

                let (mut results, runtime_error) =
                    run_source_code(source.replace('\r', "").as_str(), &mut runtime);
                let (ok, trace) =
                    render_run_source_code_output(&runtime, &results, &runtime_error, true);
                all_results.append(&mut results);
                if !ok {
                    has_failed = true;
                }
                write_session_event(
                    stdout_writer,
                    "block",
                    Some(id),
                    &[
                        (
                            'o',
                            if ok {
                                "true".to_string()
                            } else {
                                "false".to_string()
                            },
                        ),
                        ('t', trace.trim().to_string()),
                    ],
                )?;
            }
            "artifacts" => {
                if id.is_empty() || fields.next().is_some() {
                    write_session_event(
                        stdout_writer,
                        "protocol_error",
                        if id.is_empty() { None } else { Some(id) },
                        &[('e', "artifacts requires: artifacts <id>".to_string())],
                    )?;
                    continue;
                }
                if has_failed {
                    write_session_event(
                        stdout_writer,
                        "artifacts_unavailable",
                        Some(id),
                        &[(
                            'e',
                            "artifacts are unavailable after a failed block".to_string(),
                        )],
                    )?;
                    continue;
                }

                let no_error = None;
                let summary = display_run_summary_json_with_runtime(
                    &runtime,
                    all_results.as_slice(),
                    &no_error,
                );
                let (_, graph) = render_graph_from_stmt_results(
                    "session",
                    "entry",
                    !output_style.is_detailed(),
                    &runtime,
                    all_results.as_slice(),
                    None,
                );
                let (_, fact_graph) = render_fact_graph_from_stmt_results(
                    "session",
                    "entry",
                    !output_style.is_detailed(),
                    &runtime,
                    all_results.as_slice(),
                    None,
                );
                let (_, definition_graph) = render_definition_graph_from_stmt_results(
                    "session",
                    "entry",
                    !output_style.is_detailed(),
                    &mut runtime,
                    all_results.as_slice(),
                    None,
                );
                write_session_event(
                    stdout_writer,
                    "artifacts",
                    Some(id),
                    &[
                        ('s', summary),
                        ('g', graph),
                        ('f', fact_graph),
                        ('d', definition_graph),
                    ],
                )?;
            }
            "close" if id.is_empty() && fields.next().is_none() => return Ok(()),
            _ => {
                write_session_event(
                    stdout_writer,
                    "protocol_error",
                    if id.is_empty() { None } else { Some(id) },
                    &[('e', "expected run, artifacts, or close".to_string())],
                )?;
            }
        }
    }
}

fn initialize_session_runtime(
    runtime: &mut Runtime,
    directory: &Path,
    force_isolated: bool,
) -> Result<&'static str, RuntimeError> {
    if force_isolated || !directory.join("litex.config").is_file() {
        runtime.isolated = true;
        runtime.new_file_path_new_env_new_name_scope("session");
        return Ok("isolated");
    }

    let root = directory.to_string_lossy().into_owned();
    runtime.isolated = false;
    discover_repository(runtime, root.as_str())?;
    runtime.prepare_current_repository_for_repl(format!("{}/<session>", root).as_str());
    Ok("project")
}

fn write_session_event(
    stdout_writer: &mut dyn Write,
    event: &str,
    id: Option<&str>,
    fields: &[(char, String)],
) -> io::Result<()> {
    let mut output = format!("{{\"event\":{}}}", json_string(event));
    output.pop();
    if let Some(id) = id {
        output.push_str(format!(",\"id\":{}", json_string(id)).as_str());
    }
    for (key, value) in fields {
        match key {
            'o' => output.push_str(format!(",\"ok\":{}", value).as_str()),
            'm' => output.push_str(format!(",\"mode\":{}", json_string(value)).as_str()),
            't' => output.push_str(format!(",\"trace\":{}", json_string(value)).as_str()),
            's' => output.push_str(format!(",\"summary\":{}", json_string(value)).as_str()),
            'g' => output.push_str(format!(",\"graph\":{}", json_string(value)).as_str()),
            'f' => output.push_str(format!(",\"fact_graph\":{}", json_string(value)).as_str()),
            'd' => {
                output.push_str(format!(",\"definition_graph\":{}", json_string(value)).as_str())
            }
            'e' => output.push_str(format!(",\"error\":{}", json_string(value)).as_str()),
            _ => {}
        }
    }
    output.push('}');
    writeln!(stdout_writer, "{}", output)
}

fn json_string(value: &str) -> String {
    render_json_value(&JsonValue::JsonString(value.to_string()), 0)
}

#[cfg(test)]
mod tests {
    use super::run_session_loop_with_readers;
    use crate::prelude::OutputLanguage;
    use crate::runtime::OutputStyle;
    use std::fs;
    use std::io::Cursor;
    use std::path::PathBuf;

    fn session_test_dir(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!("litex-session-{}-{}", name, std::process::id()))
    }

    fn run_frame(id: &str, source: &str) -> String {
        format!("run {} {}\n{}", id, source.as_bytes().len(), source)
    }

    #[test]
    fn project_session_keeps_previous_blocks() {
        let root = session_test_dir("project");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("create project fixture");
        fs::write(
            root.join("litex.config"),
            "[hierarchy]\nmodule\n\n[export]\nmain = \"./main.lit\"\n",
        )
        .expect("write config");
        fs::write(root.join("main.lit"), "have planned_value R = 9\n").expect("write plan file");

        let input = format!(
            "{}{}artifacts final\nclose\n",
            run_frame("definition", "have x R = 1\n"),
            run_frame("proof", "have y R = x + 1\ny = 2\n"),
        );
        let mut stdin_reader = Cursor::new(input.into_bytes());
        let mut stdout_writer = Vec::new();

        run_session_loop_with_readers(
            &mut stdin_reader,
            &mut stdout_writer,
            &root,
            OutputStyle::Normal,
            false,
            OutputLanguage::English,
            false,
        )
        .expect("session must run");

        let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
        assert!(output.contains("\"event\":\"ready\",\"mode\":\"project\""));
        assert!(output.contains("\"id\":\"definition\",\"ok\":true"));
        assert!(output.contains("\"id\":\"proof\",\"ok\":true"));
        assert!(output.contains("y = 2"));
        assert!(output.contains("\"event\":\"artifacts\",\"id\":\"final\""));
        assert!(output.contains("litex-fact-graph"));
        assert!(output.contains("litex-definition-graph"));

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn session_accepts_a_multiline_code_block() {
        let root = session_test_dir("multiline");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("create isolated fixture");

        let input = format!("{}close\n", run_frame("block", "sketch:\n    1 = 1\n"));
        let mut stdin_reader = Cursor::new(input.into_bytes());
        let mut stdout_writer = Vec::new();

        run_session_loop_with_readers(
            &mut stdin_reader,
            &mut stdout_writer,
            &root,
            OutputStyle::Normal,
            false,
            OutputLanguage::English,
            false,
        )
        .expect("session must run");

        let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
        assert!(output.contains("\"id\":\"block\",\"ok\":true"));
        assert!(!output.contains("block header missing body"));

        let _ = fs::remove_dir_all(&root);
    }
}
