use super::source_execution::SourceRunOutcome;
use crate::prelude::*;
use std::env;
use std::io::{self, BufRead, Write};
use std::path::Path;

pub struct SessionRequest {
    pub options: RunOptions,
    pub target: SessionTarget,
}

impl SessionRequest {
    pub fn new(options: RunOptions, target: SessionTarget) -> Self {
        Self { options, target }
    }
}

/// Run a machine-readable, one-process Litex session.
///
/// Input frames are `run <id> <utf8-byte-count>`, followed by exactly that
/// many source bytes, or `artifacts <id>`. Each response is one JSON line.
/// The length frame keeps arbitrary multiline Litex source out of terminal
/// prompt parsing. Frames are Litex source only: terminal import commands are
/// deliberately outside this machine protocol.
pub fn run_session(request: SessionRequest) {
    let SessionRequest { options, target } = request;
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

    if let Err(error) = run_session_loop_with_readers_and_target(
        &mut stdin_locked,
        &mut stdout_locked,
        &directory,
        options,
        target,
    ) {
        eprintln!("session output error: {}", error);
    }
}

fn run_session_loop_with_readers_and_target(
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
    directory: &Path,
    options: RunOptions,
    target: SessionTarget,
) -> io::Result<()> {
    let mut runtime = Runtime::new(options);

    let (startup_mode, mut all_results) =
        match initialize_session_runtime(&mut runtime, directory, target) {
        Ok(startup) => startup,
        Err((stmt_results, error)) => {
            let error_json = display_runtime_error_json(&runtime, &error, true);
            let runtime_error = Some(error);
            let (_, trace) = render_run_output(&runtime, &stmt_results, &runtime_error);
            write_session_event(
                stdout_writer,
                "startup_error",
                None,
                &[('e', error_json), ('t', trace.trim().to_string())],
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

                let SourceRunOutcome {
                    stmt_results: mut results,
                    runtime_error,
                } = runtime.execute_source(source.replace('\r', "").as_str());
                let (ok, trace) = render_run_output(&runtime, &results, &runtime_error);
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
                let summary = render_run_summary(RunSummaryRequest {
                    runtime: &runtime,
                    stmt_results: all_results.as_slice(),
                    runtime_error: &no_error,
                });
                let (_, graph) = render_graph_from_stmt_results(
                    RunTargetKind::Session,
                    None,
                    !options.output_style.is_detailed(),
                    &runtime,
                    all_results.as_slice(),
                    None,
                );
                let (_, fact_graph) = render_fact_graph_from_stmt_results(
                    RunTargetKind::Session,
                    None,
                    !options.output_style.is_detailed(),
                    &runtime,
                    all_results.as_slice(),
                    None,
                );
                let (_, definition_graph) = render_definition_graph_from_stmt_results(
                    RunTargetKind::Session,
                    None,
                    !options.output_style.is_detailed(),
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
    target: SessionTarget,
) -> Result<(&'static str, Vec<StmtResult>), (Vec<StmtResult>, RuntimeError)> {
    let source_label = ExecutionTarget::Session(target.clone())
        .source_label()
        .to_string();

    if let SessionTarget::File {
        path: preload_file,
        mode,
    } = &target
    {
        let clean_path = preload_file.replace('\r', "");
        let path = Path::new(clean_path.as_str());
        let path = if path.is_absolute() {
            path.to_path_buf()
        } else {
            directory.join(path)
        };
        let path_string = path.to_string_lossy().into_owned();
        let (stmt_results, runtime_error) =
            execute_file_in_runtime(path_string.as_str(), runtime, *mode);
        if let Some(error) = runtime_error {
            return Err((stmt_results, error));
        }
        if mode.is_isolated() {
            return Ok(("isolated", stmt_results));
        }
        if let Err(error) = runtime.prepare_current_repository_for_repl(source_label.as_str()) {
            return Err((stmt_results, error));
        }
        return Ok(("project", stmt_results));
    }

    if target == SessionTarget::Isolated
        || !directory.join("litex.config").is_file()
    {
        runtime.start_isolated_source(source_label.as_str());
        return Ok(("isolated", vec![]));
    }

    let root = directory.to_string_lossy().into_owned();
    if let Err(error) = discover_repository(runtime, root.as_str()) {
        return Err((vec![], error));
    }
    if let Err(error) = runtime.prepare_current_repository_for_repl(source_label.as_str()) {
        return Err((vec![], error));
    }
    Ok(("project", vec![]))
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
#[path = "../../tests/unit/pipeline/session/tests.rs"]
mod tests;
