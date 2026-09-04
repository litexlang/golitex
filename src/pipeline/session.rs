use super::file_execution::file_execution_option;
use super::source_execution::SourceRunOutcome;
use crate::prelude::*;
use std::env;
use std::io::{self, BufRead, Write};
use std::path::Path;

pub struct SessionRequest {
    pub options: InvocationOptions,
    pub target: SessionTarget,
}

impl SessionRequest {
    pub fn new(options: InvocationOptions, target: SessionTarget) -> Self {
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
                false,
                None,
                &[],
                JsonValue::Null,
                session_error("current_directory_error", error.to_string().as_str()),
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
        eprintln!(
            "{}",
            render_stream_output(
                "session",
                "output_error",
                false,
                None,
                &[],
                JsonValue::Null,
                session_error("io_error", error.to_string().as_str()),
            )
        );
    }
}

fn run_session_loop_with_readers_and_target(
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
    directory: &Path,
    options: InvocationOptions,
    target: SessionTarget,
) -> io::Result<()> {
    let mut runtime = Runtime::new(options);

    let (startup_mode, mut all_results) =
        match initialize_session_runtime(&mut runtime, directory, target) {
            Ok(startup) => startup,
            Err((stmt_results, error)) => {
                let error_json = render_runtime_error_json(&runtime, &error, true);
                write_session_event(
                    stdout_writer,
                    "startup_error",
                    false,
                    None,
                    stmt_results.as_slice(),
                    JsonValue::Null,
                    JsonValue::RawJson(error_json),
                )?;
                return Ok(());
            }
        };
    write_session_event(
        stdout_writer,
        "ready",
        true,
        None,
        &[],
        JsonValue::Object(vec![(
            "mode".to_string(),
            JsonValue::JsonString(startup_mode.to_string()),
        )]),
        JsonValue::Null,
    )?;

    let mut has_failed = false;
    let mut header = String::new();

    loop {
        header.clear();
        if stdin_reader.read_line(&mut header)? == 0 {
            write_session_event(
                stdout_writer,
                "closed",
                true,
                None,
                &[],
                JsonValue::Null,
                JsonValue::Null,
            )?;
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
                        false,
                        if id.is_empty() { None } else { Some(id) },
                        &[],
                        JsonValue::Null,
                        session_error("invalid_frame", "run requires: run <id> <utf8-byte-count>"),
                    )?;
                    continue;
                }
                let mut source_bytes = vec![0; source_byte_count.unwrap()];
                if let Err(error) = stdin_reader.read_exact(source_bytes.as_mut_slice()) {
                    write_session_event(
                        stdout_writer,
                        "protocol_error",
                        false,
                        Some(id),
                        &[],
                        JsonValue::Null,
                        session_error(
                            "frame_read_error",
                            format!("could not read source bytes: {}", error).as_str(),
                        ),
                    )?;
                    return Ok(());
                }
                let source = match String::from_utf8(source_bytes) {
                    Ok(source) => source,
                    Err(error) => {
                        write_session_event(
                            stdout_writer,
                            "protocol_error",
                            false,
                            Some(id),
                            &[],
                            JsonValue::Null,
                            session_error(
                                "invalid_utf8",
                                format!("source bytes must be UTF-8: {}", error).as_str(),
                            ),
                        )?;
                        continue;
                    }
                };

                if has_failed {
                    write_session_event(
                        stdout_writer,
                        "skipped",
                        false,
                        Some(id),
                        &[],
                        JsonValue::Null,
                        session_error("earlier_block_failed", "an earlier block failed"),
                    )?;
                    continue;
                }

                let SourceRunOutcome {
                    stmt_results: mut results,
                    runtime_error,
                } = runtime.execute_source(source.replace('\r', "").as_str());
                let ok = runtime_error.is_none();
                if !ok {
                    has_failed = true;
                }
                write_session_event(
                    stdout_writer,
                    "result",
                    ok,
                    Some(id),
                    results.as_slice(),
                    JsonValue::Null,
                    runtime_error
                        .as_ref()
                        .map(|error| {
                            JsonValue::RawJson(render_runtime_error_json(&runtime, error, true))
                        })
                        .unwrap_or(JsonValue::Null),
                )?;
                all_results.append(&mut results);
            }
            "artifacts" => {
                if id.is_empty() || fields.next().is_some() {
                    write_session_event(
                        stdout_writer,
                        "protocol_error",
                        false,
                        if id.is_empty() { None } else { Some(id) },
                        &[],
                        JsonValue::Null,
                        session_error("invalid_frame", "artifacts requires: artifacts <id>"),
                    )?;
                    continue;
                }
                if has_failed {
                    write_session_event(
                        stdout_writer,
                        "artifacts_unavailable",
                        false,
                        Some(id),
                        &[],
                        JsonValue::Null,
                        session_error(
                            "earlier_block_failed",
                            "artifacts are unavailable after a failed block",
                        ),
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
                    !options.output_detail().is_detailed(),
                    &runtime,
                    all_results.as_slice(),
                    None,
                );
                let (_, fact_graph) = render_fact_graph_from_stmt_results(
                    RunTargetKind::Session,
                    None,
                    !options.output_detail().is_detailed(),
                    &runtime,
                    all_results.as_slice(),
                    None,
                );
                let (_, definition_graph) = render_definition_graph_from_stmt_results(
                    RunTargetKind::Session,
                    None,
                    !options.output_detail().is_detailed(),
                    &mut runtime,
                    all_results.as_slice(),
                    None,
                );
                write_session_event(
                    stdout_writer,
                    "artifacts",
                    true,
                    Some(id),
                    &[],
                    JsonValue::Object(vec![
                        ("summary".to_string(), JsonValue::RawJson(summary)),
                        ("graph".to_string(), JsonValue::RawJson(graph)),
                        ("fact_graph".to_string(), JsonValue::RawJson(fact_graph)),
                        (
                            "definition_graph".to_string(),
                            JsonValue::RawJson(definition_graph),
                        ),
                    ]),
                    JsonValue::Null,
                )?;
            }
            "close" if id.is_empty() && fields.next().is_none() => {
                write_session_event(
                    stdout_writer,
                    "closed",
                    true,
                    None,
                    &[],
                    JsonValue::Null,
                    JsonValue::Null,
                )?;
                return Ok(());
            }
            _ => {
                write_session_event(
                    stdout_writer,
                    "protocol_error",
                    false,
                    if id.is_empty() { None } else { Some(id) },
                    &[],
                    JsonValue::Null,
                    session_error("unknown_frame", "expected run, artifacts, or close"),
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
    if let SessionTarget::File { path: preload_file } = &target {
        let clean_path = preload_file.replace('\r', "");
        let path = Path::new(clean_path.as_str());
        let path = if path.is_absolute() {
            path.to_path_buf()
        } else {
            directory.join(path)
        };
        let path_string = path.to_string_lossy().into_owned();
        let execution = file_execution_option(path_string.as_str());
        let (stmt_results, runtime_error) = match execution {
            LitexExecution::File => execute_file_in_runtime(path_string.as_str(), runtime),
            LitexExecution::IsolatedFile => {
                execute_isolated_file_in_runtime(path_string.as_str(), runtime)
            }
            _ => unreachable!("file context resolved to a non-file execution option"),
        };
        if let Some(error) = runtime_error {
            return Err((stmt_results, error));
        }
        if execution == LitexExecution::IsolatedFile {
            if let Err(error) =
                runtime.prepare_current_module_for_virtual_source(VirtualSource::Session)
            {
                return Err((stmt_results, error));
            }
            return Ok(("isolated", stmt_results));
        }
        if let Err(error) =
            runtime.prepare_current_module_for_virtual_source(VirtualSource::Session)
        {
            return Err((stmt_results, error));
        }
        return Ok(("project", stmt_results));
    }

    if let SessionTarget::IsolatedFile { path: preload_file } = &target {
        let clean_path = preload_file.replace('\r', "");
        let path = Path::new(clean_path.as_str());
        let path = if path.is_absolute() {
            path.to_path_buf()
        } else {
            directory.join(path)
        };
        let path_string = path.to_string_lossy().into_owned();
        let (stmt_results, runtime_error) =
            execute_isolated_file_in_runtime(path_string.as_str(), runtime);
        if let Some(error) = runtime_error {
            return Err((stmt_results, error));
        }
        if let Err(error) =
            runtime.prepare_current_module_for_virtual_source(VirtualSource::Session)
        {
            return Err((stmt_results, error));
        }
        return Ok(("isolated", stmt_results));
    }

    if target == SessionTarget::Isolated || !directory.join("litex.config").is_file() {
        runtime.start_virtual_source(VirtualSource::Session);
        return Ok(("isolated", vec![]));
    }

    let root = directory.to_string_lossy().into_owned();
    if let Err(error) = discover_repository(runtime, root.as_str()) {
        return Err((vec![], error));
    }
    if let Err(error) = runtime.prepare_current_module_for_virtual_source(VirtualSource::Session) {
        return Err((vec![], error));
    }
    Ok(("project", vec![]))
}

fn write_session_event(
    stdout_writer: &mut dyn Write,
    event: &str,
    ok: bool,
    id: Option<&str>,
    statement_results: &[StmtResult],
    content: JsonValue,
    error: JsonValue,
) -> io::Result<()> {
    writeln!(
        stdout_writer,
        "{}",
        render_stream_output("session", event, ok, id, statement_results, content, error,)
    )
}

fn session_error(kind: &str, message: &str) -> JsonValue {
    JsonValue::Object(vec![
        ("kind".to_string(), JsonValue::JsonString(kind.to_string())),
        (
            "message".to_string(),
            JsonValue::JsonString(message.to_string()),
        ),
    ])
}

#[cfg(test)]
#[path = "../../tests/unit/pipeline/session/tests.rs"]
mod tests;
