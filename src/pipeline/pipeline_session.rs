use crate::prelude::*;
use std::env;
use std::io::{self, BufRead, Write};
use std::path::Path;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SessionPreload {
    None,
    ThroughFile(String),
    BeforeFile(String),
}

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
    preload_file: Option<&str>,
) {
    let preload = match preload_file {
        Some(file) => SessionPreload::ThroughFile(file.to_string()),
        None => SessionPreload::None,
    };
    run_session_with_output_style_and_strict_and_language_and_preload(
        output_style,
        strict_mode,
        output_language,
        force_isolated,
        preload,
    );
}

pub fn run_session_with_output_style_and_strict_and_language_and_preload(
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    force_isolated: bool,
    preload: SessionPreload,
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

    if let Err(error) = run_session_loop_with_readers_and_preload(
        &mut stdin_locked,
        &mut stdout_locked,
        &directory,
        output_style,
        strict_mode,
        output_language,
        force_isolated,
        preload,
    ) {
        eprintln!("session output error: {}", error);
    }
}

#[cfg(test)]
fn run_session_loop_with_readers(
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
    directory: &Path,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    force_isolated: bool,
) -> io::Result<()> {
    run_session_loop_with_readers_and_preload(
        stdin_reader,
        stdout_writer,
        directory,
        output_style,
        strict_mode,
        output_language,
        force_isolated,
        SessionPreload::None,
    )
}

fn run_session_loop_with_readers_and_preload(
    stdin_reader: &mut dyn BufRead,
    stdout_writer: &mut dyn Write,
    directory: &Path,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    force_isolated: bool,
    preload: SessionPreload,
) -> io::Result<()> {
    let mut runtime = Runtime::new();
    runtime.set_output_style(output_style);
    runtime.strict_mode = strict_mode;
    runtime.output_language = output_language;

    let (startup_mode, mut all_results) =
        match initialize_session_runtime(&mut runtime, directory, force_isolated, preload) {
            Ok(startup) => startup,
            Err((stmt_results, error)) => {
                let error_json = display_runtime_error_json(&runtime, &error, true);
                let runtime_error = Some(error);
                let (_, trace) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);
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

                let (mut results, runtime_error, failure_kind) =
                    crate::pipeline::pipeline::run_source_code_with_failure_kind(
                        source.replace('\r', "").as_str(),
                        &mut runtime,
                    );
                let (ok, trace) =
                    render_run_source_code_output(&runtime, &results, &runtime_error, true);
                all_results.append(&mut results);
                if !ok
                    && failure_kind
                        != Some(crate::pipeline::pipeline::RunSourceFailureKind::TryStmt)
                {
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
    preload: SessionPreload,
) -> Result<(&'static str, Vec<StmtResult>), (Vec<StmtResult>, RuntimeError)> {
    if let SessionPreload::ThroughFile(preload_file) = &preload {
        let clean_path = preload_file.replace('\r', "");
        let path = Path::new(clean_path.as_str());
        let path = if path.is_absolute() {
            path.to_path_buf()
        } else {
            directory.join(path)
        };
        let path_string = path.to_string_lossy().into_owned();
        let (stmt_results, runtime_error) =
            run_file_with_project_context(path_string.as_str(), runtime, force_isolated);
        if let Some(error) = runtime_error {
            return Err((stmt_results, error));
        }
        if runtime.isolated {
            return Ok(("isolated", stmt_results));
        }
        if let Err(error) = runtime
            .prepare_current_repository_for_repl(format!("{}::<session>", path_string).as_str())
        {
            return Err((stmt_results, error));
        }
        return Ok(("project", stmt_results));
    }

    if let SessionPreload::BeforeFile(preload_file) = &preload {
        let clean_path = preload_file.replace('\r', "");
        let path = Path::new(clean_path.as_str());
        let path = if path.is_absolute() {
            path.to_path_buf()
        } else {
            directory.join(path)
        };
        let path_string = path.to_string_lossy().into_owned();
        if force_isolated {
            let error = ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                "`-session -before` requires a registered project file and cannot be isolated"
                    .to_string(),
                (0, Rc::from(path_string.as_str())),
            ))
            .into();
            return Err((vec![], error));
        }
        let target = match discover_repository_for_file(runtime, path_string.as_str()) {
            Ok(Some(target)) => target,
            Ok(None) => {
                let error = ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                    "`-session -before` requires a litex.config in the target file's folder"
                        .to_string(),
                    (0, Rc::from(path_string.as_str())),
                ))
                .into();
                return Err((vec![], error));
            }
            Err(error) => return Err((vec![], error)),
        };
        let (stmt_results, runtime_error) = run_repository_before_file_target(runtime, target);
        if let Some(error) = runtime_error {
            return Err((stmt_results, error));
        }
        return Ok(("project", stmt_results));
    }

    if force_isolated || !directory.join("litex.config").is_file() {
        runtime.isolated = true;
        runtime.new_file_path_new_env_new_name_scope("session");
        return Ok(("isolated", vec![]));
    }

    let root = directory.to_string_lossy().into_owned();
    runtime.isolated = false;
    if let Err(error) = discover_repository(runtime, root.as_str()) {
        return Err((vec![], error));
    }
    if let Err(error) =
        runtime.prepare_current_repository_for_repl(format!("{}/<session>", root).as_str())
    {
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
mod tests {
    use super::{
        run_session_loop_with_readers, run_session_loop_with_readers_and_preload, SessionPreload,
    };
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

    fn run_isolated_session(name: &str, input: String) -> String {
        run_isolated_session_with_style(name, input, OutputStyle::Normal)
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
    fn project_file_session_preloads_registered_prefix() {
        let root = session_test_dir("project-file-preload");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("create project fixture");
        fs::write(
            root.join("litex.config"),
            "[hierarchy]\nmodule\n\n[export]\nbefore = \"./before.lit\"\nafter = \"./after.lit\"\n",
        )
        .expect("write config");
        fs::write(root.join("before.lit"), "have planned_value R = 9\n")
            .expect("write prefix file");
        fs::write(root.join("after.lit"), "1 = 0\n").expect("write later file");

        let input = format!(
            "{}artifacts final\nclose\n",
            run_frame("use_prefix", "before::planned_value = 9\n"),
        );
        let mut stdin_reader = Cursor::new(input.into_bytes());
        let mut stdout_writer = Vec::new();
        let preload = root.join("before.lit");

        run_session_loop_with_readers_and_preload(
            &mut stdin_reader,
            &mut stdout_writer,
            &root,
            OutputStyle::Normal,
            false,
            OutputLanguage::English,
            false,
            SessionPreload::ThroughFile(preload.to_string_lossy().into_owned()),
        )
        .expect("session must run");

        let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
        assert!(output.contains("\"event\":\"ready\",\"mode\":\"project\""));
        assert!(output.contains("\"id\":\"use_prefix\",\"ok\":true"));
        assert!(output.contains("before::planned_value = 9"));
        assert!(output.contains("\"event\":\"artifacts\",\"id\":\"final\""));
        assert!(!output.contains("1 = 0"));

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn project_file_session_reports_a_failing_prefix_before_ready() {
        let root = session_test_dir("project-file-preload-failure");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("create project fixture");
        fs::write(
            root.join("litex.config"),
            "[hierarchy]\nmodule\n\n[export]\nbroken = \"./broken.lit\"\n",
        )
        .expect("write config");
        fs::write(root.join("broken.lit"), "1 = 0\n").expect("write broken prefix file");

        let mut stdin_reader = Cursor::new(b"close\n".to_vec());
        let mut stdout_writer = Vec::new();
        let preload = root.join("broken.lit");

        run_session_loop_with_readers_and_preload(
            &mut stdin_reader,
            &mut stdout_writer,
            &root,
            OutputStyle::Normal,
            false,
            OutputLanguage::English,
            false,
            SessionPreload::ThroughFile(preload.to_string_lossy().into_owned()),
        )
        .expect("session must report startup failure");

        let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
        assert!(output.contains("\"event\":\"startup_error\""));
        assert!(output.contains("\"trace\""));
        assert!(output.contains("1 = 0"));
        assert!(!output.contains("\"event\":\"ready\""));

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn project_before_file_session_skips_the_target_and_uses_its_environment() {
        let root = session_test_dir("project-before-file");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("create project fixture");
        fs::write(
            root.join("litex.config"),
            "[hierarchy]\nmodule\n\n[export]\nbefore = \"./before.lit\"\ntarget = \"./target.lit\"\nafter = \"./after.lit\"\n",
        )
        .expect("write config");
        fs::write(root.join("before.lit"), "have planned_value R = 9\n")
            .expect("write prefix file");
        fs::write(root.join("target.lit"), "    have broken_draft R = 1\n")
            .expect("write invalid draft target");
        fs::write(root.join("after.lit"), "1 = 0\n").expect("write later file");

        let input = format!(
            "{}{}{}artifacts final\nclose\n",
            run_frame("use_prefix", "before::planned_value = 9\n"),
            run_frame(
                "draft",
                "try:\n    have draft_value R = before::planned_value + 1\n",
            ),
            run_frame("use_draft", "try:\n    target::draft_value = 10\n"),
        );
        let mut stdin_reader = Cursor::new(input.into_bytes());
        let mut stdout_writer = Vec::new();
        let target = root.join("target.lit");

        run_session_loop_with_readers_and_preload(
            &mut stdin_reader,
            &mut stdout_writer,
            &root,
            OutputStyle::Normal,
            false,
            OutputLanguage::English,
            false,
            SessionPreload::BeforeFile(target.to_string_lossy().into_owned()),
        )
        .expect("session must run");

        let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
        assert!(output.contains("\"event\":\"ready\",\"mode\":\"project\""));
        assert!(output.contains("\"id\":\"use_prefix\",\"ok\":true"));
        assert!(output.contains("\"id\":\"draft\",\"ok\":true"), "{output}");
        assert!(
            output.contains("\"id\":\"use_draft\",\"ok\":true"),
            "{output}"
        );
        assert!(output.contains("\"event\":\"artifacts\",\"id\":\"final\""));
        assert!(!output.contains("unexpected indent"), "{output}");
        assert!(!output.contains("1 = 0"), "{output}");

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn project_before_file_session_reports_a_failing_predecessor() {
        let root = session_test_dir("project-before-failing-prefix");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("create project fixture");
        fs::write(
            root.join("litex.config"),
            "[hierarchy]\nmodule\n\n[export]\nbefore = \"./before.lit\"\ntarget = \"./target.lit\"\n",
        )
        .expect("write config");
        fs::write(root.join("before.lit"), "    have broken_prefix R = 1\n")
            .expect("write invalid prefix file");
        fs::write(root.join("target.lit"), "").expect("write target file");

        let mut stdin_reader = Cursor::new(b"close\n".to_vec());
        let mut stdout_writer = Vec::new();
        let target = root.join("target.lit");

        run_session_loop_with_readers_and_preload(
            &mut stdin_reader,
            &mut stdout_writer,
            &root,
            OutputStyle::Normal,
            false,
            OutputLanguage::English,
            false,
            SessionPreload::BeforeFile(target.to_string_lossy().into_owned()),
        )
        .expect("session must report startup failure");

        let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
        assert!(output.contains("\"event\":\"startup_error\""), "{output}");
        assert!(output.contains("unexpected indent"), "{output}");
        assert!(!output.contains("\"event\":\"ready\""), "{output}");

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn project_before_first_export_starts_with_an_empty_prefix() {
        let root = session_test_dir("project-before-first-export");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("create project fixture");
        fs::write(
            root.join("litex.config"),
            "[hierarchy]\nmodule\n\n[export]\ntarget = \"./target.lit\"\nafter = \"./after.lit\"\n",
        )
        .expect("write config");
        fs::write(root.join("target.lit"), "    have broken_draft R = 1\n")
            .expect("write invalid draft target");
        fs::write(root.join("after.lit"), "1 = 0\n").expect("write later file");

        let input = format!(
            "{}{}close\n",
            run_frame("draft", "try:\n    have draft_value R = 4\n"),
            run_frame("use_draft", "try:\n    target::draft_value = 4\n"),
        );
        let mut stdin_reader = Cursor::new(input.into_bytes());
        let mut stdout_writer = Vec::new();
        let target = root.join("target.lit");

        run_session_loop_with_readers_and_preload(
            &mut stdin_reader,
            &mut stdout_writer,
            &root,
            OutputStyle::Normal,
            false,
            OutputLanguage::English,
            false,
            SessionPreload::BeforeFile(target.to_string_lossy().into_owned()),
        )
        .expect("first-export session must run");

        let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
        assert!(output.contains("\"event\":\"ready\",\"mode\":\"project\""));
        assert!(output.contains("\"id\":\"draft\",\"ok\":true"), "{output}");
        assert!(
            output.contains("\"id\":\"use_draft\",\"ok\":true"),
            "{output}"
        );
        assert!(!output.contains("unexpected indent"), "{output}");
        assert!(!output.contains("1 = 0"), "{output}");

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn project_before_file_session_follows_nested_export_order() {
        let root = session_test_dir("project-before-nested");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("B")).expect("create nested project fixture");
        fs::write(
            root.join("litex.config"),
            "[hierarchy]\nmodule\n\n[export]\nroot_before = \"./root_before.lit\"\nB = \"./B\"\nroot_after = \"./root_after.lit\"\n",
        )
        .expect("write root config");
        fs::write(root.join("root_before.lit"), "have root_value R = 2\n")
            .expect("write root prefix file");
        fs::write(root.join("root_after.lit"), "1 = 0\n").expect("write root later file");
        fs::write(
            root.join("B/litex.config"),
            "[hierarchy]\nsubmodule\n\n[export]\nbefore = \"./before.lit\"\ntarget = \"./target.lit\"\nafter = \"./after.lit\"\n",
        )
        .expect("write nested config");
        fs::write(
            root.join("B/before.lit"),
            "root_before::root_value = 2\nhave nested_value R = 3\n",
        )
        .expect("write nested prefix file");
        fs::write(root.join("B/target.lit"), "    have broken_draft R = 1\n")
            .expect("write invalid nested target");
        fs::write(root.join("B/after.lit"), "1 = 0\n").expect("write nested later file");

        let input = format!(
            "{}{}artifacts final\nclose\n",
            run_frame(
                "draft",
                "try:\n    root_before::root_value = 2\n    B::before::nested_value = 3\n    have draft_value R = 4\n",
            ),
            run_frame("use_draft", "try:\n    B::target::draft_value = 4\n"),
        );
        let mut stdin_reader = Cursor::new(input.into_bytes());
        let mut stdout_writer = Vec::new();
        let target = root.join("B/target.lit");

        run_session_loop_with_readers_and_preload(
            &mut stdin_reader,
            &mut stdout_writer,
            &root,
            OutputStyle::Normal,
            false,
            OutputLanguage::English,
            false,
            SessionPreload::BeforeFile(target.to_string_lossy().into_owned()),
        )
        .expect("nested session must run");

        let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
        assert!(output.contains("\"event\":\"ready\",\"mode\":\"project\""));
        assert!(output.contains("\"id\":\"draft\",\"ok\":true"), "{output}");
        assert!(
            output.contains("\"id\":\"use_draft\",\"ok\":true"),
            "{output}"
        );
        assert!(output.contains("\"event\":\"artifacts\",\"id\":\"final\""));
        assert!(!output.contains("unexpected indent"), "{output}");
        assert!(!output.contains("1 = 0"), "{output}");

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

    #[test]
    fn session_continues_after_failed_try_parse() {
        let input = format!(
            "{}{}artifacts final\nclose\n",
            run_frame(
                "failed_try",
                "try:\n    have candidate R\n    have candidate R\n",
            ),
            run_frame("next", "have candidate R\ncandidate = candidate\n"),
        );
        let output = run_isolated_session("failed-try-parse", input);

        assert!(output.contains("\"id\":\"failed_try\",\"ok\":false"));
        assert!(output.contains("\"id\":\"next\",\"ok\":true"));
        assert!(output.contains("\"event\":\"artifacts\",\"id\":\"final\""));
        assert!(!output.contains("\"event\":\"skipped\""));
    }

    #[test]
    fn session_continues_after_failed_try_block_tokenization() {
        let input = format!(
            "{}{}close\n",
            run_frame(
                "failed_try",
                "try:\n    prop malformed:\n        1 = 1\n            2 = 2\n",
            ),
            run_frame("next", "try:\n    1 = 1\n"),
        );
        let output = run_isolated_session("failed-try-block-tokenization", input);

        assert!(output.contains("\"id\":\"failed_try\",\"ok\":false"));
        assert!(output.contains("\"id\":\"next\",\"ok\":true"));
        assert!(!output.contains("\"event\":\"skipped\""));
    }

    #[test]
    fn session_continues_after_failed_try_execution() {
        let input = format!(
            "{}{}artifacts final\nclose\n",
            run_frame("failed_try", "try:\n    clear\n"),
            run_frame("next", "have after_try R = 2\nafter_try = 2\n"),
        );
        let output = run_isolated_session("failed-try-execution", input);

        assert!(output.contains("\"id\":\"failed_try\",\"ok\":false"));
        assert!(output.contains("\"id\":\"next\",\"ok\":true"));
        assert!(output.contains("\"event\":\"artifacts\",\"id\":\"final\""));
        assert!(!output.contains("\"event\":\"skipped\""));
    }

    #[test]
    fn session_stops_after_failed_non_try_statement() {
        let input = format!(
            "{}{}artifacts final\nclose\n",
            run_frame("failed", "have ordinary R\nhave ordinary R\n"),
            run_frame("next", "1 = 1\n"),
        );
        let output = run_isolated_session("failed-non-try", input);

        assert!(output.contains("\"id\":\"failed\",\"ok\":false"));
        assert!(output.contains(
            "\"event\":\"skipped\",\"id\":\"next\",\"error\":\"an earlier block failed\""
        ));
        assert!(output.contains("\"event\":\"artifacts_unavailable\",\"id\":\"final\""));
    }

    #[test]
    fn nested_try_does_not_make_outer_statement_recoverable() {
        let input = format!(
            "{}{}close\n",
            run_frame(
                "failed_claim",
                "claim:\n    ? 1 = 1\n    try:\n        have nested R\n        have nested R\n",
            ),
            run_frame("next", "1 = 1\n"),
        );
        let output = run_isolated_session("nested-failed-try", input);

        assert!(output.contains("\"id\":\"failed_claim\",\"ok\":false"));
        assert!(output.contains(
            "\"event\":\"skipped\",\"id\":\"next\",\"error\":\"an earlier block failed\""
        ));
    }

    #[test]
    fn error_output_session_failed_try_is_detailed_in_every_style() {
        let mut failed_events = Vec::new();
        for output_style in [
            OutputStyle::Compact,
            OutputStyle::Normal,
            OutputStyle::Detailed,
        ] {
            let input = format!(
                "{}{}close\n",
                run_frame("failed_try", "try:\n    1 = 0\n"),
                run_frame("next", "try:\n    1 = 1\n"),
            );
            let output = run_isolated_session_with_style(
                format!("error-output-try-{:?}", output_style).as_str(),
                input,
                output_style,
            );

            let failed_event = output
                .lines()
                .find(|line| line.contains("\"id\":\"failed_try\""))
                .expect("session should emit the failed try event")
                .to_string();
            assert!(failed_event.contains("\"ok\":false"));
            assert!(failed_event.contains("\\\"phases\\\": {"));
            assert!(failed_event.contains("\\\"previous_error\\\":"));
            assert!(failed_event.contains("\\\"failed_goal\\\": \\\"1 = 0\\\""));
            assert!(failed_event.contains("\\\"unknown_result\\\": {"));
            assert!(output.contains("\"id\":\"next\",\"ok\":true"));
            assert!(!output.contains("\"event\":\"skipped\""));
            failed_events.push(failed_event);
        }

        assert_eq!(failed_events[0], failed_events[1]);
        assert_eq!(failed_events[1], failed_events[2]);
    }

    fn run_isolated_session_with_style(
        name: &str,
        input: String,
        output_style: OutputStyle,
    ) -> String {
        let root = session_test_dir(name);
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("create isolated fixture");

        let mut stdin_reader = Cursor::new(input.into_bytes());
        let mut stdout_writer = Vec::new();
        run_session_loop_with_readers(
            &mut stdin_reader,
            &mut stdout_writer,
            &root,
            output_style,
            false,
            OutputLanguage::English,
            false,
        )
        .expect("session must run");

        let output = String::from_utf8(stdout_writer).expect("UTF-8 output");
        let _ = fs::remove_dir_all(&root);
        output
    }
}
