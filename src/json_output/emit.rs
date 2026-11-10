//! Build JSON strings for a finished run.

use super::project_compact::project_run_compact;
use super::project_detailed::project_run_detailed;
use super::project_normal::{
    project_run_normal, project_run_normal_with_files_and_turns, project_run_normal_with_turns,
};
use crate::run::run_command_outcome::{RunFileResult, RunLitexCodeResult};
use crate::runtime::Runtime;

/// Recognized batch commands retain their normal envelope even when execution
/// fails before a Runtime-backed result is available (tokenization, I/O, etc.).
/// Argument parsing and interactive/meta commands keep their text diagnostics.
pub fn emit_command_error(
    command: &crate::launch_command::LaunchCommand,
    error: &crate::runtime::RuntimeError,
) -> Option<String> {
    use super::helper::{object, run_result_value, runtime_termination_value, string};
    use crate::launch_command::LaunchCommand;

    let (target, path) = match command {
        LaunchCommand::Eval { .. } => ("eval", None),
        LaunchCommand::File { path, .. } => ("file", Some(path)),
        LaunchCommand::Repository { path, .. } => ("repo", Some(path)),
        LaunchCommand::ExtractExecutableCode {
            target,
            input,
            language,
        } => {
            return Some(
                crate::run::run_extract_executable_code::extract_command_error_json(
                    target, input, *language, error,
                ),
            );
        }
        LaunchCommand::CompileToLatex {
            input, language, ..
        } => {
            return Some(crate::run::run_compile_to_latex::latex_command_error_json(
                input, *language, error,
            ));
        }
        _ => return None,
    };
    let language = command.output_language();
    Some(
        object(
            language,
            vec![
                ("kind", string("run")),
                ("run_result", run_result_value(false)),
                ("target", string(target)),
                (
                    "path",
                    path.map(|p| string(p.display().to_string()))
                        .unwrap_or(crate::knowledge_base::JsonValue::Null),
                ),
                ("detail", string("normal")),
                ("language", string(language.as_str())),
                (
                    "statement_results",
                    crate::knowledge_base::JsonValue::Array(Vec::new()),
                ),
                (
                    "errors",
                    crate::knowledge_base::JsonValue::Array(Vec::new()),
                ),
                (
                    "session_terminated",
                    crate::knowledge_base::JsonValue::Bool(true),
                ),
                ("termination", runtime_termination_value(error, language)),
            ],
        )
        .stringify_pretty(),
    )
}

/// Build Compact JSON for a code run (caller still holds Runtime for cites).
pub fn emit_run_compact(
    run: &RunLitexCodeResult,
    runtime: &Runtime,
    target: &str,
    path: Option<&std::path::Path>,
) -> String {
    project_run_compact(run, runtime, target, path).stringify_pretty()
}

/// Build Normal JSON for a code run (caller still holds Runtime for cites).
pub fn emit_run_normal(
    run: &RunLitexCodeResult,
    runtime: &Runtime,
    target: &str,
    path: Option<&std::path::Path>,
) -> String {
    project_run_normal(run, runtime, target, path).stringify_pretty()
}

/// Build Normal JSON for an initial batch plus later REPL turns.
pub fn emit_run_normal_with_turns(
    run: &RunLitexCodeResult,
    turns: &[RunLitexCodeResult],
    runtime: &Runtime,
    target: &str,
    path: Option<&std::path::Path>,
) -> String {
    project_run_normal_with_turns(run, turns, runtime, target, path).stringify_pretty()
}

/// Build the final `-r -session` Normal JSON: every export file plus later REPL turns.
pub fn emit_run_normal_with_files_and_turns(
    run: &RunLitexCodeResult,
    files: &[RunFileResult],
    turns: &[RunLitexCodeResult],
    runtime: &Runtime,
    target: &str,
    path: Option<&std::path::Path>,
) -> String {
    project_run_normal_with_files_and_turns(run, files, turns, runtime, target, path)
        .stringify_pretty()
}

/// Build Detailed JSON for a code run (caller still holds Runtime for cites).
pub fn emit_run_detailed(
    run: &RunLitexCodeResult,
    runtime: &Runtime,
    target: &str,
    path: Option<&std::path::Path>,
) -> String {
    project_run_detailed(run, runtime, target, path).stringify_pretty()
}

/// Select the verification view for the current runner; Detailed remains an
/// explicit consumer of retained evidence.
pub(crate) fn emit_run_feedback(
    run: &RunLitexCodeResult,
    files: &[RunFileResult],
    turns: &[RunLitexCodeResult],
    runtime: &Runtime,
    target: &str,
    path: Option<&std::path::Path>,
) -> String {
    use crate::result_detail::OutputDetail;
    if runtime.result_detail() == OutputDetail::Compact {
        let runs = std::iter::once(run)
            .chain(files.iter().map(|file| &file.run))
            .chain(turns)
            .collect::<Vec<_>>();
        return super::project_compact::project_compact_runs(run, &runs, runtime, path)
            .stringify_pretty();
    }
    if files.is_empty() {
        emit_run_normal_with_turns(run, turns, runtime, target, path)
    } else {
        emit_run_normal_with_files_and_turns(run, files, turns, runtime, target, path)
    }
}

pub fn emit_compact_command_error(
    command: &crate::launch_command::LaunchCommand,
    error: &crate::runtime::RuntimeError,
) -> String {
    use crate::launch_command::LaunchCommand;
    let path = match command {
        LaunchCommand::File { path, .. } | LaunchCommand::Repository { path, .. } => {
            Some(path.as_path())
        }
        _ => None,
    };
    let lang = command.output_language();
    super::project_compact::verdict(
        false,
        vec![super::feedback::runtime_error(error, path, lang)],
        lang,
    )
    .stringify_pretty()
}

pub(crate) fn append_compact_session_error(
    previous: Option<&str>,
    error: &crate::run::RunSessionError,
    path: Option<&std::path::Path>,
    runtime: &Runtime,
) -> String {
    use crate::knowledge_base::JsonValue;
    let lang = super::helper::output_language(runtime);
    let mut errors = previous
        .and_then(|json| JsonValue::parse(json).ok())
        .and_then(|json| {
            json.as_object()
                .ok()?
                .get(&super::json_keys::localize_key("errors", lang))?
                .as_array()
                .ok()
                .map(<[JsonValue]>::to_vec)
        })
        .unwrap_or_default();
    errors.extend(super::feedback::session_errors(error, path, lang));
    super::project_compact::verdict(false, errors, lang).stringify_pretty()
}
