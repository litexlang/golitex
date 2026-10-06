//! Build JSON strings for a finished run.

use super::project_compact::project_run_compact;
use super::project_detailed::project_run_detailed;
use super::project_normal::project_run_normal;
use crate::run::run_command_outcome::RunLitexCodeResult;
use crate::runtime::Runtime;

/// Recognized batch commands retain their normal envelope even when execution
/// fails before a Runtime-backed result is available (tokenization, I/O, etc.).
/// Argument parsing and interactive/meta commands keep their text diagnostics.
pub fn emit_command_error(
    command: &crate::launch_command::LaunchCommand,
    error: &crate::runtime::RuntimeError,
) -> Option<String> {
    use super::helper::{bool_value, object, string};
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
                ("success", bool_value(false)),
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
                ("session_error", string(error.to_string())),
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

/// Build Detailed JSON for a code run (caller still holds Runtime for cites).
pub fn emit_run_detailed(
    run: &RunLitexCodeResult,
    runtime: &Runtime,
    target: &str,
    path: Option<&std::path::Path>,
) -> String {
    project_run_detailed(run, runtime, target, path).stringify_pretty()
}
