//! Build Normal JSON strings for a finished run.

use super::project_normal::project_run_normal;
use crate::knowledge_base::JsonValue;
use crate::run::run_command_outcome::RunLitexCodeResult;
use crate::runtime::Runtime;

/// Build Normal JSON for a code run (caller still holds Runtime for cites).
pub fn emit_run_normal(
    run: &RunLitexCodeResult,
    runtime: &Runtime,
    target: &str,
    path: Option<&std::path::Path>,
) -> String {
    project_run_normal(run, runtime, target, path).stringify_pretty()
}

/// Convenience: pretty-print one JsonValue.
pub fn stringify_normal(value: &JsonValue) -> String {
    value.stringify_pretty()
}
