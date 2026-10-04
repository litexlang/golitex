//! Build JSON strings for a finished run.

use super::project_compact::project_run_compact;
use super::project_detailed::project_run_detailed;
use super::project_normal::project_run_normal;
use crate::run::run_command_outcome::RunLitexCodeResult;
use crate::runtime::Runtime;

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
