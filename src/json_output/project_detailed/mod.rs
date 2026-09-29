//! Detailed JSON projection.
//!
//! Full IR projector sources live beside this file but are unwired until they
//! match current Exec/Verify result types. Entry points fall back to Normal so
//! release/CLI builds stay green.

use crate::execute::ExecStmtResult;
use crate::json_output::project_normal::{project_run_normal, project_stmt_normal};
use crate::knowledge_base::JsonValue;
use crate::run::run_command_outcome::RunLitexCodeResult;
use crate::runtime::Runtime;
use std::path::Path;

pub fn project_stmt_detailed(result: &ExecStmtResult, runtime: &Runtime) -> JsonValue {
    project_stmt_normal(result, runtime)
}

pub fn project_run_detailed(
    run: &RunLitexCodeResult,
    runtime: &Runtime,
    target: &str,
    path: Option<&Path>,
) -> JsonValue {
    project_run_normal(run, runtime, target, path)
}
