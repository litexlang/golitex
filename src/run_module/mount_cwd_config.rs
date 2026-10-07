//! Mount cwd `litex.config` for `-e` / bare REPL (missing → empty / no-op).

use super::load_config::{load_config_or_empty, resolve_std_root};
use super::run_export_file::run_export_file_with_graph;
use super::run_import_module::{run_import_module_with_graph, RunImportModuleOutcome};
use crate::run::run_command_outcome::RunSessionError;
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};
use std::collections::HashSet;
use std::path::PathBuf;

/// Outcome of mounting the current working directory's project config.
pub enum MountCwdConfigOutcome {
    /// No config, or all imports/exports mounted successfully.
    Done,
    /// Soft fail / missing dep / cycle / IO while mounting.
    SessionError(RunSessionError),
}

/// Load `cwd/litex.config` (missing → empty) and mount imports + all exports.
///
/// Caller must ensure there is **no** live file env (e.g. after `abort_file`).
/// On success the runtime has no open file env; caller opens Eval/Repl after.
pub fn mount_cwd_config(runtime: &mut Runtime) -> RuntimeResult<MountCwdConfigOutcome> {
    mount_cwd_config_with_graph(runtime, None)
}

pub(crate) fn mount_cwd_config_with_graph(runtime: &mut Runtime, mut graph: Option<&mut crate::graph::MathGraph>) -> RuntimeResult<MountCwdConfigOutcome> {
    let cwd = std::env::current_dir().map_err(|error| RuntimeError::Io {
        path: PathBuf::from("."),
        message: error.to_string(),
    })?;
    let std_root = resolve_std_root(Some(&cwd));
    let config = load_config_or_empty(&cwd, &std_root)?;

    if config.imports.is_empty() && config.exports.is_empty() {
        return Ok(MountCwdConfigOutcome::Done);
    }

    runtime
        .global_module_manager
        .set_root_config(config.clone());

    let mut done = HashSet::new();
    let mut running = HashSet::new();
    let mut file_results = Vec::new();

    for import in &config.imports {
        match run_import_module_with_graph(
            runtime,
            &import.path,
            &import.alias,
            &std_root,
            &mut done,
            &mut running,
            &mut file_results,
            graph.as_deref_mut(),
        )? {
            RunImportModuleOutcome::Done => {}
            RunImportModuleOutcome::SessionError(session_error) => {
                return Ok(MountCwdConfigOutcome::SessionError(session_error));
            }
        }
    }

    for (export_file_id, export) in config.exports.iter().enumerate() {
        match run_export_file_with_graph(
            runtime,
            &export.name,
            &export.path,
            export_file_id,
            None,
            crate::runtime::CodeSource::RootExport { export_file_id },
            false,
            graph.as_deref_mut(),
        ) {
            Ok(file_result) => {
                if !file_result.run.success {
                    return Ok(MountCwdConfigOutcome::SessionError(
                        file_result.run.session_error.unwrap_or(RunSessionError::FailToImport),
                    ));
                }
            }
            Err(error) => {
                return Ok(MountCwdConfigOutcome::SessionError(
                    RunSessionError::Runtime(error),
                ));
            }
        }
    }

    Ok(MountCwdConfigOutcome::Done)
}
