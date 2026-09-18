//! Run one imported module package (recursive imports, then exports).

use super::load_config::{load_config, normalize_module_dir};
use super::run_export_file::run_export_file;
use crate::new_pipeline::run::run_command_outcome::{RunFileResult, RunSessionError};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use std::collections::HashSet;
use std::path::{Path, PathBuf};

/// Outcome of running an imported module subtree.
pub enum RunImportModuleOutcome {
    Done,
    /// Soft Failed / missing dep / cycle / mount fail while importing.
    SessionError(RunSessionError),
}

/// Run an imported module directory.
///
/// Config import order: recurse each dep first (missing/broken → FailToImport).
/// Then mount this module and run its exports in config order.
/// Soft Failed on an export → FailToImport (file result already pushed).
pub fn run_import_module(
    runtime: &mut Runtime,
    module_dir: &Path,
    alias: &str,
    std_root: &Path,
    done: &mut HashSet<PathBuf>,
    running: &mut HashSet<PathBuf>,
    file_results: &mut Vec<RunFileResult>,
) -> RuntimeResult<RunImportModuleOutcome> {
    let key = normalize_module_dir(module_dir);
    if done.contains(&key) {
        return Ok(RunImportModuleOutcome::Done);
    }
    if running.contains(&key) {
        return Ok(RunImportModuleOutcome::SessionError(
            RunSessionError::FailToImport,
        ));
    }
    if !key.is_dir() {
        return Ok(RunImportModuleOutcome::SessionError(
            RunSessionError::FailToImport,
        ));
    }

    running.insert(key.clone());

    let config = match load_config(&key, std_root) {
        Ok(config) => config,
        Err(error) => {
            running.remove(&key);
            return Ok(RunImportModuleOutcome::SessionError(
                RunSessionError::Runtime(error),
            ));
        }
    };

    for import in &config.imports {
        match run_import_module(
            runtime,
            &import.path,
            &import.alias,
            std_root,
            done,
            running,
            file_results,
        )? {
            RunImportModuleOutcome::Done => {}
            outcome @ RunImportModuleOutcome::SessionError(_) => {
                running.remove(&key);
                return Ok(outcome);
            }
        }
    }

    let mod_id = match runtime.global_module_manager.mount_module(
        alias.to_string(),
        key.clone(),
        config.clone(),
    ) {
        Ok(mod_id) => mod_id,
        Err(_) => {
            running.remove(&key);
            return Ok(RunImportModuleOutcome::SessionError(
                RunSessionError::FailToImport,
            ));
        }
    };

    let exports = runtime.global_module_manager.imports()[mod_id]
        .litex_config
        .exports
        .clone();

    for (export_file_id, export) in exports.iter().enumerate() {
        let file_result = match run_export_file(
            runtime,
            &export.name,
            &export.path,
            export_file_id,
            Some(mod_id),
            false,
        ) {
            Ok(file_result) => file_result,
            Err(error) => {
                running.remove(&key);
                return Ok(RunImportModuleOutcome::SessionError(
                    RunSessionError::Runtime(error),
                ));
            }
        };
        let failed = !file_result.run.success;
        file_results.push(file_result);
        if failed {
            running.remove(&key);
            return Ok(RunImportModuleOutcome::SessionError(
                RunSessionError::FailToImport,
            ));
        }
    }

    running.remove(&key);
    done.insert(key);
    Ok(RunImportModuleOutcome::Done)
}
