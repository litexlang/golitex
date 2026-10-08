//! Run a repository root by `litex.config` (`-r`).

use super::load_config::{load_config, resolve_std_root};
use super::run_export_file::run_export_file;
use super::run_import_module::{run_import_module, RunImportModuleOutcome};
use crate::launch_command::LaunchCommand;
use crate::run::run_command_outcome::{RunFileResult, RunRepoResult, RunSessionError};
use crate::run::run_repl::run_repl_loop;
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};
use std::collections::HashSet;
use std::path::PathBuf;

/// `-r <repository>`: load root config, run import modules, then root exports.
pub fn run_project(command: LaunchCommand) -> RuntimeResult<RunRepoResult> {
    let LaunchCommand::Repository { path, session, .. } = &command else {
        panic!("run_project expects LaunchCommand::Repository");
    };
    let root = path.clone();
    let session = *session;

    if root.as_os_str().is_empty() {
        return Err(RuntimeError::InvalidArguments(
            "-r requires a repository path".to_string(),
        ));
    }
    if !root.is_dir() {
        return Err(RuntimeError::Io {
            path: root,
            message: "repository path is not a directory".to_string(),
        });
    }

    let std_root = resolve_std_root(Some(&root));
    let root_config = load_config(&root, &std_root)?;

    let mut runtime = Runtime::new(command);
    // Runtime::new opens a placeholder file env for the repo path; drop it.
    runtime.abort_file();
    runtime
        .global_module_manager
        .set_root_config(root_config.clone());

    let mut done = HashSet::new();
    let mut running = HashSet::new();
    let mut file_results = Vec::new();

    for import in &root_config.imports {
        match run_import_module(
            &mut runtime,
            &import.path,
            &import.alias,
            &std_root,
            &mut done,
            &mut running,
            &mut file_results,
        )? {
            RunImportModuleOutcome::Done => {}
            RunImportModuleOutcome::SessionError(session_error) => {
                return Ok(finish_repo(
                    &runtime,
                    root,
                    file_results,
                    Some(session_error),
                ));
            }
        }
    }

    let export_count = root_config.exports.len();
    for (export_file_id, export) in root_config.exports.iter().enumerate() {
        let is_last = export_file_id + 1 == export_count;
        let keep_env_open = session && is_last;

        match run_export_file(
            &mut runtime,
            &export.name,
            &export.path,
            export_file_id,
            None,
            crate::runtime::CodeSource::RootExport { export_file_id },
            keep_env_open,
        ) {
            Ok(file_result) => {
                let failed = !file_result.run.success;
                let session_error = file_result
                    .run
                    .session_error
                    .clone()
                    .unwrap_or(RunSessionError::FailToImport);
                file_results.push(file_result);
                if failed {
                    return Ok(finish_repo(
                        &runtime,
                        root,
                        file_results,
                        Some(session_error),
                    ));
                }
                if keep_env_open {
                    if let Err(error) = run_repl_loop(&mut runtime) {
                        return Ok(finish_repo(
                            &runtime,
                            root,
                            file_results,
                            Some(RunSessionError::Runtime(error)),
                        ));
                    }
                }
            }
            Err(error) => {
                return Ok(finish_repo(
                    &runtime,
                    root,
                    file_results,
                    Some(RunSessionError::Runtime(error)),
                ));
            }
        }
    }

    Ok(finish_repo(&runtime, root, file_results, None))
}

fn finish_repo(
    runtime: &Runtime,
    root: PathBuf,
    files: Vec<RunFileResult>,
    session_error: Option<RunSessionError>,
) -> RunRepoResult {
    let mut result = RunRepoResult::new(root.clone(), files, session_error);
    result
        .run
        .attach_normal_json(runtime, "repo", Some(root.as_path()));
    result
}
