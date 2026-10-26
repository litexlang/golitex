//! Run a repository root by `litex.config` (`-r`).

use super::load_config::{load_config, resolve_std_root};
use super::run_export_file::run_export_file_observed;
use super::run_import_module::{run_import_module_observed, RunImportModuleOutcome};
use crate::launch_command::LaunchCommand;
use crate::run::run_command_outcome::{
    RunFileResult, RunLitexCodeResult, RunRepoResult, RunSessionError,
};
use crate::run::run_repl::run_repl_loop;
use crate::run::source_observer::SourceObserver;
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};
use std::collections::HashSet;
use std::path::PathBuf;

/// `-r <repository>`: load root config, run import modules, then root exports.
pub fn run_project(command: LaunchCommand) -> RuntimeResult<RunRepoResult> {
    run_project_observed(command, &mut ())
}

pub fn run_project_observed(
    command: LaunchCommand,
    observer: &mut dyn SourceObserver,
) -> RuntimeResult<RunRepoResult> {
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
    runtime.abort_source();
    runtime
        .global_module_manager
        .set_root_config(root_config.clone());

    let mut done = HashSet::new();
    let mut running = HashSet::new();
    let mut file_results = Vec::new();
    // `Some` only after the target export opens the interactive Session. Its
    // final snapshot then merges every export file with all REPL turns.
    let mut session_turns: Option<Vec<RunLitexCodeResult>> = None;

    for import in &root_config.imports {
        match run_import_module_observed(
            &mut runtime,
            &import.path,
            &import.alias,
            &std_root,
            &mut done,
            &mut running,
            &mut file_results,
            observer,
        )? {
            RunImportModuleOutcome::Done => {}
            RunImportModuleOutcome::SessionError(mut session_error) => {
                if let RunSessionError::FailToImport(failure) = &mut session_error {
                    failure.prepend(&root);
                }
                return Ok(finish_repo(
                    &runtime,
                    root,
                    file_results,
                    Some(session_error),
                    None,
                ));
            }
        }
    }

    runtime
        .global_module_manager
        .validate_alias_targets(&root_config)
        .map_err(RuntimeError::InvalidArguments)?;

    let export_count = root_config.exports.len();
    for (export_file_id, export) in root_config.exports.iter().enumerate() {
        let is_last = export_file_id + 1 == export_count;
        let keep_env_open = session && is_last;

        match run_export_file_observed(
            &mut runtime,
            &export.name,
            crate::runtime::CodeSource::RootExport {
                path: export.path.clone(),
                export_file_id,
            },
            keep_env_open,
            observer,
        ) {
            Ok(file_result) => {
                let failed = !file_result.run.success;
                let session_error = file_result.mount_error();
                file_results.push(file_result);
                if failed {
                    return Ok(finish_repo(
                        &runtime,
                        root,
                        file_results,
                        Some(session_error),
                        None,
                    ));
                }
                if keep_env_open {
                    let turns = session_turns.get_or_insert_with(Vec::new);
                    let repl = run_repl_loop(&mut runtime, turns);
                    if let Some(last) = file_results.last_mut() {
                        last.run.attach_normal_json_with_repl_turns(
                            &runtime,
                            turns,
                            "file",
                            Some(last.path.as_path()),
                        );
                    }
                    match repl {
                        // Keep the live env until finish_repo has rendered
                        // citations for the full Session snapshot.
                        Ok(()) => {}
                        Err(error) => {
                            let result = finish_repo(
                                &runtime,
                                root,
                                file_results,
                                Some(RunSessionError::Runtime(error)),
                                session_turns.as_deref(),
                            );
                            runtime.abort_source();
                            return Ok(result);
                        }
                    }
                }
            }
            Err(error) => {
                return Ok(finish_repo(
                    &runtime,
                    root,
                    file_results,
                    Some(RunSessionError::Runtime(error)),
                    None,
                ));
            }
        }
    }

    let result = finish_repo(&runtime, root, file_results, None, session_turns.as_deref());
    if session_turns.is_some() {
        runtime.abort_source();
    }
    Ok(result)
}

fn finish_repo(
    runtime: &Runtime,
    root: PathBuf,
    files: Vec<RunFileResult>,
    session_error: Option<RunSessionError>,
    session_turns: Option<&[RunLitexCodeResult]>,
) -> RunRepoResult {
    let mut result = RunRepoResult::new(root.clone(), files, session_error);
    let json = match session_turns {
        Some(turns) => crate::json_output::emit_run_normal_with_files_and_turns(
            &result.run,
            &result.files,
            turns,
            runtime,
            "repo",
            Some(root.as_path()),
        ),
        None => {
            crate::json_output::emit_run_normal(&result.run, runtime, "repo", Some(root.as_path()))
        }
    };
    result.run.normal_json = Some(json);
    result
}
