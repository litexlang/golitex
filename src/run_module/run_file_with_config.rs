//! Project-aware `-f`: optional `litex.config` mount, then the target file.

use super::load_config::{load_config_or_empty, resolve_std_root};
use super::run_export_file::run_export_file;
use super::run_import_module::{run_import_module, RunImportModuleOutcome};
use crate::launch_command::LaunchCommand;
use crate::module_manager::LitexConfigExport;
use crate::run::run_command_outcome::{
    RunFileResult, RunLitexCodeResult, RunSessionError,
};
use crate::run::run_repl::run_repl_loop;
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

/// `-f <file>` with directory-local `litex.config` (no parent search).
///
/// - no config → isolated run (same as bare `-f`)
/// - target in `[export]` → imports + exports up to and including target
/// - target not in `[export]` → all imports + all exports, then target as extra file
/// - mount soft fail → `FailToImport`; target soft fail → normal file failure
pub fn run_file_with_config(command: LaunchCommand) -> RuntimeResult<RunFileResult> {
    let LaunchCommand::File { path, session, .. } = &command else {
        panic!("run_file_with_config expects LaunchCommand::File");
    };
    let path = path.clone();
    let session = *session;

    if path.as_os_str().is_empty() {
        return Err(RuntimeError::InvalidArguments(
            "-f requires a source file".to_string(),
        ));
    }
    if !path.is_file() {
        return Err(RuntimeError::Io {
            path: path.clone(),
            message: "source file not found".to_string(),
        });
    }

    let module_dir = module_dir_of(&path);
    let std_root = resolve_std_root(Some(&module_dir));
    let config = load_config_or_empty(&module_dir, &std_root)?;

    if config.imports.is_empty() && config.exports.is_empty() {
        return run_file_isolated(command, path, session);
    }

    let export_index = find_export_index(&config.exports, &path);

    let mut runtime = Runtime::new(command);
    runtime.abort_file();
    runtime
        .global_module_manager
        .set_root_config(config.clone());

    let mut done = HashSet::new();
    let mut running = HashSet::new();
    let mut mount_files = Vec::new();

    for import in &config.imports {
        match run_import_module(
            &mut runtime,
            &import.path,
            &import.alias,
            &std_root,
            &mut done,
            &mut running,
            &mut mount_files,
        )? {
            RunImportModuleOutcome::Done => {}
            RunImportModuleOutcome::SessionError(session_error) => {
                return Ok(fail_to_import_result(&runtime, path, session_error));
            }
        }
    }

    let export_limit = match export_index {
        Some(index) => index + 1,
        None => config.exports.len(),
    };

    for (export_file_id, export) in config.exports.iter().enumerate().take(export_limit) {
        let is_target = export_index == Some(export_file_id);
        let keep_env_open = session && is_target;

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
                if !file_result.run.success {
                    if is_target {
                        return Ok(file_result_with_json(&runtime, path, file_result.run));
                    }
                    return Ok(fail_to_import_result(
                        &runtime,
                        path,
                        file_result.run.session_error.unwrap_or(RunSessionError::FailToImport),
                    ));
                }
                if is_target {
                    if keep_env_open {
                        if let Err(error) = run_repl_loop(&mut runtime) {
                            return Ok(file_result_with_json(
                                &runtime,
                                path,
                                RunLitexCodeResult::new(
                                    file_result.run.statement_results,
                                    Some(RunSessionError::Runtime(error)),
                                ),
                            ));
                        }
                    }
                    return Ok(file_result_with_json(&runtime, path, file_result.run));
                }
            }
            Err(error) => {
                return Ok(fail_to_import_result(
                    &runtime,
                    path,
                    RunSessionError::Runtime(error),
                ));
            }
        }
    }

    // Target is not in [export]: run it as an extra file after full mount.
    let export_name = export_name_for_path(&path);
    let export_file_id = config.exports.len();
    match run_export_file(
        &mut runtime,
        &export_name,
        &path,
        export_file_id,
        None,
        crate::runtime::CodeSource::StandaloneFile,
        session,
    ) {
        Ok(file_result) => {
            if !file_result.run.success {
                return Ok(file_result_with_json(&runtime, path, file_result.run));
            }
            if session {
                if let Err(error) = run_repl_loop(&mut runtime) {
                    return Ok(file_result_with_json(
                        &runtime,
                        path,
                        RunLitexCodeResult::new(
                            file_result.run.statement_results,
                            Some(RunSessionError::Runtime(error)),
                        ),
                    ));
                }
            }
            Ok(file_result_with_json(&runtime, path, file_result.run))
        }
        Err(error) => Err(error),
    }
}

fn run_file_isolated(
    command: LaunchCommand,
    path: PathBuf,
    session: bool,
) -> RuntimeResult<RunFileResult> {
    let source = fs::read_to_string(&path).map_err(|error| RuntimeError::Io {
        path: path.clone(),
        message: error.to_string(),
    })?;

    let mut runtime = Runtime::new(command);
    let mut code_result = match runtime.run_litex_code(&source) {
        Ok(result) => result,
        Err(error) => {
            runtime.abort_file();
            return Err(error);
        }
    };
    code_result.attach_normal_json(&runtime, "file", Some(path.as_path()));

    if !code_result.success {
        runtime.abort_file();
        return Ok(RunFileResult::new(path, code_result));
    }

    if session {
        run_repl_loop(&mut runtime)?;
        return Ok(RunFileResult::new(path, code_result));
    }

    let (file, exec_env) = runtime.finish_file();
    runtime.publish_completed_export_file(file, exec_env);
    Ok(RunFileResult::new(path, code_result))
}

fn file_result_with_json(
    runtime: &Runtime,
    path: PathBuf,
    mut run: RunLitexCodeResult,
) -> RunFileResult {
    run.attach_normal_json(runtime, "file", Some(path.as_path()));
    RunFileResult::new(path, run)
}

fn fail_to_import_result(
    runtime: &Runtime,
    path: PathBuf,
    session_error: RunSessionError,
) -> RunFileResult {
    file_result_with_json(
        runtime,
        path,
        RunLitexCodeResult::new(Vec::new(), Some(session_error)),
    )
}

fn module_dir_of(path: &Path) -> PathBuf {
    match path.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent.to_path_buf(),
        _ => PathBuf::from("."),
    }
}

fn find_export_index(exports: &[LitexConfigExport], target: &Path) -> Option<usize> {
    exports
        .iter()
        .position(|export| same_path(&export.path, target))
}

fn same_path(left: &Path, right: &Path) -> bool {
    match (left.canonicalize(), right.canonicalize()) {
        (Ok(a), Ok(b)) => a == b,
        _ => left == right,
    }
}

fn export_name_for_path(path: &Path) -> String {
    path.file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or("file")
        .to_string()
}
