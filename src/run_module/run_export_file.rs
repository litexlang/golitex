//! Run one `[export]` `.lit` file and record its ExecEnv.

use crate::module_manager::ExportFileAndItsExecEnv;
use crate::run::run_command_outcome::RunFileResult;
use crate::runtime::{CodeSource, Runtime, RuntimeError, RuntimeResult};
use std::fs;
use crate::run::source_observer::SourceObserver;

/// Run one export / standalone file under the given module context.
///
/// Source supplies the real path and root/imported export identity.
/// - `keep_env_open = true` → on success, leave the file env open (for `-session`);
///   do not finish or record
///
/// Soft failure / hard SessionError inside the file: abort env, return the
/// `RunFileResult` (caller decides FailToImport). Hard IO stays `Err`.
pub fn run_export_file(
    runtime: &mut Runtime,
    export_name: &str,
    code_source: CodeSource,
    keep_env_open: bool,
) -> RuntimeResult<RunFileResult> {
    run_export_file_observed(runtime, export_name, code_source, keep_env_open, &mut ())
}

pub fn run_export_file_observed(
    runtime: &mut Runtime,
    export_name: &str,
    code_source: CodeSource,
    keep_env_open: bool,
    observer: &mut dyn SourceObserver,
) -> RuntimeResult<RunFileResult> {
    let current_mod_id = match &code_source {
        CodeSource::ImportedExport { global_mod_id, .. } => Some(*global_mod_id),
        CodeSource::RootExport { .. } | CodeSource::Real(_) => None,
        CodeSource::Eval | CodeSource::Repl => {
            return Err(RuntimeError::InvalidArguments(
                "export source requires a real path".into(),
            ));
        }
    };
    let export_path = code_source.display_path();
    if !export_path.is_file() {
        return Err(RuntimeError::Io {
            path: export_path.to_path_buf(),
            message: "export `.lit` file not found".to_string(),
        });
    }

    let source = fs::read_to_string(&export_path).map_err(|error| RuntimeError::Io {
        path: export_path.to_path_buf(),
        message: error.to_string(),
    })?;

    runtime
        .global_module_manager
        .set_current_mod_id(current_mod_id)
        .map_err(RuntimeError::InternalBug)?;
    runtime.begin_source(code_source);

    let mut code_result = match runtime.run_litex_code_observed(&source, observer) {
        Ok(result) => result,
        Err(error) => {
            runtime.abort_source();
            let _ = runtime.global_module_manager.set_current_mod_id(None);
            return Err(error);
        }
    };
    // Capture fact-ID-backed stores and citations while the file env is live.
    code_result.attach_normal_json(runtime, "file", Some(&export_path));

    if !code_result.success {
        runtime.abort_source();
        let _ = runtime.global_module_manager.set_current_mod_id(None);
        return Ok(RunFileResult::new(export_path.to_path_buf(), code_result));
    }

    if keep_env_open {
        let _ = runtime.global_module_manager.set_current_mod_id(None);
        let _ = export_name;
        return Ok(RunFileResult::new(export_path.to_path_buf(), code_result));
    }

    let (_file, exec_env) = runtime.finish_source();
    let recorded =
        ExportFileAndItsExecEnv::new(export_name.to_string(), export_path.to_path_buf(), exec_env);
    match current_mod_id {
        None => {
            runtime.global_module_manager.record_root_export(recorded);
        }
        Some(mod_id) => {
            runtime
                .global_module_manager
                .record_imported_export(mod_id, recorded)
                .map_err(RuntimeError::InternalBug)?;
        }
    }
    let _ = runtime.global_module_manager.set_current_mod_id(None);

    Ok(RunFileResult::new(export_path.to_path_buf(), code_result))
}
