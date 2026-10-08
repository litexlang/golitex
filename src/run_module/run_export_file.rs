//! Run one `[export]` `.lit` file and record its ExecEnv.

use crate::module_manager::ExportFileAndItsExecEnv;
use crate::run::run_command_outcome::RunFileResult;
use crate::runtime::{CodeSource, RealOrVirtualPath, Runtime, RuntimeError, RuntimeResult};
use std::fs;
use std::path::Path;

/// Run one export / standalone file under the given module context.
///
/// - `current_mod_id = None` → root record path (`record_root_export`) when finishing
/// - `current_mod_id = Some(i)` → imported record path (`record_imported_export`)
/// - `code_source` → live outermost-symbol qualification
/// - `keep_env_open = true` → on success, leave the file env open (for `-session`);
///   do not finish or record
///
/// Soft failure / hard SessionError inside the file: abort env, return the
/// `RunFileResult` (caller decides FailToImport). Hard IO stays `Err`.
pub fn run_export_file(
    runtime: &mut Runtime,
    export_name: &str,
    export_path: &Path,
    export_file_id: usize,
    current_mod_id: Option<usize>,
    code_source: CodeSource,
    keep_env_open: bool,
) -> RuntimeResult<RunFileResult> {
    if !export_path.is_file() {
        return Err(RuntimeError::Io {
            path: export_path.to_path_buf(),
            message: "export `.lit` file not found".to_string(),
        });
    }

    let source = fs::read_to_string(export_path).map_err(|error| RuntimeError::Io {
        path: export_path.to_path_buf(),
        message: error.to_string(),
    })?;

    runtime
        .global_module_manager
        .set_current_mod_id(current_mod_id)
        .map_err(RuntimeError::InternalBug)?;
    let _ = export_file_id;
    runtime.set_code_source(code_source);
    runtime.begin_file(RealOrVirtualPath::Real(export_path.to_path_buf()));

    let mut code_result = match runtime.run_litex_code(&source) {
        Ok(result) => result,
        Err(error) => {
            runtime.abort_file();
            let _ = runtime.global_module_manager.set_current_mod_id(None);
            return Err(error);
        }
    };
    // Capture fact-ID-backed stores and citations while the file env is live.
    code_result.attach_normal_json(runtime, "file", Some(export_path));

    if !code_result.success {
        runtime.abort_file();
        let _ = runtime.global_module_manager.set_current_mod_id(None);
        return Ok(RunFileResult::new(export_path.to_path_buf(), code_result));
    }

    if keep_env_open {
        let _ = runtime.global_module_manager.set_current_mod_id(None);
        let _ = export_name;
        return Ok(RunFileResult::new(export_path.to_path_buf(), code_result));
    }

    let (_file, exec_env) = runtime.finish_file();
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
