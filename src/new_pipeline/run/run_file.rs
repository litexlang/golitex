use super::run_command_outcome::RunFileResult;
use crate::new_pipeline::runtime::{RealOrVirtualPath, Runtime, RuntimeError, RuntimeResult};
use std::fs;
use std::path::PathBuf;

/// Run one file.
/// Module mount / litex.config preload is assumed elsewhere later; not defined here.
pub fn run_file(path: PathBuf) -> RuntimeResult<RunFileResult> {
    if path.as_os_str().is_empty() {
        return Err(RuntimeError::InvalidArguments(
            "-f requires a source file".to_string(),
        ));
    }

    let source = fs::read_to_string(&path).map_err(|error| RuntimeError::Io {
        path: path.clone(),
        message: error.to_string(),
    })?;

    let mut runtime = Runtime::new();
    // Pretend module mount already succeeded with an empty context.
    runtime.begin_file(RealOrVirtualPath::Real(path.clone()));
    let code_result = match runtime.run_litex_code(&source) {
        Ok(result) => result,
        Err(error) => {
            runtime.abort_file();
            return Err(error);
        }
    };

    if code_result.success {
        let (file, exec_env) = runtime.finish_file();
        runtime.publish_completed_export_file(file, exec_env);
    } else {
        runtime.abort_file();
    }

    Ok(RunFileResult::new(path, code_result))
}
