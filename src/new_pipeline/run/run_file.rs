use super::run_command_outcome::RunFileResult;
use crate::new_pipeline::runtime::{RealOrVirtualPath, Runtime, RuntimeError, RuntimeResult};
use std::fs;
use std::path::PathBuf;

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
    runtime.begin_file(RealOrVirtualPath::Real(path.clone()), false);
    let code_result = match runtime.run_litex_code(&source) {
        Ok(result) => result,
        Err(error) => {
            runtime.abort_file();
            return Err(error);
        }
    };

    if code_result.all_stmts_succeeded {
        let (file, exec_env) = runtime.finish_file();
        runtime.publish_completed_export_file(file, exec_env);
    } else {
        runtime.abort_file();
    }

    Ok(RunFileResult::from_code_result(path, code_result))
}
