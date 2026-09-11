use crate::new_pipeline::runtime::{RuntimeError, RuntimeResult, RealOrVirtualPath, Runtime};
use std::fs;
use std::path::PathBuf;

pub fn run_file(path: PathBuf) -> RuntimeResult<()> {
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
    runtime.begin_file(RealOrVirtualPath::Real(path), false);
    if let Err(error) = runtime.run_litex_code(&source) {
        runtime.abort_file();
        return Err(error);
    }
    let (file, exec_env) = runtime.finish_file();
    runtime.publish_completed_export_file(file, exec_env);
    Ok(())
}
