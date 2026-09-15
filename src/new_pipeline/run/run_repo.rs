use super::run_command_outcome::RunRepoResult;
use crate::new_pipeline::runtime::{RuntimeError, RuntimeResult};
use std::path::PathBuf;

/// Run a repository.
/// Module mount / litex.config walk is assumed elsewhere later; not defined here.
pub fn run_repo(path: PathBuf) -> RuntimeResult<RunRepoResult> {
    if path.as_os_str().is_empty() {
        return Err(RuntimeError::InvalidArguments(
            "-r requires a repository path".to_string(),
        ));
    }
    let _ = path;
    Err(RuntimeError::Unsupported(format!(
        "{} `-r` module mount is not wired yet",
        crate::new_pipeline::LITEX
    )))
}
