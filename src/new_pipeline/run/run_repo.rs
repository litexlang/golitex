use crate::new_pipeline::launch_command::LaunchCommand;
use super::run_command_outcome::RunRepoResult;
use crate::new_pipeline::runtime::{RuntimeError, RuntimeResult};

/// Run a repository.
/// Module mount / litex.config walk is assumed elsewhere later; not defined here.
/// `session` will keep the last export env and enter REPL once mount exists.
pub fn run_repo(command: LaunchCommand) -> RuntimeResult<RunRepoResult> {
    let LaunchCommand::Repository { path, .. } = &command else {
        panic!("run_repo expects LaunchCommand::Repository");
    };
    if path.as_os_str().is_empty() {
        return Err(RuntimeError::InvalidArguments(
            "-r requires a repository path".to_string(),
        ));
    }
    let _ = command;
    Err(RuntimeError::Unsupported(format!(
        "{} `-r` module mount is not wired yet",
        crate::new_pipeline::LITEX
    )))
}
