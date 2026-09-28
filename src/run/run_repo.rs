use crate::launch_command::LaunchCommand;
use crate::run_module::run_project;
use super::run_command_outcome::RunRepoResult;
use crate::runtime::RuntimeResult;

/// `-r <repository>`: config-driven project run.
pub fn run_repo(command: LaunchCommand) -> RuntimeResult<RunRepoResult> {
    run_project(command)
}
