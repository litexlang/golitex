use crate::launch_command::LaunchCommand;
use super::run_command_outcome::RunFileResult;
use crate::run_module::run_file_with_config;
use crate::runtime::RuntimeResult;

/// `-f <file>`: directory-local `litex.config` mount when present, else isolated.
pub fn run_file(command: LaunchCommand) -> RuntimeResult<RunFileResult> {
    run_file_with_config(command)
}
