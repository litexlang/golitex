use crate::new_pipeline::launch_command::parse_launch_command;
use super::run_command::run_command;
use super::run_command_outcome::RunCommandOutcome;
use crate::new_pipeline::runtime::RuntimeResult;

/// New-pipeline CLI entry: argv -> LaunchCommand -> run_command.
pub fn launch() -> RuntimeResult<RunCommandOutcome> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let command = parse_launch_command(&args)?;
    run_command(command)
}
