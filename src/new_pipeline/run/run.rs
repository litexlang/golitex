use super::command::parse_cli_command;
use super::run_command::{run_command, RunCommandOutcome};
use crate::new_pipeline::runtime::RuntimeResult;

/// New-pipeline CLI entry: argv -> CliCommand -> run_command.
pub fn run() -> RuntimeResult<RunCommandOutcome> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let command = parse_cli_command(&args)?;
    run_command(command)
}
