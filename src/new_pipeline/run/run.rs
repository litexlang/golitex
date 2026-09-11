use super::command::parse_cli_command;
use super::command_dispatch::{run_cli_command, DispatchOutcome};
use crate::new_pipeline::runtime::PipelineResult;

/// New-pipeline CLI entry: argv -> slim `CliCommand` -> dispatch.
///
/// Dual-track test entry. Legacy CLI remains default unless `LITEX_NEW_PIPELINE` is set.
pub fn run() -> PipelineResult<DispatchOutcome> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let command = parse_cli_command(&args)?;
    run_cli_command(command)
}
