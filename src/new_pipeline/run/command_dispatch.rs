use super::command::CliCommand;
use super::run_litex_code::run_litex_code;
use crate::new_pipeline::runtime::PipelineResult;

pub const NEW_PIPELINE_VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Debug)]
pub enum DispatchOutcome {
    Ran,
    Help,
    Version,
}

pub fn run_cli_command(command: CliCommand) -> PipelineResult<DispatchOutcome> {
    match command {
        CliCommand::Help => {
            print_help_message();
            Ok(DispatchOutcome::Help)
        }
        CliCommand::Version => {
            println!("litex new_pipeline {}", NEW_PIPELINE_VERSION);
            Ok(DispatchOutcome::Version)
        }
        CliCommand::Eval(_) | CliCommand::File(_) | CliCommand::Repository(_) => {
            run_litex_code(command)?;
            Ok(DispatchOutcome::Ran)
        }
    }
}

fn print_help_message() {
    println!("litex new_pipeline (test track)");
    println!();
    println!("Usage:");
    println!("  LITEX_NEW_PIPELINE=1 litex -e <code>");
    println!("  LITEX_NEW_PIPELINE=1 litex -f <file>");
    println!("  LITEX_NEW_PIPELINE=1 litex -r <repository>");
    println!("  LITEX_NEW_PIPELINE=1 litex -help");
    println!("  LITEX_NEW_PIPELINE=1 litex -version");
    println!();
    println!("Without LITEX_NEW_PIPELINE, the legacy CLI is used.");
}
