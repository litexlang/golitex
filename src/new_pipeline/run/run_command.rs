use super::command::CliCommand;
use super::run_command_outcome::{HelpResult, RunCommandOutcome, VersionResult};
use super::{run_eval, run_file, run_repl, run_repo};
use crate::new_pipeline::runtime::RuntimeResult;
use crate::new_pipeline::LITEX;

pub const NEW_PIPELINE_VERSION: &str = env!("CARGO_PKG_VERSION");

pub fn run_command(command: CliCommand) -> RuntimeResult<RunCommandOutcome> {
    match command {
        CliCommand::Help => {
            let entries = print_help_message();
            Ok(RunCommandOutcome::Help(HelpResult::new(entries)))
        }
        CliCommand::Version => {
            println!("{} {}", LITEX, NEW_PIPELINE_VERSION);
            Ok(RunCommandOutcome::Version(VersionResult::new(
                NEW_PIPELINE_VERSION,
            )))
        }
        CliCommand::Repl => {
            run_repl::run_repl()?;
            Ok(RunCommandOutcome::RunRepl)
        }
        CliCommand::Eval(code) => {
            let result = run_eval::run_eval(code)?;
            Ok(RunCommandOutcome::RunEval(result))
        }
        CliCommand::File(path) => {
            let result = run_file::run_file(path)?;
            Ok(RunCommandOutcome::RunFile(result))
        }
        CliCommand::Repository(path) => {
            let result = run_repo::run_repo(path)?;
            Ok(RunCommandOutcome::RunRepo(result))
        }
    }
}

fn print_help_message() -> Vec<String> {
    let bin = LITEX.to_ascii_lowercase();
    let entries = vec![
        format!("{} (test track)", LITEX),
        format!("LITEX_NEW_PIPELINE=1 {}", bin),
        format!("LITEX_NEW_PIPELINE=1 {} -e <code>", bin),
        format!("LITEX_NEW_PIPELINE=1 {} -f <file>", bin),
        format!("LITEX_NEW_PIPELINE=1 {} -r <repository>", bin),
        format!("LITEX_NEW_PIPELINE=1 {} -help", bin),
        format!("LITEX_NEW_PIPELINE=1 {} -version", bin),
        "Without LITEX_NEW_PIPELINE, the legacy CLI is used.".to_string(),
    ];
    println!("{}", entries[0]);
    println!();
    println!("Usage:");
    for entry in &entries[1..7] {
        println!("  {}", entry);
    }
    println!();
    println!("{}", entries[7]);
    entries
}
