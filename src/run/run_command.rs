use crate::launch_command::LaunchCommand;
use super::run_command_outcome::{HelpResult, RunCommandOutcome, VersionResult};
use super::{run_eval, run_file, run_repl, run_repo};
use crate::runtime::RuntimeResult;
use crate::LITEX;

pub const NEW_PIPELINE_VERSION: &str = env!("CARGO_PKG_VERSION");

pub fn run_command(command: LaunchCommand) -> RuntimeResult<RunCommandOutcome> {
    match command {
        LaunchCommand::Help => {
            let entries = print_help_message();
            Ok(RunCommandOutcome::Help(HelpResult::new(entries)))
        }
        LaunchCommand::Version => {
            println!("{} {}", LITEX, NEW_PIPELINE_VERSION);
            Ok(RunCommandOutcome::Version(VersionResult::new(
                NEW_PIPELINE_VERSION,
            )))
        }
        command @ LaunchCommand::Repl { .. } => {
            run_repl::run_repl(command)?;
            Ok(RunCommandOutcome::RunRepl)
        }
        command @ LaunchCommand::Eval { .. } => {
            let result = run_eval::run_eval(command)?;
            Ok(RunCommandOutcome::RunEval(result))
        }
        command @ LaunchCommand::File { .. } => {
            let result = run_file::run_file(command)?;
            Ok(RunCommandOutcome::RunFile(result))
        }
        command @ LaunchCommand::Repository { .. } => {
            let result = run_repo::run_repo(command)?;
            Ok(RunCommandOutcome::RunRepo(result))
        }
    }
}

fn print_help_message() -> Vec<String> {
    let bin = LITEX.to_ascii_lowercase();
    let entries = vec![
        format!("{} (test track)", LITEX),
        format!("{}", bin),
        format!("{} -e <code>", bin),
        format!("{} -f <file>", bin),
        format!("{} -r <repository>", bin),
        format!("{} -strict -e <code>", bin),
        format!("{} -f <file> -session", bin),
        format!("{} -help", bin),
        format!("{} -version", bin),
        "Without LITEX_NEW_PIPELINE, the legacy CLI is used.".to_string(),
        "-session keeps the Runtime env open and continues as REPL after -e/-f/-r."
            .to_string(),
        "-strict forbids `trust` / `trust have` / `abstract_prop`.".to_string(),
    ];
    println!("{}", entries[0]);
    println!();
    println!("Usage:");
    for entry in &entries[1..9] {
        println!("  {}", entry);
    }
    println!();
    println!("{}", entries[9]);
    println!("{}", entries[10]);
    println!("{}", entries[11]);
    entries
}
