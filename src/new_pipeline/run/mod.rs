mod command;
mod run;
pub mod run_command;
pub mod run_command_outcome;
pub mod run_eval;
pub mod run_file;
pub mod run_litex_code;
pub mod run_repo;

pub use command::{parse_cli_command, CliCommand};
pub use run::run;
pub use run_command::{run_command, NEW_PIPELINE_VERSION};
pub use run_command_outcome::{
    HelpResult, RunCommandOutcome, RunEvalResult, RunFileResult, RunLitexCodeResult, RunRepoResult,
    RunSessionError, VersionResult,
};
