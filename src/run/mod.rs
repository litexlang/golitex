pub mod run_command;
pub mod run_command_outcome;
pub mod run_eval;
pub mod run_extract;
pub mod run_file;
pub mod run_litex_code;
pub mod run_repl;
pub mod run_repo;

#[cfg(test)]
#[path = "../../tests/unit/run/binding_lifecycle/tests.rs"]
mod binding_lifecycle_tests;

pub use crate::launch_command::{parse_launch_command, CodeExtractionTarget, ExtractInput, LaunchCommand, OutputLanguage};
pub use run_command::{run_command, VERSION};
pub use run_command_outcome::{
    ExtractResult, HelpResult, RunCommandOutcome, RunEvalResult, RunFileResult, RunLitexCodeResult,
    RunRepoResult, RunSessionError, VersionResult,
};
