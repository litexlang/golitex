pub mod cli_arg_e;
pub mod cli_arg_f;
pub mod cli_arg_r;
mod command;
mod command_dispatch;
mod run;
pub mod run_litex_code;

pub use command::{parse_cli_command, CliCommand};
pub use command_dispatch::{run_cli_command, DispatchOutcome, NEW_PIPELINE_VERSION};
pub use run::run;
pub use run_litex_code::{
    execute_module_plan_verified, run_litex_code, FileSpec, ModuleExecutionPlan,
};
