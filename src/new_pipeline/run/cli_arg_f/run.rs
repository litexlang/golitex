use crate::new_pipeline::run::run_litex_code::{
    execute_module_plan_verified, ModuleExecutionPlan,
};
use crate::new_pipeline::runtime::{PipelineError, PipelineResult, Runtime};
use std::path::PathBuf;

/// Entry point for `litex -f <file>`.
pub fn run_cli_arg_f(path: PathBuf) -> PipelineResult<()> {
    if path.as_os_str().is_empty() {
        return Err(PipelineError::InvalidArguments(
            "-f requires a source file".to_string(),
        ));
    }

    let mut runtime = Runtime::new();
    let plan = ModuleExecutionPlan::single_export(&path);
    execute_module_plan_verified(&mut runtime, &plan)
}
