use crate::new_pipeline::execute::RunResult;
use crate::new_pipeline::run::run_litex_code::{
    execute_module_plan_verified, ModuleExecutionPlan,
};
use crate::new_pipeline::runtime::{PipelineError, PipelineResult, RunOptions, RunTarget, Runtime};

/// Entry point for `litex -f <file>`.
pub fn run_cli_arg_f(options: RunOptions) -> PipelineResult<RunResult> {
    let RunTarget::File(path) = options.target.clone() else {
        unreachable!("cli_arg_f receives only a File target")
    };
    if path.as_os_str().is_empty() {
        return Err(PipelineError::InvalidArguments(
            "-f requires a source file".to_string(),
        ));
    }

    let mut runtime = Runtime::from_run_options(&options);

    // The config loader will replace this one-export plan.  Keeping the plan
    // explicit already fixes the order: std -> imported modules -> exports.
    let plan = ModuleExecutionPlan::single_export(path);
    let mut files = Vec::new();
    execute_module_plan_verified(&mut runtime, &plan, &mut files)?;

    Ok(RunResult {
        target: options.target,
        files,
    })
}
