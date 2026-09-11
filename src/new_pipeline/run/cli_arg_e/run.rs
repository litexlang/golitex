use crate::new_pipeline::runtime::{PipelineResult, Runtime};

/// Entry point for `litex -e <code>`.
pub fn run_cli_arg_e(code: String) -> PipelineResult<()> {
    let mut runtime = Runtime::new();
    runtime.begin_file("<eval>", false);
    if let Err(error) = runtime.run_code_verified(&code) {
        runtime.abort_file();
        return Err(error);
    }

    let (path, exec_env) = runtime.finish_file();
    runtime.publish_completed_export_file(path, exec_env);
    Ok(())
}
