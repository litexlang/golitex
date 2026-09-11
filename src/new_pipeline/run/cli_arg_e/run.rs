use crate::new_pipeline::execute::{FileRunResult, RunResult};
use crate::new_pipeline::runtime::{PipelineResult, RunOptions, RunTarget, Runtime};

/// Entry point for `litex -e <code>`.
///
/// It uses the same file-scope lifecycle as `-f`, with a virtual source name.
/// The command is kept here so the top-level `run` dispatcher does not grow a
/// second implementation of tokenize/parse/execute.
pub fn run_cli_arg_e(options: RunOptions) -> PipelineResult<RunResult> {
    let RunTarget::Eval(code) = options.target.clone() else {
        unreachable!("cli_arg_e receives only an Eval target")
    };

    let mut runtime = Runtime::from_run_options(&options);
    runtime.begin_file("<eval>", false);
    let statement_results = match runtime.run_code_verified(&code) {
        Ok(results) => results,
        Err(error) => {
            runtime.abort_file();
            return Err(error);
        }
    };

    let completed = runtime.finish_file();
    let file_result = FileRunResult {
        name: completed.name.clone(),
        path: completed.path.clone(),
        statement_results,
    };
    runtime.publish_completed_export_file(completed);

    Ok(RunResult {
        target: options.target,
        files: vec![file_result],
    })
}
