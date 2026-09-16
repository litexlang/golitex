use crate::new_pipeline::launch_command::LaunchCommand;
use super::run_command_outcome::RunEvalResult;
use super::run_repl::run_repl_loop;
use crate::new_pipeline::runtime::{RealOrVirtualPath, Runtime, RuntimeError, RuntimeResult};

/// With `session`, a successful eval keeps the env open and enters REPL.
pub fn run_eval(command: LaunchCommand) -> RuntimeResult<RunEvalResult> {
    let LaunchCommand::Eval { code, session, .. } = &command else {
        return Err(RuntimeError::Invariant(
            "run_eval expects LaunchCommand::Eval".to_string(),
        ));
    };
    let code = code.clone();
    let session = *session;

    let mut runtime = Runtime::new();
    runtime.launch_command = command;
    runtime.begin_file(RealOrVirtualPath::Eval);
    let code_result = match runtime.run_litex_code(&code) {
        Ok(result) => result,
        Err(error) => {
            runtime.abort_file();
            return Err(error);
        }
    };

    if !code_result.success {
        runtime.abort_file();
        return Ok(RunEvalResult::new(code_result));
    }

    if session {
        run_repl_loop(&mut runtime)?;
        return Ok(RunEvalResult::new(code_result));
    }

    let (file, exec_env) = runtime.finish_file();
    runtime.publish_completed_export_file(file, exec_env);
    Ok(RunEvalResult::new(code_result))
}
