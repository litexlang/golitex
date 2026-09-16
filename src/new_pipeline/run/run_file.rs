use crate::new_pipeline::launch_command::LaunchCommand;
use super::run_command_outcome::RunFileResult;
use super::run_repl::run_repl_loop;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
use std::fs;

/// Run one file.
/// Module mount / litex.config preload is assumed elsewhere later; not defined here.
/// With `session`, a successful run keeps the file env open and enters REPL.
pub fn run_file(command: LaunchCommand) -> RuntimeResult<RunFileResult> {
    let LaunchCommand::File { path, session, .. } = &command else {
        panic!("run_file expects LaunchCommand::File");
    };
    let path = path.clone();
    let session = *session;

    if path.as_os_str().is_empty() {
        return Err(RuntimeError::InvalidArguments(
            "-f requires a source file".to_string(),
        ));
    }

    let source = fs::read_to_string(&path).map_err(|error| RuntimeError::Io {
        path: path.clone(),
        message: error.to_string(),
    })?;

    let mut runtime = Runtime::new(command);
    let code_result = match runtime.run_litex_code(&source) {
        Ok(result) => result,
        Err(error) => {
            runtime.abort_file();
            return Err(error);
        }
    };

    if !code_result.success {
        runtime.abort_file();
        return Ok(RunFileResult::new(path, code_result));
    }

    if session {
        // Keep the same file ExecEnv; REPL continues this environment.
        run_repl_loop(&mut runtime)?;
        return Ok(RunFileResult::new(path, code_result));
    }

    let (file, exec_env) = runtime.finish_file();
    runtime.publish_completed_export_file(file, exec_env);
    Ok(RunFileResult::new(path, code_result))
}
