use crate::launch_command::LaunchCommand;
use super::run_command_outcome::{RunEvalResult, RunLitexCodeResult};
use super::run_repl::run_repl_loop;
use crate::run_module::{mount_cwd_config, MountCwdConfigOutcome};
use crate::runtime::{RealOrVirtualPath, Runtime, RuntimeResult};

/// `-e <code>`: mount cwd `litex.config` when present (else empty), then eval.
/// With `session`, a successful eval keeps the env open and enters REPL.
pub fn run_eval(command: LaunchCommand) -> RuntimeResult<RunEvalResult> {
    let LaunchCommand::Eval { code, session, .. } = &command else {
        panic!("run_eval expects LaunchCommand::Eval");
    };
    let code = code.clone();
    let session = *session;

    let mut runtime = Runtime::new(command);
    // Drop placeholder Eval env so mount can open export files.
    runtime.abort_file();

    match mount_cwd_config(&mut runtime)? {
        MountCwdConfigOutcome::Done => {}
        MountCwdConfigOutcome::SessionError(session_error) => {
            return Ok(RunEvalResult::new(RunLitexCodeResult::new(
                Vec::new(),
                Some(session_error),
            )));
        }
    }

    runtime.set_code_source(crate::runtime::CodeSource::Eval);
    runtime.begin_file(RealOrVirtualPath::Eval);

    let mut code_result = match runtime.run_litex_code(&code) {
        Ok(result) => result,
        Err(error) => {
            runtime.abort_file();
            return Err(error);
        }
    };
    code_result.attach_normal_json(&runtime, "eval", None);

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
