use super::run_command_outcome::RunEvalResult;
use crate::new_pipeline::runtime::{RealOrVirtualPath, Runtime, RuntimeResult};

pub fn run_eval(code: String) -> RuntimeResult<RunEvalResult> {
    let mut runtime = Runtime::new();
    runtime.begin_file(RealOrVirtualPath::Eval, false);
    let code_result = match runtime.run_litex_code(&code) {
        Ok(result) => result,
        Err(error) => {
            runtime.abort_file();
            return Err(error);
        }
    };

    if code_result.all_stmts_succeeded {
        let (file, exec_env) = runtime.finish_file();
        runtime.publish_completed_export_file(file, exec_env);
    } else {
        runtime.abort_file();
    }

    Ok(RunEvalResult::from_code_result(code_result))
}
