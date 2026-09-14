use crate::new_pipeline::runtime::{RealOrVirtualPath, Runtime, RuntimeResult};

pub fn run_eval(code: String) -> RuntimeResult<()> {
    let mut runtime = Runtime::new();
    runtime.begin_file(RealOrVirtualPath::Eval, false);
    if let Err(error) = runtime.run_litex_code(&code) {
        runtime.abort_file();
        return Err(error);
    }
    let (file, exec_env) = runtime.finish_file();
    runtime.publish_completed_export_file(file, exec_env);
    Ok(())
}
