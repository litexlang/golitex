use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

/// Compatibility entrypoint for compiling one complete typed source run.
pub fn compile_run(
    result: &RunLitexCodeResult,
    runtime: &Runtime,
    artifact_namespace: &str,
) -> Result<String, LeanCompileError> {
    LitexToLeanCompiler::new(result, runtime).compile(artifact_namespace)
}
