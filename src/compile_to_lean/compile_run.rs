use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

/// Compile one complete typed source run using its completed Runtime.
pub fn compile_run(
    result: &RunLitexCodeResult,
    runtime: Runtime,
    artifact_namespace: &str,
) -> Result<String, LeanCompileError> {
    LitexToLeanCompiler::new(runtime).compile_run(result, artifact_namespace)
}
