use crate::error::RuntimeError;
use crate::pipeline::SourceImportPolicy;
use crate::result::StmtResult;
use crate::runtime::Runtime;

/// Test-only shorthand for the production `Runtime::execute_source` entry point.
pub fn execute_source(
    source_code: &str,
    runtime: &mut Runtime,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    runtime
        .execute_source(source_code, SourceImportPolicy::UseRuntimePolicy)
        .into_parts()
}
