use crate::new_pipeline::runtime::{PipelineError, PipelineResult};
use std::path::PathBuf;

/// Future entry point for `litex -r <repository>`.
pub fn run_cli_arg_r(_path: PathBuf) -> PipelineResult<()> {
    Err(PipelineError::Unsupported(
        "repository execution is not wired yet".to_string(),
    ))
}
