use crate::new_pipeline::runtime::{PipelineError, PipelineResult, Runtime};
use crate::prelude::Stmt;

impl Runtime {
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> PipelineResult<()> {
        let _ = stmt;
        Err(PipelineError::Unsupported(
            "new_pipeline exec_stmt is not wired yet".to_string(),
        ))
    }
}
