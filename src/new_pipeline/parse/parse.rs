use crate::new_pipeline::runtime::{PipelineError, PipelineResult, Runtime};
use crate::new_pipeline::tokenize::TokenBlock;
use crate::prelude::Stmt;

impl Runtime {
    /// Parse token blocks into statements.
    ///
    /// Not wired yet. Success path will return `Vec<Stmt>`.
    pub fn parse(&mut self, token_blocks: &[TokenBlock]) -> PipelineResult<Vec<Stmt>> {
        let _ = token_blocks;
        Err(PipelineError::Unsupported(
            "new_pipeline parse is not wired yet".to_string(),
        ))
    }
}
