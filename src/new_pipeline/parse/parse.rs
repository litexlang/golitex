use crate::new_pipeline::runtime::{PipelineError, PipelineResult, Runtime};
use crate::new_pipeline::tokenize::TokenBlock;

/// Syntax-neutral statement placeholder used by the execution skeleton.
///
/// The parser will eventually replace `tokens` with typed statement variants.
/// Keeping a parsed value distinct from `TokenBlock` preserves the stage
/// boundary now.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParsedStatement {
    pub line: usize,
    pub source_path: std::path::PathBuf,
    pub tokens: Vec<String>,
}

impl Runtime {
    pub fn parse_stmt(&mut self, token_block: &mut TokenBlock) -> PipelineResult<ParsedStatement> {
        if token_block.tokens.is_empty() {
            return Err(PipelineError::Invariant(format!(
                "parser received an empty token block at line {}",
                token_block.line
            )));
        }

        Ok(ParsedStatement {
            line: token_block.line,
            source_path: token_block.source_path.clone(),
            tokens: token_block.tokens.clone(),
        })
    }
}
