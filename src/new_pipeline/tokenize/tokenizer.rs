use crate::new_pipeline::runtime::{PipelineError, PipelineResult};
use std::path::PathBuf;

/// One source-level unit handed from tokenizer to parser.
///
/// This is intentionally small while the new syntax model is being built. The
/// real tokenizer can later add indentation, source spans, and token kinds
/// without changing the file runner's lifecycle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokenBlock {
    pub line: usize,
    pub source_path: PathBuf,
    pub tokens: Vec<String>,
}

pub struct Tokenizer;

impl Tokenizer {
    pub fn new() -> Self {
        Self
    }

    /// Tokenize source into non-empty line blocks.
    pub fn tokenize(
        &self,
        code: &str,
        source_path: impl Into<PathBuf>,
    ) -> PipelineResult<Vec<TokenBlock>> {
        let source_path = source_path.into();
        let mut blocks = Vec::new();

        for (index, raw_line) in code.lines().enumerate() {
            let line = index + 1;
            let content = raw_line.split('#').next().unwrap_or("").trim();
            if content.is_empty() {
                continue;
            }

            let tokens = content
                .split_whitespace()
                .map(str::to_owned)
                .collect::<Vec<_>>();
            if tokens.is_empty() {
                return Err(PipelineError::Invariant(format!(
                    "tokenizer produced an empty block at line {line}"
                )));
            }
            blocks.push(TokenBlock {
                line,
                source_path: source_path.clone(),
                tokens,
            });
        }

        Ok(blocks)
    }
}

impl Default for Tokenizer {
    fn default() -> Self {
        Self::new()
    }
}
