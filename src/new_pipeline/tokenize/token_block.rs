use crate::new_pipeline::runtime::{PipelineError, PipelineResult};
use std::path::PathBuf;

/// One indented source unit handed from tokenizer to parser.
///
/// Shape matches the legacy token block: a header line, an optional indented
/// body, a source location, and a parse cursor.  Owned entirely by
/// `new_pipeline`; it does not import `crate::parsing`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokenBlock {
    pub header: Vec<String>,
    pub body: Vec<TokenBlock>,
    pub line: usize,
    pub source_path: PathBuf,
    pub parse_index: usize,
}

impl TokenBlock {
    pub fn new(
        header: Vec<String>,
        body: Vec<TokenBlock>,
        line: usize,
        source_path: PathBuf,
    ) -> Self {
        Self {
            header,
            body,
            line,
            source_path,
            parse_index: 0,
        }
    }

    pub fn current(&self) -> PipelineResult<&str> {
        self.header
            .get(self.parse_index)
            .map(|token| token.as_str())
            .ok_or_else(|| {
                PipelineError::InvalidArguments(format!(
                    "unexpected end of tokens at line {} in {}",
                    self.line,
                    self.source_path.display()
                ))
            })
    }

    pub fn advance(&mut self) -> PipelineResult<String> {
        let token = self.current()?.to_string();
        self.parse_index += 1;
        Ok(token)
    }

    pub fn skip(&mut self) -> PipelineResult<()> {
        self.current()?;
        self.parse_index += 1;
        Ok(())
    }

    pub fn exceed_end_of_head(&self) -> bool {
        self.parse_index >= self.header.len()
    }
}
