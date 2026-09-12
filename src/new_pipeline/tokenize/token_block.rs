use crate::new_pipeline::runtime::{RealOrVirtualPath, RuntimeParseError, RuntimeResult};

/// One indented source unit handed from tokenizer to parser.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokenBlock {
    pub header: Vec<String>,
    pub body: Vec<TokenBlock>,
    pub line: usize,
    pub source_path: RealOrVirtualPath,
    pub parse_index: usize,
}

impl TokenBlock {
    pub fn new(
        header: Vec<String>,
        body: Vec<TokenBlock>,
        line: usize,
        source_path: RealOrVirtualPath,
    ) -> Self {
        Self {
            header,
            body,
            line,
            source_path,
            parse_index: 0,
        }
    }

    pub fn current(&self) -> RuntimeResult<&str> {
        self.header
            .get(self.parse_index)
            .map(|token| token.as_str())
            .ok_or_else(|| {
                RuntimeParseError::new(
                    "unexpected end of tokens",
                    self.line,
                    self.source_path.clone(),
                )
                .into()
            })
    }

    pub fn advance(&mut self) -> RuntimeResult<String> {
        let token = self.current()?.to_string();
        self.parse_index += 1;
        Ok(token)
    }

    pub fn skip(&mut self) -> RuntimeResult<()> {
        self.current()?;
        self.parse_index += 1;
        Ok(())
    }

    pub fn exceed_end_of_head(&self) -> bool {
        self.parse_index >= self.header.len()
    }
}
