use crate::new_pipeline::runtime::{
    CodeSource, RealOrVirtualPath, RuntimeParseError, RuntimeResult,
};

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

    pub fn peek(&self) -> Option<&str> {
        self.header.get(self.parse_index).map(String::as_str)
    }

    pub fn peek_at(&self, offset: usize) -> Option<&str> {
        self.header
            .get(self.parse_index + offset)
            .map(String::as_str)
    }

    pub fn expect(&mut self, expected: &str) -> RuntimeResult<()> {
        let got = self.current()?;
        if got != expected {
            return Err(RuntimeParseError::new(
                format!("expected `{expected}`, got `{got}`"),
                self.line,
                self.source_path.clone(),
            )
            .into());
        }
        self.parse_index += 1;
        Ok(())
    }

    pub fn expect_colon_end_of_header(&mut self) -> RuntimeResult<()> {
        self.expect(":")?;
        if !self.exceed_end_of_head() {
            return Err(RuntimeParseError::new(
                "trailing tokens after `:`",
                self.line,
                self.source_path.clone(),
            )
            .into());
        }
        Ok(())
    }

    pub fn line_file(&self, code_source: CodeSource) -> crate::new_pipeline::ast::SourceLine {
        crate::new_pipeline::ast::SourceLine::new(self.line, code_source)
    }

    pub fn parse_error(
        &self,
        message: impl Into<String>,
    ) -> crate::new_pipeline::runtime::RuntimeError {
        RuntimeParseError::new(message, self.line, self.source_path.clone()).into()
    }
}
