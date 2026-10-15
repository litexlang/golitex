use crate::runtime::{CodeSource, RuntimeParseError, RuntimeResult};
use std::ops::Range;
use std::sync::Arc;

/// One indented source unit handed from tokenizer to parser.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokenBlock {
    pub header: Vec<String>,
    pub body: Vec<TokenBlock>,
    pub line: usize,
    pub source_path: CodeSource,
    pub parse_index: usize,
    /// Original input and byte ranges, before comments, joining and aliases.
    pub source: Option<Arc<str>>,
    pub token_spans: Vec<Range<usize>>,
}

impl TokenBlock {
    pub fn new(
        header: Vec<String>,
        body: Vec<TokenBlock>,
        line: usize,
        source_path: CodeSource,
    ) -> Self {
        Self {
            header,
            body,
            line,
            source_path,
            parse_index: 0,
            source: None,
            token_spans: Vec::new(),
        }
    }

    pub fn current(&self) -> RuntimeResult<&str> {
        self.header
            .get(self.parse_index)
            .map(|token| token.as_str())
            .ok_or_else(|| self.parse_error("unexpected end of tokens"))
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
        let Some(got) = self.peek() else {
            let mut error =
                self.error_at_cursor(format!("expected `{expected}`, reached end of line"));
            if let Some(source) = &mut error.source {
                source.label = Some(format!("missing `{expected}`"));
            }
            return Err(error.into());
        };
        if got != expected {
            return Err(self.parse_error(format!("expected `{expected}`, got `{got}`")));
        }
        self.parse_index += 1;
        Ok(())
    }

    pub fn expect_colon_end_of_header(&mut self) -> RuntimeResult<()> {
        self.expect(":")?;
        if !self.exceed_end_of_head() {
            return Err(self.parse_error("trailing tokens after `:`"));
        }
        Ok(())
    }

    pub fn line_file(&self) -> crate::ast::SourceLine {
        crate::ast::SourceLine::new(self.line, self.source_path.clone())
    }

    pub fn parse_error(&self, message: impl Into<String>) -> crate::runtime::RuntimeError {
        self.error_at_cursor(message).into()
    }

    pub fn error_at_cursor(&self, message: impl Into<String>) -> RuntimeParseError {
        let error = RuntimeParseError::new(message, self.line, self.source_path.clone());
        let offset = self
            .token_spans
            .get(self.parse_index)
            .map(|span| span.start)
            .or_else(|| self.token_spans.last().map(|span| span.end));
        match (&self.source, offset) {
            (Some(source), Some(offset)) => error.with_source(source, offset),
            _ => error,
        }
    }

    pub fn header_slice(&self, range: Range<usize>) -> Self {
        let mut block = Self::new(
            self.header[range.clone()].to_vec(),
            Vec::new(),
            self.line,
            self.source_path.clone(),
        );
        block.source = self.source.clone();
        if let Some(spans) = self.token_spans.get(range) {
            block.token_spans = spans.to_vec();
        }
        block
    }
}
