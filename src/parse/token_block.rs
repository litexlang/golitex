use crate::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TokenBlock {
    pub header: Vec<String>,
    pub body: Vec<TokenBlock>,
    pub line_file: LineFile,
    pub parse_index: usize,
}

impl TokenBlock {
    /// 返回当前 token；若已读完则返回 Error。
    pub fn current(&self) -> Result<&str, RuntimeError> {
        self.header
            .get(self.parse_index)
            .map(|s| s.as_str())
            .ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "Unexpected end of tokens".to_string(),
                        self.line_file.clone(),
                    ),
                ))
            })
    }

    pub fn skip_token(self: &mut Self, token: &str) -> Result<(), RuntimeError> {
        if self.current()? == token {
            self.parse_index += 1;
            Ok(())
        } else {
            Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!("Expected token: {}", token),
                    self.line_file.clone(),
                ),
            )))
        }
    }

    pub fn advance(&mut self) -> Result<String, RuntimeError> {
        let t = self.current()?.to_string();
        self.parse_index += 1;
        Ok(t)
    }

    pub fn skip(&mut self) -> Result<(), RuntimeError> {
        self.current()?;
        self.parse_index += 1;
        Ok(())
    }

    pub fn exceed_end_of_head(&self) -> bool {
        return self.parse_index >= self.header.len();
    }

    pub fn skip_token_and_colon_and_exceed_end_of_head(
        &mut self,
        token: &str,
    ) -> Result<(), RuntimeError> {
        self.skip_token(token)?;
        self.skip_token(COLON)?;
        if !self.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "Expected token: at head".to_string(),
                    self.line_file.clone(),
                ),
            )));
        }
        Ok(())
    }

    pub fn token_at_index(&self, index: usize) -> Result<&str, RuntimeError> {
        self.header.get(index).map(|s| s.as_str()).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!("Expected token: at index {}", index),
                    self.line_file.clone(),
                ),
            ))
        })
    }

    pub fn current_token_empty_if_exceed_end_of_head(&self) -> &str {
        if self.exceed_end_of_head() {
            return "";
        }
        self.header
            .get(self.parse_index)
            .map(|s| s.as_str())
            .unwrap_or("")
    }

    pub fn current_token_is_equal_to(&self, token: &str) -> bool {
        self.current_token_empty_if_exceed_end_of_head() == token
    }

    pub fn token_at_end_of_head(&self) -> &str {
        self.header
            .get(self.header.len() - 1)
            .map(|s| s.as_str())
            .unwrap_or("")
    }

    pub fn token_at_add_index(&self, index: usize) -> &str {
        self.header
            .get(self.parse_index + index)
            .map(|s| s.as_str())
            .unwrap_or("")
    }
}

impl TokenBlock {
    pub fn new(tokens: Vec<String>, body: Vec<TokenBlock>, line_file: LineFile) -> TokenBlock {
        TokenBlock {
            header: tokens,
            body,
            line_file,
            parse_index: 0,
        }
    }
}
