use super::tokenizer::Tokenizer;
use crate::prelude::*;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TokenBlock {
    pub header: Vec<String>,
    pub body: Vec<TokenBlock>,
    pub line_file: LineFile,
    pub parse_index: usize,
}

fn indent_level(line: &str) -> usize {
    let mut n = 0;
    for c in line.chars() {
        match c {
            ' ' => n += 1,
            '\t' => n += 4,
            _ => break,
        }
    }
    n
}

fn ends_with_colon(s: &str) -> bool {
    let trimmed = s.trim_end();
    trimmed.ends_with(COLON)
}

impl TokenBlock {
    pub fn parse_blocks(
        s: &str,
        current_file_path: Rc<str>,
        tokenizer: &mut Tokenizer,
    ) -> Result<Vec<TokenBlock>, RuntimeError> {
        let stripped_source_code = strip_triple_quote_comment_blocks(s);
        let lines: Vec<_> = stripped_source_code.lines().collect();
        let mut i = 0;
        parse_level(&lines, &mut i, 0, current_file_path, tokenizer)
    }
}

fn strip_triple_quote_comment_blocks(source_code: &str) -> String {
    // Treat a line that consists only of `"` characters (after trimming) as a delimiter.
    // Between two delimiter lines, everything is replaced with empty lines so
    // the parser will ignore those lines.
    let mut in_comment = false;
    let line_count_upper_bound = source_code.lines().count();
    let mut out_lines: Vec<String> = Vec::with_capacity(line_count_upper_bound);

    for line in source_code.lines() {
        let trimmed = line.trim();
        let only_quote_chars = !trimmed.is_empty() && trimmed.chars().all(|c| c == '"');
        if only_quote_chars {
            in_comment = !in_comment;
            out_lines.push(String::new());
            continue;
        }

        if in_comment {
            out_lines.push(String::new());
        } else {
            out_lines.push(line.to_string());
        }
    }

    out_lines.join("\n")
}

fn parse_level(
    lines: &[&str],
    i: &mut usize,
    base_indent: usize,
    current_file_path: Rc<str>,
    tokenizer: &mut Tokenizer,
) -> Result<Vec<TokenBlock>, RuntimeError> {
    let pushed = base_indent > 0;
    if pushed {
        tokenizer.push_scope();
    }
    let out = parse_level_impl(lines, i, base_indent, current_file_path, tokenizer);
    if pushed {
        tokenizer.pop_scope();
    }
    out
}

fn parse_level_impl(
    lines: &[&str],
    i: &mut usize,
    base_indent: usize,
    current_file_path: Rc<str>,
    tokenizer: &mut Tokenizer,
) -> Result<Vec<TokenBlock>, RuntimeError> {
    let remaining_line_count_upper_bound = lines.len().saturating_sub(*i);
    let mut items = Vec::with_capacity(remaining_line_count_upper_bound);
    let mut body_indent = None;

    while *i < lines.len() {
        let raw = lines[*i];
        let line_no = *i + 1;
        let line_file = (line_no, current_file_path.clone());
        let indent = indent_level(raw);
        let content = raw.trim();

        if content.is_empty() {
            *i += 1;
            continue;
        }

        if indent < base_indent {
            break;
        }

        if indent > base_indent {
            return Err({
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    format!(
                        "unexpected indent at line {} in {}",
                        line_file.0,
                        line_file.1.as_ref()
                    ),
                    line_file,
                    None,
                    vec![],
                )))
            });
        }

        *i += 1;

        // Tokenize header; if it's empty (e.g. whole line comment),
        // treat it like a blank line for block parsing.
        let header_tokens = tokenizer.tokenize_line(content, line_file.clone())?;
        if header_tokens.is_empty() {
            continue;
        }

        if ends_with_colon(content) {
            // 必须有 body
            if *i >= lines.len() {
                return Err({
                    let line_file = (line_no, current_file_path.clone());
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                        None,
                        format!(
                            "block header missing body at line {} in {}",
                            line_file.0,
                            line_file.1.as_ref()
                        ),
                        line_file,
                        None,
                        vec![],
                    )))
                });
            }

            let next_indent = indent_level(lines[*i]);
            if next_indent <= indent {
                return Err({
                    let line_file = (*i + 1, current_file_path.clone());
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                        None,
                        format!(
                            "expected indent at line {} in {}",
                            line_file.0,
                            line_file.1.as_ref()
                        ),
                        line_file,
                        None,
                        vec![],
                    )))
                });
            }

            let body =
                parse_level(lines, i, next_indent, current_file_path.clone(), tokenizer)?;
            items.push(TokenBlock::new(
                header_tokens,
                body,
                (line_no, current_file_path.clone()),
            ));
        } else {
            items.push(TokenBlock::new(
                header_tokens,
                vec![],
                (line_no, current_file_path.clone()),
            ));
        }

        if let Some(expected) = body_indent {
            if indent != expected {
                return Err({
                    let line_file = (line_no, current_file_path.clone());
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                        None,
                        format!(
                            "inconsistent indent at line {} in {}",
                            line_file.0,
                            line_file.1.as_ref()
                        ),
                        line_file,
                        None,
                        vec![],
                    )))
                });
            }
        } else {
            body_indent = Some(indent);
        }
    }

    Ok(items)
}

impl TokenBlock {
    /// 返回当前 token；若已读完则返回 Error。
    pub fn current(&self) -> Result<&str, RuntimeError> {
        self.header
            .get(self.parse_index)
            .map(|s| s.as_str())
            .ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "Unexpected end of tokens".to_string(),
                    self.line_file.clone(),
                    None,
                    vec![],
                )))
            })
    }

    pub fn skip_token(self: &mut Self, token: &str) -> Result<(), RuntimeError> {
        if self.current()? == token {
            self.parse_index += 1;
            Ok(())
        } else {
            Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    format!("Expected token: {}", token),
                    self.line_file.clone(),
                    None,
                    vec![],
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
                RuntimeErrorStruct::new(
                    None,
                    "Expected token: at head".to_string(),
                    self.line_file.clone(),
                    None,
                    vec![],
                ),
            )));
        }
        Ok(())
    }

    pub fn token_at_index(&self, index: usize) -> Result<&str, RuntimeError> {
        self.header.get(index).map(|s| s.as_str()).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                format!("Expected token: at index {}", index),
                self.line_file.clone(),
                None,
                vec![],
            )))
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
