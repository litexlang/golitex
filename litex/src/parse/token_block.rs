use super::tokenizer::tokenize_line;
use crate::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TokenBlock {
    pub header: Vec<String>,
    pub body: Vec<TokenBlock>,
    pub line_file: (usize, usize),
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
    trimmed.ends_with(':') || trimmed.ends_with('：')
}

impl TokenBlock {
    pub fn parse_blocks(
        s: &str,
        current_file_index: usize,
    ) -> Result<Vec<TokenBlock>, ParseBlockError> {
        let stripped_source_code = strip_triple_quote_comment_blocks(s);
        let lines: Vec<_> = stripped_source_code.lines().collect();
        let mut i = 0;
        parse_level(&lines, &mut i, 0, current_file_index)
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
    current_file_index: usize,
) -> Result<Vec<TokenBlock>, ParseBlockError> {
    let remaining_line_count_upper_bound = lines.len().saturating_sub(*i);
    let mut items = Vec::with_capacity(remaining_line_count_upper_bound);
    let mut body_indent = None;

    while *i < lines.len() {
        let raw = lines[*i];
        let line_no = *i + 1;
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
            return Err(ParseBlockError::UnexpectedIndent(
                line_no,
                current_file_index,
            ));
        }

        *i += 1;

        // Tokenize header; if it's empty (e.g. whole line comment),
        // treat it like a blank line for block parsing.
        let header_tokens = tokenize_line(content);
        if header_tokens.is_empty() {
            continue;
        }

        if ends_with_colon(content) {
            // 必须有 body
            if *i >= lines.len() {
                return Err(ParseBlockError::MissingBody(line_no, current_file_index));
            }

            let next_indent = indent_level(lines[*i]);
            if next_indent <= indent {
                return Err(ParseBlockError::ExpectedIndent(*i + 1, current_file_index));
            }

            let body = parse_level(lines, i, next_indent, current_file_index)?;
            items.push(TokenBlock::new(
                header_tokens,
                body,
                (line_no, current_file_index),
            ));
        } else {
            items.push(TokenBlock::new(
                header_tokens,
                vec![],
                (line_no, current_file_index),
            ));
        }

        if let Some(expected) = body_indent {
            if indent != expected {
                return Err(ParseBlockError::InconsistentIndent(
                    line_no,
                    current_file_index,
                ));
            }
        } else {
            body_indent = Some(indent);
        }
    }

    Ok(items)
}

impl TokenBlock {
    /// 返回当前 token；若已读完则返回 Error。
    pub fn current(&self) -> Result<&str, ParsingError> {
        self.header
            .get(self.parse_index)
            .map(|s| s.as_str())
            .ok_or_else(|| {
                ParsingError::new("Unexpected end of tokens".to_string(), self.line_file, None)
            })
    }

    pub fn skip_token(self: &mut Self, token: &str) -> Result<(), ParsingError> {
        if self.current()? == token {
            self.parse_index += 1;
            Ok(())
        } else {
            Err(ParsingError::new(
                format!("Expected token: {}", token),
                self.line_file,
                None,
            ))
        }
    }

    pub fn advance(&mut self) -> Result<String, ParsingError> {
        let t = self.current()?.to_string();
        self.parse_index += 1;
        Ok(t)
    }

    pub fn skip(&mut self) -> Result<(), ParsingError> {
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
    ) -> Result<(), ParsingError> {
        self.skip_token(token)?;
        self.skip_token(COLON)?;
        if !self.exceed_end_of_head() {
            return Err(ParsingError::new(
                "Expected token: at head".to_string(),
                self.line_file,
                None,
            ));
        }
        Ok(())
    }

    pub fn token_at_index(&self, index: usize) -> Result<&str, ParsingError> {
        self.header.get(index).map(|s| s.as_str()).ok_or_else(|| {
            ParsingError::new(
                format!("Expected token: at index {}", index),
                self.line_file,
                None,
            )
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
}

impl TokenBlock {
    pub fn new(
        tokens: Vec<String>,
        body: Vec<TokenBlock>,
        line_file: (usize, usize),
    ) -> TokenBlock {
        TokenBlock {
            header: tokens,
            body,
            line_file,
            parse_index: 0,
        }
    }
}
