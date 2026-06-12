//! Tokenizer: splits source text into token blocks for the parser.
//!
//! - `#` starts an end-of-line comment.
//! - Multi-character symbols from [`crate::common::keywords::key_symbols_sorted_by_len_desc`] are
//!   matched with longest-first priority.
//! - Double-quoted segments are one token (with `\"` and `\\` skips for the closing quote).

use crate::common::keywords::key_symbols_sorted_by_len_desc;
use crate::parse::TokenBlock;
use crate::prelude::*;

use std::collections::HashMap;
use std::rc::Rc;

pub struct Tokenizer {
    pub macros_in_block_scopes: Vec<HashMap<String, Vec<String>>>,
}

impl Default for Tokenizer {
    fn default() -> Self {
        Self::new()
    }
}

impl Tokenizer {
    pub fn new() -> Self {
        Self {
            macros_in_block_scopes: vec![],
        }
    }

    pub fn parse_blocks(
        &mut self,
        s: &str,
        current_file_path: Rc<str>,
    ) -> Result<Vec<TokenBlock>, RuntimeError> {
        let stripped_source_code = self.strip_triple_quote_comment_blocks(s);
        let lines: Vec<_> = stripped_source_code.lines().collect();
        let mut i = 0;
        self.parse_level(&lines, &mut i, 0, current_file_path)
    }

    pub fn tokenize_line(
        &self,
        line: &str,
        line_file: LineFile,
    ) -> Result<Vec<String>, RuntimeError> {
        let raw_tokens = self.raw_tokenize_line(line);
        self.expand_macro_tokens(raw_tokens, line_file)
    }

    fn raw_tokenize_line(&self, line: &str) -> Vec<String> {
        let line = line.trim_end();
        let symbols = key_symbols_sorted_by_len_desc();
        let mut tokens = Vec::with_capacity(line.len());
        let mut i = 0;
        let bytes = line.as_bytes();

        while i < bytes.len() {
            if !line.is_char_boundary(i) {
                let mut char_start = i;
                while char_start > 0 && !line.is_char_boundary(char_start) {
                    char_start -= 1;
                }
                i = char_start;
                continue;
            }

            if bytes[i] == b'#' {
                break;
            }

            let ws_ch = line[i..].chars().next().unwrap_or('\0');
            if ws_ch.is_whitespace() {
                i += ws_ch.len_utf8();
                continue;
            }

            let mut matched = false;
            for &sym in &symbols {
                let sym_length_bytes = sym.len();
                if i + sym_length_bytes <= line.len()
                    && line.is_char_boundary(i)
                    && line.is_char_boundary(i + sym_length_bytes)
                    && &line[i..i + sym_length_bytes] == sym
                {
                    tokens.push(sym.to_string());
                    i += sym_length_bytes;
                    matched = true;
                    break;
                }
            }
            if matched {
                continue;
            }

            let current_ch = line[i..].chars().next().unwrap_or('\0');
            if Self::is_identifier_start_char(current_ch) {
                let start = i;
                i += current_ch.len_utf8();
                while i < line.len() {
                    let next_ch = line[i..].chars().next().unwrap_or('\0');
                    if !Self::is_identifier_continue_char(next_ch) {
                        break;
                    }
                    i += next_ch.len_utf8();
                }
                tokens.push(line[start..i].to_string());
                continue;
            }

            if bytes[i] == b'@' {
                let start = i;
                i += 1;
                while i < line.len() {
                    let next_ch = line[i..].chars().next().unwrap_or('\0');
                    if !Self::is_identifier_continue_char(next_ch) {
                        break;
                    }
                    i += next_ch.len_utf8();
                }
                tokens.push(line[start..i].to_string());
                continue;
            }

            if bytes[i].is_ascii_digit() {
                let start = i;
                i += 1;
                while i < bytes.len() && bytes[i].is_ascii_digit() {
                    i += 1;
                }
                if i + 1 < bytes.len() && bytes[i] == b'.' && bytes[i + 1].is_ascii_digit() {
                    i += 1;
                    while i < bytes.len() && bytes[i].is_ascii_digit() {
                        i += 1;
                    }
                }
                tokens.push(line[start..i].to_string());
                continue;
            }

            let ch = line[i..].chars().next().unwrap_or('\0');
            tokens.push(ch.to_string());
            i += ch.len_utf8();
        }
        tokens
    }

    fn expand_macro_tokens(
        &self,
        raw_tokens: Vec<String>,
        line_file: LineFile,
    ) -> Result<Vec<String>, RuntimeError> {
        let mut expanded = Vec::with_capacity(raw_tokens.len());
        for token in raw_tokens {
            if Self::is_macro_use_token(&token) {
                let macro_name = &token[1..];
                let macro_tokens = self.find_macro(macro_name).ok_or_else(|| {
                    Self::parse_error(format!("Unknown macro: {}", token), line_file.clone())
                })?;
                expanded.extend(macro_tokens.iter().cloned());
            } else {
                expanded.push(token);
            }
        }
        Ok(expanded)
    }

    fn strip_triple_quote_comment_blocks(&self, source_code: &str) -> String {
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
        &mut self,
        lines: &[&str],
        i: &mut usize,
        base_indent: usize,
        current_file_path: Rc<str>,
    ) -> Result<Vec<TokenBlock>, RuntimeError> {
        self.macros_in_block_scopes.push(HashMap::new());
        let result = self.parse_level_in_current_scope(lines, i, base_indent, current_file_path);
        self.macros_in_block_scopes.pop();
        result
    }

    fn parse_level_in_current_scope(
        &mut self,
        lines: &[&str],
        i: &mut usize,
        base_indent: usize,
        current_file_path: Rc<str>,
    ) -> Result<Vec<TokenBlock>, RuntimeError> {
        let remaining_line_count_upper_bound = lines.len().saturating_sub(*i);
        let mut items = Vec::with_capacity(remaining_line_count_upper_bound);
        let mut body_indent = None;

        while *i < lines.len() {
            let raw = lines[*i];
            let line_no = *i + 1;
            let line_file = (line_no, current_file_path.clone());
            let indent = Self::indent_level(raw);
            let content = raw.trim();

            if content.is_empty() {
                *i += 1;
                continue;
            }

            if indent < base_indent {
                break;
            }

            if indent > base_indent {
                // Indented farther than the current block: normally a syntax error, but allow lines that
                // are only a `# ...` comment (any leading spaces/tabs before `#`). Writers often align
                // such comments with a surrounding block without attaching them to a sibling item.
                let trimmed_start = raw.trim_start();
                if trimmed_start.is_empty() || trimmed_start.starts_with('#') {
                    *i += 1;
                    continue;
                }
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "unexpected indent at line {} in {}",
                            line_file.0,
                            line_file.1.as_ref()
                        ),
                        line_file,
                    ),
                )));
            }

            *i += 1;

            // Tokenize header; if it's empty (e.g. whole line comment),
            // treat it like a blank line for block parsing.
            if self.register_macro_definition(content, line_file.clone())? {
                continue;
            }

            let raw_header_tokens = self.raw_tokenize_line(content);
            let header_tokens = self.expand_macro_tokens(raw_header_tokens, line_file.clone())?;
            if header_tokens.is_empty() {
                continue;
            }

            if Self::ends_with_colon(content) {
                // A block header must have an indented body.
                if *i >= lines.len() {
                    let line_file = (line_no, current_file_path.clone());
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!(
                                "block header missing body at line {} in {}",
                                line_file.0,
                                line_file.1.as_ref()
                            ),
                            line_file,
                        ),
                    )));
                }

                let next_indent = Self::indent_level(lines[*i]);
                if next_indent <= indent {
                    let line_file = (*i + 1, current_file_path.clone());
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!(
                                "expected indent at line {} in {}",
                                line_file.0,
                                line_file.1.as_ref()
                            ),
                            line_file,
                        ),
                    )));
                }

                let body = self.parse_level(lines, i, next_indent, current_file_path.clone())?;
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
                    let line_file = (line_no, current_file_path.clone());
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!(
                                "inconsistent indent at line {} in {}",
                                line_file.0,
                                line_file.1.as_ref()
                            ),
                            line_file,
                        ),
                    )));
                }
            } else {
                body_indent = Some(indent);
            }
        }

        Ok(items)
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

    fn register_macro_definition(
        &mut self,
        line: &str,
        line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        let Some(mut rest) = line.strip_prefix("macro") else {
            return Ok(false);
        };
        if !rest
            .chars()
            .next()
            .map(|ch| ch.is_whitespace())
            .unwrap_or(false)
        {
            return Ok(false);
        }

        if Self::ends_with_colon(line) {
            return Err(Self::parse_error(
                "macro definition cannot have a block body".to_string(),
                line_file,
            ));
        }

        rest = rest.trim_start();
        let name_end = rest
            .char_indices()
            .find(|(_, ch)| ch.is_whitespace())
            .map(|(index, _)| index)
            .unwrap_or(rest.len());
        let name = &rest[..name_end];
        if !Self::is_macro_name(name) {
            return Err(Self::parse_error(
                format!("Invalid macro name: {}", name),
                line_file,
            ));
        }

        rest = rest[name_end..].trim_start();
        let Some(replacement_and_tail) = rest.strip_prefix('"') else {
            return Err(Self::parse_error(
                "macro definition must be: macro name \"replacement\"".to_string(),
                line_file,
            ));
        };

        let mut replacement_end = None;
        let mut escaped = false;
        for (index, ch) in replacement_and_tail.char_indices() {
            if escaped {
                escaped = false;
                continue;
            }
            if ch == '\\' {
                escaped = true;
                continue;
            }
            if ch == '"' {
                replacement_end = Some(index);
                break;
            }
        }

        let Some(replacement_end) = replacement_end else {
            return Err(Self::parse_error(
                "macro replacement must end with a double quote".to_string(),
                line_file,
            ));
        };
        let replacement_source = &replacement_and_tail[..replacement_end];
        let tail = replacement_and_tail[replacement_end + 1..].trim_start();
        if !tail.is_empty() && !tail.starts_with('#') {
            return Err(Self::parse_error(
                "macro definition must be: macro name \"replacement\"".to_string(),
                line_file,
            ));
        }

        let replacement_tokens = self.raw_tokenize_line(replacement_source);
        if replacement_tokens
            .iter()
            .any(|token| Self::is_macro_use_token(token) || token == "macro")
        {
            return Err(Self::parse_error(
                "macro replacement cannot contain macro use or macro definition".to_string(),
                line_file,
            ));
        }

        let current_scope = self.macros_in_block_scopes.last_mut().ok_or_else(|| {
            Self::parse_error(
                "Internal tokenizer macro scope missing".to_string(),
                line_file,
            )
        })?;
        current_scope.insert(name.to_string(), replacement_tokens);
        Ok(true)
    }

    fn find_macro(&self, name: &str) -> Option<&Vec<String>> {
        self.macros_in_block_scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name))
    }

    fn is_macro_use_token(token: &str) -> bool {
        let Some(name) = token.strip_prefix('@') else {
            return false;
        };
        Self::is_macro_name(name)
    }

    fn is_macro_name(name: &str) -> bool {
        let mut chars = name.chars();
        match chars.next() {
            Some(ch) if Self::is_identifier_start_char(ch) => {}
            _ => return false,
        }
        chars.all(Self::is_identifier_continue_char)
    }

    fn is_identifier_start_char(ch: char) -> bool {
        ch == '_' || ch.is_alphabetic()
    }

    fn is_identifier_continue_char(ch: char) -> bool {
        ch == '_' || ch.is_alphanumeric()
    }

    fn parse_error(message: String, line_file: LineFile) -> RuntimeError {
        RuntimeError::from(ParseRuntimeError(
            RuntimeErrorStruct::new_with_msg_and_line_file(message, line_file),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::Tokenizer;
    use crate::prelude::*;
    use std::rc::Rc;

    fn test_line_file() -> LineFile {
        (1, Rc::from("test.lit"))
    }

    #[test]
    fn exist_bang_splits_into_exist_and_bang() {
        let tokenizer = Tokenizer::new();
        assert_eq!(
            tokenizer
                .tokenize_line("exist! a R st {}", test_line_file())
                .unwrap(),
            vec!["exist", "!", "a", "R", "st", "{", "}"]
        );
    }

    #[test]
    fn forall_bang_splits_like_exist_bang() {
        let tokenizer = Tokenizer::new();
        assert_eq!(
            tokenizer
                .tokenize_line("forall! x R: x > 0", test_line_file())
                .unwrap(),
            vec!["forall", "!", "x", "R", ":", "x", ">", "0"]
        );
    }

    #[test]
    fn unicode_identifier_is_one_token() {
        let tokenizer = Tokenizer::new();
        assert_eq!(
            tokenizer
                .tokenize_line("alias thm 自反等式 <=> self_eq", test_line_file())
                .unwrap(),
            vec!["alias", "thm", "自反等式", "<=>", "self_eq"]
        );
    }

    #[test]
    fn exist_bang_with_whitespace() {
        let tokenizer = Tokenizer::new();
        assert_eq!(
            tokenizer
                .tokenize_line("exist ! a R st {}", test_line_file())
                .unwrap(),
            vec!["exist", "!", "a", "R", "st", "{", "}"]
        );
    }

    #[test]
    fn macro_definition_expands_later_line_in_same_block() {
        let mut tokenizer = Tokenizer::new();
        let blocks = tokenizer
            .parse_blocks("macro eq \"a = b\"\nhave @eq", Rc::from("test.lit"))
            .unwrap();
        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0].header, vec!["have", "a", "=", "b"]);
    }

    #[test]
    fn unicode_macro_name_expands() {
        let mut tokenizer = Tokenizer::new();
        let blocks = tokenizer
            .parse_blocks("macro 等式 \"a = b\"\nhave @等式", Rc::from("test.lit"))
            .unwrap();
        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0].header, vec!["have", "a", "=", "b"]);
    }

    #[test]
    fn macro_scope_is_visible_in_child_block() {
        let mut tokenizer = Tokenizer::new();
        let blocks = tokenizer
            .parse_blocks(
                "macro eq \"a = b\"\nprove claim:\n    have @eq",
                Rc::from("test.lit"),
            )
            .unwrap();
        assert_eq!(blocks[0].body[0].header, vec!["have", "a", "=", "b"]);
    }

    #[test]
    fn macro_scope_expires_after_block() {
        let mut tokenizer = Tokenizer::new();
        let error = tokenizer
            .parse_blocks(
                "prove claim:\n    macro eq \"a = b\"\n    have @eq\nhave @eq",
                Rc::from("test.lit"),
            )
            .unwrap_err();
        assert!(format!("{:?}", error).contains("Unknown macro: @eq"));
    }

    #[test]
    fn inner_macro_overrides_outer_macro_only_inside_child_block() {
        let mut tokenizer = Tokenizer::new();
        let blocks = tokenizer
            .parse_blocks(
                "macro x \"outer\"\nprove claim:\n    macro x \"inner\"\n    have @x\nhave @x",
                Rc::from("test.lit"),
            )
            .unwrap();
        assert_eq!(blocks[0].body[0].header, vec!["have", "inner"]);
        assert_eq!(blocks[1].header, vec!["have", "outer"]);
    }

    #[test]
    fn macro_replacement_cannot_use_macro() {
        let mut tokenizer = Tokenizer::new();
        let error = tokenizer
            .parse_blocks("macro x \"@other\"", Rc::from("test.lit"))
            .unwrap_err();
        assert!(format!("{:?}", error).contains("macro replacement cannot contain"));
    }
}
