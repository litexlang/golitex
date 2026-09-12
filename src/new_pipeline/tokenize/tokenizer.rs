use super::symbols::{
    key_symbols_sorted_by_len_desc, unicode_alias_tokens, C_NOT_ZERO, COLON,
    N_POSITIVE, Q_NEGATIVE, Q_NOT_ZERO, Q_POSITIVE, R_NEGATIVE, R_NOT_ZERO, R_POSITIVE,
    UNICODE_C_NOT_ZERO, UNICODE_N_POSITIVE, UNICODE_Q_NEGATIVE, UNICODE_Q_NOT_ZERO,
    UNICODE_Q_POSITIVE, UNICODE_R_NEGATIVE, UNICODE_R_NOT_ZERO, UNICODE_R_POSITIVE,
    UNICODE_Z_NEGATIVE, UNICODE_Z_NOT_ZERO, UNICODE_Z_POSITIVE, Z_NEGATIVE, Z_NOT_ZERO,
    Z_POSITIVE,
};
use super::token_block::TokenBlock;
use crate::new_pipeline::runtime::{
    RealOrVirtualPath, RuntimeParseError, RuntimeResult,
};

pub struct Tokenizer;

impl Tokenizer {
    pub fn new() -> Self {
        Self
    }

    pub fn tokenize(
        &self,
        code: &str,
        source_path: RealOrVirtualPath,
    ) -> RuntimeResult<Vec<TokenBlock>> {
        let stripped = self.strip_triple_quote_comment_blocks(code);
        let lines: Vec<&str> = stripped.lines().collect();
        let mut index = 0;
        self.parse_level(&lines, &mut index, 0, &source_path)
    }

    // Skip ASCII `"..."` inline asides. They are not tokens and must not cross lines.
    fn strip_inline_asides(
        &self,
        line: &str,
        line_no: usize,
        source_path: &RealOrVirtualPath,
    ) -> RuntimeResult<String> {
        let mut out = String::with_capacity(line.len());
        let mut i = 0;
        let bytes = line.as_bytes();
        while i < bytes.len() {
            if bytes[i] == b'"' {
                i += 1;
                let mut closed = false;
                while i < bytes.len() {
                    if bytes[i] == b'"' {
                        i += 1;
                        closed = true;
                        break;
                    }
                    let ch = line[i..].chars().next().unwrap_or('\0');
                    i += ch.len_utf8();
                }
                if !closed {
                    return Err(RuntimeParseError::new(
                        "unclosed inline aside `\"...\"`",
                        line_no,
                        source_path.clone(),
                    )
                    .into());
                }
                continue;
            }
            let ch = line[i..].chars().next().unwrap_or('\0');
            out.push(ch);
            i += ch.len_utf8();
        }
        Ok(out)
    }

    fn tokenize_line(&self, line: &str) -> Vec<String> {
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
                let sym_len = sym.len();
                if i + sym_len <= line.len()
                    && line.is_char_boundary(i)
                    && line.is_char_boundary(i + sym_len)
                    && &line[i..i + sym_len] == sym
                    && Self::compact_set_suffix_has_right_boundary(sym, line, i + sym_len)
                {
                    tokens.push(sym.to_string());
                    i += sym_len;
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

        let mut canonical_tokens = Vec::with_capacity(tokens.len());
        for token in tokens {
            if let Some(alias_tokens) = unicode_alias_tokens(token.as_str()) {
                canonical_tokens.extend(alias_tokens.iter().map(|token| (*token).to_string()));
            } else {
                canonical_tokens.push(token);
            }
        }
        canonical_tokens
    }

    fn strip_triple_quote_comment_blocks(&self, source_code: &str) -> String {
        let mut in_comment = false;
        let mut out_lines = Vec::with_capacity(source_code.lines().count());
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
        &self,
        lines: &[&str],
        i: &mut usize,
        base_indent: usize,
        source_path: &RealOrVirtualPath,
    ) -> RuntimeResult<Vec<TokenBlock>> {
        let mut items = Vec::new();
        let mut body_indent = None;

        while *i < lines.len() {
            let raw = lines[*i];
            let line_no = *i + 1;
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
                let trimmed_start = raw.trim_start();
                if trimmed_start.is_empty() || trimmed_start.starts_with('#') {
                    *i += 1;
                    continue;
                }
                return Err(RuntimeParseError::new(
                    "unexpected indent",
                    line_no,
                    source_path.clone(),
                )
                .into());
            }

            *i += 1;
            // Strip `"..."` asides before structure checks and tokenization.
            let content = self.strip_inline_asides(content, line_no, source_path)?;
            let content = content.trim();
            if content.is_empty() {
                continue;
            }

            let header_tokens = self.tokenize_line(content);
            if header_tokens.is_empty() {
                continue;
            }

            if Self::ends_with_colon(content) {
                if *i >= lines.len() {
                    return Err(RuntimeParseError::new(
                        "block header missing body",
                        line_no,
                        source_path.clone(),
                    )
                    .into());
                }
                let next_indent = Self::indent_level(lines[*i]);
                if next_indent <= indent {
                    return Err(RuntimeParseError::new(
                        "expected indent",
                        *i + 1,
                        source_path.clone(),
                    )
                    .into());
                }
                let body = self.parse_level(lines, i, next_indent, source_path)?;
                items.push(TokenBlock::new(
                    header_tokens,
                    body,
                    line_no,
                    source_path.clone(),
                ));
            } else {
                items.push(TokenBlock::new(
                    header_tokens,
                    vec![],
                    line_no,
                    source_path.clone(),
                ));
            }

            if let Some(expected) = body_indent {
                if indent != expected {
                    return Err(RuntimeParseError::new(
                        "inconsistent indent",
                        line_no,
                        source_path.clone(),
                    )
                    .into());
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
        s.trim_end().ends_with(COLON)
    }

    fn is_identifier_start_char(ch: char) -> bool {
        ch == '_' || ch.is_alphabetic()
    }

    fn is_identifier_continue_char(ch: char) -> bool {
        ch == '_' || ch.is_alphanumeric()
    }

    fn compact_set_suffix_has_right_boundary(token: &str, line: &str, end: usize) -> bool {
        if !matches!(
            token,
            N_POSITIVE
                | Z_POSITIVE
                | Q_POSITIVE
                | R_POSITIVE
                | Z_NEGATIVE
                | Q_NEGATIVE
                | R_NEGATIVE
                | Z_NOT_ZERO
                | Q_NOT_ZERO
                | R_NOT_ZERO
                | C_NOT_ZERO
                | UNICODE_N_POSITIVE
                | UNICODE_Z_POSITIVE
                | UNICODE_Q_POSITIVE
                | UNICODE_R_POSITIVE
                | UNICODE_Z_NEGATIVE
                | UNICODE_Q_NEGATIVE
                | UNICODE_R_NEGATIVE
                | UNICODE_Z_NOT_ZERO
                | UNICODE_Q_NOT_ZERO
                | UNICODE_R_NOT_ZERO
                | UNICODE_C_NOT_ZERO
        ) {
            return true;
        }
        if end == line.len() {
            return true;
        }
        let next = line[end..].chars().next().unwrap_or('\0');
        next.is_whitespace()
            || matches!(
                next,
                ',' | ':' | ')' | ']' | '}' | '>' | '=' | '!' | '<' | '$' | '{' | '#'
            )
    }
}

impl Default for Tokenizer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokenizes_one_plus_one_equals_two() {
        let blocks = Tokenizer::new()
            .tokenize("1 + 1 = 2", RealOrVirtualPath::Eval)
            .expect("tokenize");
        assert_eq!(blocks.len(), 1);
        assert_eq!(
            blocks[0].header,
            vec!["1", "+", "1", "=", "2"]
                .into_iter()
                .map(str::to_string)
                .collect::<Vec<_>>()
        );
        assert!(blocks[0].body.is_empty());
        assert_eq!(blocks[0].line, 1);
    }

    #[test]
    fn tokenizes_indented_block_body() {
        let source = "forall x R:\n    x = x\n";
        let blocks = Tokenizer::new()
            .tokenize(source, RealOrVirtualPath::Eval)
            .expect("tokenize");
        assert_eq!(blocks.len(), 1);
        assert_eq!(
            blocks[0].header,
            vec!["forall", "x", "R", ":"]
                .into_iter()
                .map(str::to_string)
                .collect::<Vec<_>>()
        );
        assert_eq!(blocks[0].body.len(), 1);
        assert_eq!(
            blocks[0].body[0].header,
            vec!["x", "=", "x"]
                .into_iter()
                .map(str::to_string)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn strips_inline_aside_quotes() {
        let source = "forall a R:\n    \"我们有\" a ^ 2 >= 0\n";
        let blocks = Tokenizer::new()
            .tokenize(source, RealOrVirtualPath::Eval)
            .expect("tokenize");
        assert_eq!(blocks.len(), 1);
        assert_eq!(
            blocks[0].body[0].header,
            vec!["a", "^", "2", ">=", "0"]
                .into_iter()
                .map(str::to_string)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn aside_after_colon_still_opens_block() {
        let source = "forall a R: \"note\"\n    a = a\n";
        let blocks = Tokenizer::new()
            .tokenize(source, RealOrVirtualPath::Eval)
            .expect("tokenize");
        assert_eq!(blocks.len(), 1);
        assert_eq!(
            blocks[0].header,
            vec!["forall", "a", "R", ":"]
                .into_iter()
                .map(str::to_string)
                .collect::<Vec<_>>()
        );
        assert_eq!(blocks[0].body.len(), 1);
    }

    #[test]
    fn unclosed_inline_aside_is_error() {
        let err = Tokenizer::new()
            .tokenize("1 = 1 \"oops", RealOrVirtualPath::Eval)
            .expect_err("unclosed aside");
        let msg = format!("{err:?}");
        assert!(msg.contains("unclosed inline aside"), "{msg}");
    }
}
