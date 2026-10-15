use super::mapped_line::MappedLine;
use super::symbols::{
    key_symbols_sorted_by_len_desc, unicode_alias_tokens, COLON, C_NOT_ZERO, N_POSITIVE,
    Q_NEGATIVE, Q_NOT_ZERO, Q_POSITIVE, R_NEGATIVE, R_NOT_ZERO, R_POSITIVE, UNICODE_C_NOT_ZERO,
    UNICODE_N_POSITIVE, UNICODE_Q_NEGATIVE, UNICODE_Q_NOT_ZERO, UNICODE_Q_POSITIVE,
    UNICODE_R_NEGATIVE, UNICODE_R_NOT_ZERO, UNICODE_R_POSITIVE, UNICODE_Z_NEGATIVE,
    UNICODE_Z_NOT_ZERO, UNICODE_Z_POSITIVE, Z_NEGATIVE, Z_NOT_ZERO, Z_POSITIVE,
};
use super::token_block::TokenBlock;
use crate::runtime::{CodeSource, RuntimeParseError, RuntimeResult};
use std::ops::Range;
use std::sync::Arc;

pub struct Tokenizer;

impl Tokenizer {
    pub fn new() -> Self {
        Self
    }

    pub fn tokenize(&self, code: &str, source_path: CodeSource) -> RuntimeResult<Vec<TokenBlock>> {
        let result = (|| {
            let stripped = self.strip_triple_quote_comment_blocks(code, &source_path)?;
            let lines = self.join_line_continuations(&stripped, code, &source_path)?;
            let mut index = 0;
            self.parse_level(&lines, &mut index, 0, &source_path, &Arc::from(code))
        })();
        result.map_err(|error: crate::runtime::RuntimeError| error.with_source_context(code))
    }

    // Skip ASCII `"..."` inline asides. They are not tokens and must not cross lines.
    fn strip_inline_asides(
        &self,
        line: &MappedLine,
        line_no: usize,
        source_path: &CodeSource,
        source: &str,
    ) -> RuntimeResult<MappedLine> {
        let mut out = String::with_capacity(line.text.len());
        let mut offsets = Vec::new();
        let mut i = 0;
        let bytes = line.text.as_bytes();
        while i < bytes.len() {
            if bytes[i] == b'"' {
                let quote_start = i;
                i += 1;
                let mut closed = false;
                while i < bytes.len() {
                    if bytes[i] == b'"' {
                        i += 1;
                        closed = true;
                        break;
                    }
                    let ch = line.text[i..].chars().next().unwrap_or('\0');
                    i += ch.len_utf8();
                }
                if !closed {
                    return Err(RuntimeParseError::new(
                        "unclosed inline aside `\"...\"`",
                        line_no,
                        source_path.clone(),
                    )
                    .with_source(source, line.offsets[quote_start])
                    .into());
                }
                continue;
            }
            let ch = line.text[i..].chars().next().unwrap_or('\0');
            out.push(ch);
            offsets.extend_from_slice(&line.offsets[i..i + ch.len_utf8()]);
            i += ch.len_utf8();
        }
        Ok(MappedLine::new(out, offsets))
    }

    fn tokenize_line(&self, mapped: &MappedLine) -> (Vec<String>, Vec<Range<usize>>) {
        let line = mapped.text.trim_end();
        let symbols = key_symbols_sorted_by_len_desc();
        let mut tokens = Vec::with_capacity(line.len());
        let mut spans = Vec::new();
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
                    spans.push(mapped.offsets[i]..mapped.offsets[i + sym_len - 1] + 1);
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
                spans.push(mapped.offsets[start]..mapped.offsets[i - 1] + 1);
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
                spans.push(mapped.offsets[start]..mapped.offsets[i - 1] + 1);
                continue;
            }

            let ch = line[i..].chars().next().unwrap_or('\0');
            tokens.push(ch.to_string());
            spans.push(mapped.offsets[i]..mapped.offsets[i + ch.len_utf8() - 1] + 1);
            i += ch.len_utf8();
        }

        let mut canonical_tokens = Vec::with_capacity(tokens.len());
        let mut canonical_spans = Vec::with_capacity(spans.len());
        for (token, span) in tokens.into_iter().zip(spans) {
            if let Some(alias_tokens) = unicode_alias_tokens(token.as_str()) {
                canonical_tokens.extend(alias_tokens.iter().map(|token| (*token).to_string()));
                canonical_spans.extend(alias_tokens.iter().map(|_| span.clone()));
            } else {
                canonical_tokens.push(token);
                canonical_spans.push(span);
            }
        }
        (canonical_tokens, canonical_spans)
    }

    // A line that is exactly `"""` after trim opens/closes a block comment.
    // Unclosed block comments are errors. Distinct from inline `"..."` asides.
    fn strip_triple_quote_comment_blocks(
        &self,
        source_code: &str,
        source_path: &CodeSource,
    ) -> RuntimeResult<String> {
        let mut in_comment = false;
        let mut open_line = 0;
        let mut out_lines = Vec::with_capacity(source_code.lines().count());
        for (idx, line) in source_code.lines().enumerate() {
            let line_no = idx + 1;
            let trimmed = line.trim();
            if trimmed == "\"\"\"" {
                if in_comment {
                    in_comment = false;
                } else {
                    in_comment = true;
                    open_line = line_no;
                }
                out_lines.push(String::new());
                continue;
            }
            if in_comment {
                out_lines.push(String::new());
            } else {
                out_lines.push(line.to_string());
            }
        }
        if in_comment {
            return Err(RuntimeParseError::new(
                "unclosed block comment `\"\"\"...\"\"\"`",
                open_line,
                source_path.clone(),
            )
            .into());
        }
        Ok(out_lines.join("\n"))
    }

    // Trailing `\\` joins the next physical line into this one. Mid-line `\\` is
    // not continuation (distinct from template prefix `\`). A `#` comment after
    // `\\` is allowed and dropped with the marker. Consumed lines are blanked
    // so later line numbers stay stable.
    //
    // Example:
    //   a = b \\  # note
    //      = c
    // becomes the logical line `a = b    = c`.
    fn join_line_continuations(
        &self,
        source_code: &str,
        original_code: &str,
        source_path: &CodeSource,
    ) -> RuntimeResult<Vec<MappedLine>> {
        let mut start = 0;
        let starts: Vec<usize> = original_code
            .split_inclusive('\n')
            .map(|line| {
                let offset = start;
                start += line.len();
                offset
            })
            .collect();
        let mut lines: Vec<MappedLine> = source_code
            .lines()
            .enumerate()
            .map(|(index, line)| {
                MappedLine::new(
                    line.to_string(),
                    (starts[index]..starts[index] + line.len()).collect(),
                )
            })
            .collect();
        let mut i = 0;
        while i < lines.len() {
            if !Self::line_ends_with_line_continuation(&lines[i].text) {
                i += 1;
                continue;
            }
            let open_line = i + 1;
            let start = i;
            let mut joined = MappedLine::new(lines[i].text.clone(), lines[i].offsets.clone());
            while Self::line_ends_with_line_continuation(&joined.text) {
                joined.text = Self::strip_trailing_line_continuation(&joined.text);
                joined.offsets.truncate(joined.text.len());
                i += 1;
                if i >= lines.len() {
                    return Err(RuntimeParseError::new(
                        "unclosed line continuation `\\\\`",
                        open_line,
                        source_path.clone(),
                    )
                    .into());
                }
                joined.text.push_str(&lines[i].text);
                joined.offsets.extend_from_slice(&lines[i].offsets);
                lines[i] = MappedLine::new(String::new(), Vec::new());
            }
            lines[start] = joined;
            i = start + 1;
        }
        Ok(lines)
    }

    fn parse_level(
        &self,
        lines: &[MappedLine],
        i: &mut usize,
        base_indent: usize,
        source_path: &CodeSource,
        source: &Arc<str>,
    ) -> RuntimeResult<Vec<TokenBlock>> {
        let mut items = Vec::new();
        let mut body_indent = None;

        while *i < lines.len() {
            let mapped = &lines[*i];
            let raw = mapped.text.as_str();
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
                .with_source(source, mapped.offsets[raw.len() - raw.trim_start().len()])
                .into());
            }

            *i += 1;
            // Hash comments may contain arbitrary quotes. Keep hashes inside
            // actual inline asides, then validate only the remaining code.
            let content = Self::code_prefix_before_hash_comment(raw);
            let content = MappedLine::new(
                content.to_string(),
                mapped.offsets[..content.len()].to_vec(),
            );
            // Strip `"..."` asides before structure checks and tokenization.
            let content = self.strip_inline_asides(&content, line_no, source_path, source)?;
            if content.text.trim().is_empty() {
                continue;
            }

            let (header_tokens, token_spans) = self.tokenize_line(&content);
            if header_tokens.is_empty() {
                continue;
            }
            for (token, span) in header_tokens.iter().zip(&token_spans) {
                if token.starts_with("__") {
                    return Err(RuntimeParseError::new(
                        format!(
                            "names starting with `__` are reserved for Lean/codegen and cannot appear in {} source",
                            crate::LITEX
                        ),
                        line_no,
                        source_path.clone(),
                    )
                    .with_source(source, span.start)
                    .into());
                }
            }

            let body = if Self::ends_with_colon(&content.text) {
                if *i >= lines.len() {
                    return Err(RuntimeParseError::new(
                        "block header missing body",
                        line_no,
                        source_path.clone(),
                    )
                    .into());
                }
                let next_indent = Self::indent_level(&lines[*i].text);
                if next_indent <= indent {
                    return Err(RuntimeParseError::new(
                        "expected indent",
                        *i + 1,
                        source_path.clone(),
                    )
                    .into());
                }
                let body = self.parse_level(lines, i, next_indent, source_path, source)?;
                if body.is_empty() {
                    return Err(RuntimeParseError::new(
                        "block header requires a nonempty body",
                        line_no,
                        source_path.clone(),
                    )
                    .into());
                }
                body
            } else {
                Vec::new()
            };
            let mut block = TokenBlock::new(header_tokens, body, line_no, source_path.clone());
            block.source = Some(source.clone());
            block.token_spans = token_spans;
            items.push(block);

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

    // Code region before a `#` that is outside `"..."` asides.
    fn code_prefix_before_hash_comment(line: &str) -> &str {
        let bytes = line.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'"' {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'"' {
                        i += 1;
                        break;
                    }
                    let ch = line[i..].chars().next().unwrap_or('\0');
                    i += ch.len_utf8();
                }
                continue;
            }
            if bytes[i] == b'#' {
                return &line[..i];
            }
            let ch = line[i..].chars().next().unwrap_or('\0');
            i += ch.len_utf8();
        }
        line
    }

    fn line_ends_with_line_continuation(line: &str) -> bool {
        Self::code_prefix_before_hash_comment(line)
            .trim_end()
            .ends_with("\\\\")
    }

    // Drop trailing `\\` and any following `#` comment so the next line is not
    // commented out after join.
    fn strip_trailing_line_continuation(line: &str) -> String {
        let code = Self::code_prefix_before_hash_comment(line);
        let trimmed = code.trim_end();
        trimmed[..trimmed.len() - 2].to_string()
    }
}

impl Default for Tokenizer {
    fn default() -> Self {
        Self::new()
    }
}
