use crate::prelude::*;
use std::collections::HashMap;

const MACRO: &str = "macro";
const MAX_AT_EXPAND_ROUNDS: usize = 256;

pub struct Tokenizer {
    pub macros: Vec<HashMap<String, String>>,
}

impl Tokenizer {
    pub fn new() -> Self {
        Self {
            macros: vec![HashMap::new()],
        }
    }

    pub fn push_scope(&mut self) {
        self.macros.push(HashMap::new());
    }

    pub fn pop_scope(&mut self) {
        debug_assert!(
            self.macros.len() > 1,
            "tokenizer: pop_scope underflow (root scope must remain)"
        );
        if self.macros.len() > 1 {
            self.macros.pop();
        }
    }

    fn lookup_macro(&self, name: &str) -> Option<&str> {
        for m in self.macros.iter().rev() {
            if let Some(v) = m.get(name) {
                return Some(v.as_str());
            }
        }
        None
    }

    fn define_macro(&mut self, name: String, body: String) {
        if let Some(top) = self.macros.last_mut() {
            top.insert(name, body);
        }
    }

    /// Expand `@Name` using innermost-to-outermost macro scopes. A defined identifier after `@`
    /// must exist in some scope or tokenization fails.
    fn expand_at_references(
        &self,
        line: &str,
        line_file: LineFile,
    ) -> Result<String, RuntimeError> {
        let mut work = line.to_string();
        for _ in 0..MAX_AT_EXPAND_ROUNDS {
            if !work.contains('@') {
                break;
            }
            let next = expand_at_one_round(self, &work, line_file.clone())?;
            if next == work {
                break;
            }
            work = next;
        }
        Ok(work)
    }

    pub fn tokenize_line(
        &mut self,
        line: &str,
        line_file: LineFile,
    ) -> Result<Vec<String>, RuntimeError> {
        let line = line.trim_end();
        if try_consume_macro_definition(self, line, line_file.clone())? {
            return Ok(vec![]);
        }
        let expanded = self.expand_at_references(line, line_file)?;
        Ok(self.tokenize_expanded_line(&expanded))
    }

    fn tokenize_expanded_line(&self, line: &str) -> Vec<String> {
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

            if bytes[i] == b'"' {
                let start = i;
                i += 1;
                while i < bytes.len() && bytes[i] != b'"' {
                    if bytes[i] == b'\\' {
                        i += 1;
                    }
                    i += 1;
                }
                if i < bytes.len() {
                    i += 1;
                }
                tokens.push(line[start..i].to_string());
                continue;
            }

            if bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' {
                let start = i;
                i += 1;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
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
}

fn expand_at_one_round(
    tokenizer: &Tokenizer,
    input: &str,
    line_file: LineFile,
) -> Result<String, RuntimeError> {
    let mut out = String::new();
    let mut rest = input;
    while !rest.is_empty() {
        if let Some(at_pos) = rest.find('@') {
            out.push_str(&rest[..at_pos]);
            rest = &rest[at_pos + 1..];
            let name_len = ident_prefix_byte_len(rest);
            if name_len > 0 {
                let name = &rest[..name_len];
                if let Some(repl) = tokenizer.lookup_macro(name) {
                    out.push_str(repl);
                    rest = &rest[name_len..];
                    continue;
                }
                return Err(undefined_macro_err(name, line_file));
            }
            out.push('@');
        } else {
            out.push_str(rest);
            break;
        }
    }
    Ok(out)
}

fn undefined_macro_err(name: &str, line_file: LineFile) -> RuntimeError {
    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
        None,
        format!("undefined macro `@{}`", name),
        line_file,
        None,
        vec![],
    )))
}

/// Byte length of the `@`-macro name: ASCII letters, digits, and `_`, same rules as a typical ident
/// (`@Nat:` → name length of `Nat`, leaving `:` for normal tokenization).
fn ident_prefix_byte_len(s: &str) -> usize {
    let mut i = 0usize;
    let mut chars = s.chars();
    let Some(c) = chars.next() else {
        return 0;
    };
    if !(c.is_ascii_alphanumeric() || c == '_') {
        return 0;
    }
    i += c.len_utf8();
    for c in chars {
        if c.is_ascii_alphanumeric() || c == '_' {
            i += c.len_utf8();
        } else {
            break;
        }
    }
    i
}

fn skip_ascii_ws(s: &str, mut i: usize) -> usize {
    let b = s.as_bytes();
    while i < b.len() && b[i].is_ascii_whitespace() {
        i += 1;
    }
    i
}

fn parse_ascii_ident<'a>(s: &'a str, mut i: usize) -> Option<(&'a str, usize)> {
    let b = s.as_bytes();
    if i >= b.len() {
        return None;
    }
    if !(b[i].is_ascii_alphabetic() || b[i] == b'_') {
        return None;
    }
    let start = i;
    i += 1;
    while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
        i += 1;
    }
    Some((&s[start..i], i))
}

/// Single place to edit allowed macro bodies: ASCII alnum, ASCII space, `_`, and this punctuation
/// (enough for typical Litex tokens; everything else—including `@`, tab, non-ASCII—is rejected).
fn is_allowed_macro_string_char(c: char) -> bool {
    if !c.is_ascii() {
        return false;
    }
    if c.is_ascii_alphanumeric() || c == ' ' || c == '_' {
        return true;
    }
    matches!(
        c,
        '=' | '<' | '>'
            | '(' | ')' | '[' | ']' | '{' | '}'
            | ',' | '.' | ':' | ';'
            | '+' | '-' | '*' | '/' | '%' | '^'
            | '|' | '&' | '!' | '~' | '?'
            | '$' | '\\' | '\'' | '"'
    )
}

fn push_macro_replacement_char(
    out: &mut String,
    ch: char,
    line_file: LineFile,
) -> Result<(), RuntimeError> {
    if !is_allowed_macro_string_char(ch) {
        return Err(macro_parse_err(
            "macro: replacement string may contain only ASCII letters, digits, space, underscore, and basic punctuation",
            line_file,
        ));
    }
    out.push(ch);
    Ok(())
}

/// Parse `"..."` with `\"` and `\\` escapes; `i` must point at opening `"`.
/// Each decoded character must satisfy `is_allowed_macro_string_char`.
fn parse_double_quoted_payload(
    s: &str,
    i: usize,
    line_file: LineFile,
) -> Result<(String, usize), RuntimeError> {
    let b = s.as_bytes();
    if i >= b.len() || b[i] != b'"' {
        return Err(macro_parse_err(
            "macro: expected opening `\"` for replacement string",
            line_file,
        ));
    }
    let mut j = i + 1;
    let mut out = String::new();
    while j < b.len() {
        match b[j] {
            b'"' => return Ok((out, j + 1)),
            b'\\' => {
                j += 1;
                if j >= b.len() {
                    return Err(macro_parse_err(
                        "macro: unterminated escape in string",
                        line_file,
                    ));
                }
                match b[j] {
                    b'"' => push_macro_replacement_char(&mut out, '"', line_file.clone())?,
                    b'\\' => push_macro_replacement_char(&mut out, '\\', line_file.clone())?,
                    _ => {
                        return Err(macro_parse_err(
                            "macro: only `\\\"` and `\\\\` escapes are allowed in strings",
                            line_file,
                        ));
                    }
                }
                j += 1;
            }
            _ => {
                let ch = s[j..].chars().next().unwrap();
                push_macro_replacement_char(&mut out, ch, line_file.clone())?;
                j += ch.len_utf8();
            }
        }
    }
    Err(macro_parse_err(
        "macro: unterminated string literal",
        line_file,
    ))
}

fn macro_parse_err(msg: &str, line_file: LineFile) -> RuntimeError {
    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
        None,
        msg.to_string(),
        line_file,
        None,
        vec![],
    )))
}

/// `macro Name "replacement"` (optional further `"..."` chunks are concatenated). Leading indentation is ignored.
/// The line must begin (after indent) with `macro` followed by whitespace so names like `macro_foo` are not treated as this form.
fn try_consume_macro_definition(
    tokenizer: &mut Tokenizer,
    line: &str,
    line_file: LineFile,
) -> Result<bool, RuntimeError> {
    let trimmed = line.trim_start();
    if trimmed.is_empty() || !trimmed.starts_with(MACRO) {
        return Ok(false);
    }
    let after_kw = &trimmed[MACRO.len()..];
    if !after_kw
        .chars()
        .next()
        .map(|c| c.is_whitespace())
        .unwrap_or(false)
    {
        return Ok(false);
    }
    let trim_bytes = line.len() - trimmed.len();
    let mut i = trim_bytes + MACRO.len();
    i = skip_ascii_ws(line, i);
    let (name, next) = parse_ascii_ident(line, i).ok_or_else(|| {
        macro_parse_err(
            "macro: expected macro name after `macro`",
            line_file.clone(),
        )
    })?;
    if name == MACRO {
        return Err(macro_parse_err(
            "macro: macro name must not be `macro`",
            line_file,
        ));
    }
    i = skip_ascii_ws(line, next);
    let mut replacement = String::new();
    let mut saw_string = false;
    while i < line.len() && line.as_bytes()[i] == b'"' {
        saw_string = true;
        let (chunk, after) = parse_double_quoted_payload(line, i, line_file.clone())?;
        replacement.push_str(&chunk);
        i = skip_ascii_ws(line, after);
    }
    if !saw_string {
        return Err(macro_parse_err(
            "macro: expected at least one `\"...\"` replacement string",
            line_file,
        ));
    }
    if i < line.len() && line.as_bytes()[i] != b'#' {
        return Err(macro_parse_err(
            "macro: unexpected trailing input after string (use `#` for end-of-line comment)",
            line_file,
        ));
    }
    tokenizer.define_macro(name.to_string(), replacement);
    Ok(true)
}

#[cfg(test)]
mod macro_string_allowlist_tests {
    use super::*;
    use std::rc::Rc;

    fn lf() -> LineFile {
        (1, Rc::from("t.lit"))
    }

    #[test]
    fn allows_alnum_space_and_equals() {
        let mut t = Tokenizer::new();
        assert!(t.tokenize_line(r#"macro N "1 = x""#, lf()).unwrap().is_empty());
    }

    #[test]
    fn rejects_at_sign() {
        let mut t = Tokenizer::new();
        let e = t.tokenize_line(r#"macro B "a@b""#, lf()).unwrap_err();
        match e {
            RuntimeError::ParseError(s) => assert!(s.msg.contains("only ASCII")),
            o => panic!("{:?}", o),
        }
    }

    #[test]
    fn rejects_tab() {
        let mut t = Tokenizer::new();
        assert!(t.tokenize_line("macro B \"a\tb\"", lf()).is_err());
    }

    #[test]
    fn rejects_non_ascii() {
        let mut t = Tokenizer::new();
        assert!(t.tokenize_line("macro B \"α\"", lf()).is_err());
    }
}
