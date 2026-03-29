
use crate::prelude::*;
pub fn tokenize_line(line: &str) -> Vec<String> {
    let symbols = key_symbols_sorted_by_len_desc();
    let mut tokens = Vec::with_capacity(line.len());
    let mut i = 0;
    let line = line.trim_end();
    let bytes = line.as_bytes();

    while i < bytes.len() {
        // Ensure `i` is always on a UTF-8 char boundary before slicing `line[i..]`.
        // Otherwise Rust will unreachable when `&line[i..j]` is evaluated.
        if !line.is_char_boundary(i) {
            let mut char_start = i;
            while char_start > 0 && !line.is_char_boundary(char_start) {
                char_start -= 1;
            }
            i = char_start;
            continue;
        }

        // Single-line comment: ignore everything after `#`.
        if bytes[i] == b'#' {
            break;
        }

        if bytes[i].is_ascii_whitespace() {
            i += 1;
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
            while i < bytes.len() && (bytes[i].is_ascii_digit() || bytes[i] == b'.') {
                i += 1;
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
