use crate::keywords::key_symbols_sorted_by_len_desc;

pub fn tokenize_line(line: &str) -> Vec<String> {
    let symbols = key_symbols_sorted_by_len_desc();
    let mut tokens = Vec::new();
    let mut i = 0;
    let line = line.trim_end();
    let bytes = line.as_bytes();

    while i < bytes.len() {
        if bytes[i].is_ascii_whitespace() {
            i += 1;
            continue;
        }

        let mut matched = false;
        for &sym in &symbols {
            if i + sym.len() <= line.len() && &line[i..i + sym.len()] == sym {
                tokens.push(sym.to_string());
                i += sym.len();
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_symbol() {
        assert_eq!(tokenize_line("+"), vec!["+"]);
        assert_eq!(tokenize_line("  +  "), vec!["+"]);
    }

    #[test]
    fn test_keyword() {
        assert_eq!(tokenize_line("algo"), vec!["algo"]);
        assert_eq!(tokenize_line("  algo  "), vec!["algo"]);
    }

    #[test]
    fn test_mixed() {
        assert_eq!(tokenize_line("a+b"), vec!["a", "+", "b"]);
        assert_eq!(tokenize_line("algo x :"), vec!["algo", "x", ":"]);
        assert_eq!(tokenize_line("=>"), vec!["=>"]);
        assert_eq!(tokenize_line("x => y>= 1 > = 2"), vec!["x", "=>", "y", ">=", "1", ">", "=", "2"]);
    }
}
