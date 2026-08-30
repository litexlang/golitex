//! Lean source identifiers, indentation, and diagnostic display.

pub(in super::super) fn source_display_without_symbol_ids(source: &str) -> String {
    let mut rendered = String::with_capacity(source.len());
    let mut characters = source.chars().peekable();
    while let Some(character) = characters.next() {
        if character == '#' {
            let mut digits = String::new();
            while characters.peek().is_some_and(|next| next.is_ascii_digit()) {
                digits.push(characters.next().expect("peeked digit"));
            }
            if !digits.is_empty() && characters.peek() == Some(&'#') {
                characters.next();
                continue;
            }
            rendered.push('#');
            rendered.push_str(&digits);
        } else {
            rendered.push(character);
        }
    }
    rendered
}

pub(in super::super) fn lean_identifier(source: &str) -> String {
    let mut result = source
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || character == '_' {
                character
            } else {
                '_'
            }
        })
        .collect::<String>();
    if result.is_empty() {
        result.push('_');
    }
    result
}

pub(in super::super) fn indent_lines(text: &str, spaces: usize) -> String {
    let indentation = " ".repeat(spaces);
    text.lines()
        .map(|line| format!("{indentation}{line}"))
        .collect::<Vec<_>>()
        .join("\n")
}
