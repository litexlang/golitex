//! Human-facing text from IR: strip plain-identifier `#id#` wrappers.
//!
//! IR keeps `#3#x`; readable shows `x`. Used by JSON Normal output and other
//! human-facing surfaces. Not a second semantic key — only presentation.

/// Turn IR text into readable text by removing `#<digits>#` wrappers.
/// Example: `#1#k $in N` → `k $in N`.
pub fn readable_string_from_ir_text(ir_text: &str) -> String {
    let mut result = String::with_capacity(ir_text.len());
    let mut rest = ir_text;
    while let Some(start) = rest.find('#') {
        result.push_str(&rest[..start]);
        let after_hash = &rest[start + 1..];
        let digit_len = after_hash
            .chars()
            .take_while(|c| c.is_ascii_digit())
            .count();
        if digit_len > 0 {
            let after_digits = &after_hash[digit_len..];
            if let Some(stripped) = after_digits.strip_prefix('#') {
                rest = stripped;
                continue;
            }
        }
        result.push('#');
        rest = after_hash;
    }
    result.push_str(rest);
    result
}

#[cfg(test)]
mod tests {
    use super::readable_string_from_ir_text;

    #[test]
    fn strips_plain_identifier_id_wrappers() {
        assert_eq!(
            readable_string_from_ir_text("#1#k $in N"),
            "k $in N"
        );
        assert_eq!(
            readable_string_from_ir_text("#2#a = 1 or #2#a = 2"),
            "a = 1 or a = 2"
        );
        assert_eq!(readable_string_from_ir_text("1 + 1 = 2"), "1 + 1 = 2");
        assert_eq!(readable_string_from_ir_text("#"), "#");
        assert_eq!(readable_string_from_ir_text("#12"), "#12");
    }
}
