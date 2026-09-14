//! Shared helper for display strings derived from internal representation.

// Remove `#<digits>#` identifier id tags from an internal representation string.
pub fn strip_identifier_id_tags(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'#' {
            let mut j = i + 1;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 1 && j < bytes.len() && bytes[j] == b'#' {
                i = j + 1;
                continue;
            }
        }
        out.push(bytes[i] as char);
        i += 1;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::strip_identifier_id_tags;

    #[test]
    fn strips_identifier_id_tags_only() {
        assert_eq!(strip_identifier_id_tags("#12#x $in #3#A"), "x $in A");
        assert_eq!(strip_identifier_id_tags("M::#12#x"), "M::x");
    }
}
