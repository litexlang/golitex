//! Multi-character symbols owned by the new pipeline tokenizer.
//!
//! Values match the legacy keyword surface so later parse/obj/stmt stages can
//! keep the same spelling.  This module does not import `crate::syntax`.

/// Symbols matched longest-first while scanning a line.
pub fn key_symbols_sorted_by_len_desc() -> Vec<&'static str> {
    let mut symbols = vec![
        "<=>",
        "...",
        "::",
        "!=",
        "<=",
        ">=",
        "=>",
        "N+",
        "Z+",
        "Q+",
        "R+",
        "Z-",
        "Q-",
        "R-",
        "Z*",
        "Q*",
        "R*",
        "C*",
        "ℕ+",
        "ℤ+",
        "ℚ+",
        "ℝ+",
        "ℤ-",
        "ℚ-",
        "ℝ-",
        "ℤ*",
        "ℚ*",
        "ℝ*",
        "ℂ*",
        "'^",
        "'*",
        "*'",
        "'+",
        "'-",
        "+",
        "-",
        "*",
        "/",
        "%",
        "^",
        "(",
        ")",
        ",",
        "{",
        "}",
        "=",
        "<",
        ">",
        "[",
        "]",
        "\"",
        ":",
        ".",
        "?",
        "$",
        "&",
        "\\",
        "'",
        "∪",
        "∩",
        "×",
        "∉",
    ];
    symbols.sort_by(|a, b| b.len().cmp(&a.len()));
    symbols
}

pub const COLON: &str = ":";
pub const DOUBLE_QUOTE: &str = "\"";

pub const N_POSITIVE: &str = "N+";
pub const Z_POSITIVE: &str = "Z+";
pub const Q_POSITIVE: &str = "Q+";
pub const R_POSITIVE: &str = "R+";
pub const Z_NEGATIVE: &str = "Z-";
pub const Q_NEGATIVE: &str = "Q-";
pub const R_NEGATIVE: &str = "R-";
pub const Z_NOT_ZERO: &str = "Z*";
pub const Q_NOT_ZERO: &str = "Q*";
pub const R_NOT_ZERO: &str = "R*";
pub const C_NOT_ZERO: &str = "C*";
pub const UNICODE_N_POSITIVE: &str = "ℕ+";
pub const UNICODE_Z_POSITIVE: &str = "ℤ+";
pub const UNICODE_Q_POSITIVE: &str = "ℚ+";
pub const UNICODE_R_POSITIVE: &str = "ℝ+";
pub const UNICODE_Z_NEGATIVE: &str = "ℤ-";
pub const UNICODE_Q_NEGATIVE: &str = "ℚ-";
pub const UNICODE_R_NEGATIVE: &str = "ℝ-";
pub const UNICODE_Z_NOT_ZERO: &str = "ℤ*";
pub const UNICODE_Q_NOT_ZERO: &str = "ℚ*";
pub const UNICODE_R_NOT_ZERO: &str = "ℝ*";
pub const UNICODE_C_NOT_ZERO: &str = "ℂ*";

/// Expand a unicode spelling into the canonical ASCII token sequence.
pub fn unicode_alias_tokens(token: &str) -> Option<&'static [&'static str]> {
    match token {
        "∀" => Some(&["forall"]),
        "∃" => Some(&["exist"]),
        "≤" => Some(&["<="]),
        "≥" => Some(&[">="]),
        "≠" => Some(&["!="]),
        "→" => Some(&["=>"]),
        "↔" => Some(&["<=>"]),
        "∧" => Some(&["and"]),
        "∨" => Some(&["or"]),
        "¬" => Some(&["not"]),
        "∈" => Some(&["$", "in"]),
        "⊆" => Some(&["$", "subset"]),
        "⊇" => Some(&["$", "superset"]),
        "⊊" | "⊂" => Some(&["$", "proper_subset"]),
        "⊋" => Some(&["$", "proper_superset"]),
        "ℕ" => Some(&["N"]),
        "ℤ" => Some(&["Z"]),
        "ℚ" => Some(&["Q"]),
        "ℝ" => Some(&["R"]),
        "ℂ" => Some(&["C"]),
        UNICODE_N_POSITIVE => Some(&[N_POSITIVE]),
        UNICODE_Z_POSITIVE => Some(&[Z_POSITIVE]),
        UNICODE_Q_POSITIVE => Some(&[Q_POSITIVE]),
        UNICODE_R_POSITIVE => Some(&[R_POSITIVE]),
        UNICODE_Z_NEGATIVE => Some(&[Z_NEGATIVE]),
        UNICODE_Q_NEGATIVE => Some(&[Q_NEGATIVE]),
        UNICODE_R_NEGATIVE => Some(&[R_NEGATIVE]),
        UNICODE_Z_NOT_ZERO => Some(&[Z_NOT_ZERO]),
        UNICODE_Q_NOT_ZERO => Some(&[Q_NOT_ZERO]),
        UNICODE_R_NOT_ZERO => Some(&[R_NOT_ZERO]),
        UNICODE_C_NOT_ZERO => Some(&[C_NOT_ZERO]),
        "π" => Some(&["pi"]),
        "∅" => Some(&["{", "}"]),
        _ => None,
    }
}
