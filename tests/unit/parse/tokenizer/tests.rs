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
fn unicode_identifier_is_one_token() {
    let tokenizer = Tokenizer::new();
    assert_eq!(
        tokenizer
            .tokenize_line("thm 自反等式:", test_line_file())
            .unwrap(),
        vec!["thm", "自反等式", ":"]
    );
}

#[test]
fn unicode_math_aliases_normalize_to_canonical_ascii_tokens() {
    let tokenizer = Tokenizer::new();
    let cases = [
        ("∀", vec!["forall"]),
        ("∃", vec!["exist"]),
        ("∃!", vec!["exist", "!"]),
        ("≤", vec!["<="]),
        ("≥", vec![">="]),
        ("≠", vec!["!="]),
        ("→", vec!["=>"]),
        ("↔", vec!["<=>"]),
        ("∧", vec!["and"]),
        ("∨", vec!["or"]),
        ("¬", vec!["not"]),
        ("∈", vec!["$", "in"]),
        ("⊆", vec!["$", "subset"]),
        ("⊇", vec!["$", "superset"]),
        ("⊊", vec!["$", "proper_subset"]),
        ("⊋", vec!["$", "proper_superset"]),
        ("⊂", vec!["$", "proper_subset"]),
        ("ℕ", vec!["N"]),
        ("ℤ", vec!["Z"]),
        ("ℚ", vec!["Q"]),
        ("ℝ", vec!["R"]),
        ("ℂ", vec!["C"]),
        ("ℕ+", vec!["N+"]),
        ("ℤ+", vec!["Z+"]),
        ("ℚ+", vec!["Q+"]),
        ("ℝ+", vec!["R+"]),
        ("ℤ-", vec!["Z-"]),
        ("ℚ-", vec!["Q-"]),
        ("ℝ-", vec!["R-"]),
        ("ℤ*", vec!["Z*"]),
        ("ℚ*", vec!["Q*"]),
        ("ℝ*", vec!["R*"]),
        ("ℂ*", vec!["C*"]),
        ("π", vec!["pi"]),
        ("∅", vec!["{", "}"]),
    ];

    for (source, expected) in cases {
        assert_eq!(
            tokenizer.tokenize_line(source, test_line_file()).unwrap(),
            expected,
            "{source}"
        );
    }
    assert_eq!(
        tokenizer
            .tokenize_line("∃! x ℕ st {x ∈ ∅}", test_line_file())
            .unwrap(),
        vec!["exist", "!", "x", "N", "st", "{", "x", "$", "in", "{", "}", "}"]
    );
}

#[test]
fn unicode_aliases_do_not_rewrite_quoted_paths_or_longer_identifiers() {
    let tokenizer = Tokenizer::new();
    assert_eq!(
        tokenizer
            .tokenize_line("import \"../ℝ/π/∅\" as Math", test_line_file())
            .unwrap(),
        vec!["import", "\"", ".", ".", "/", "ℝ", "/", "π", "/", "∅", "\"", "as", "Math"]
    );
    assert_eq!(
        tokenizer
            .tokenize_line("π_value ℝspace", test_line_file())
            .unwrap(),
        vec!["π_value", "ℝspace"]
    );
}

#[test]
fn unicode_infix_operators_remain_distinct_parser_tokens() {
    let tokenizer = Tokenizer::new();
    assert_eq!(
        tokenizer
            .tokenize_line("x ∉ A, A ⊂ B, A ∪ B, A ∩ B, A × B", test_line_file())
            .unwrap(),
        vec![
            "x",
            "∉",
            "A",
            ",",
            "A",
            "$",
            "proper_subset",
            "B",
            ",",
            "A",
            "∪",
            "B",
            ",",
            "A",
            "∩",
            "B",
            ",",
            "A",
            "×",
            "B"
        ]
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
fn matrix_operator_tokens_preserve_apostrophe_and_interval_prefix() {
    let tokenizer = Tokenizer::new();
    assert_eq!(
        tokenizer
            .tokenize_line("A '+ B '- C '* D '^ 2", test_line_file())
            .unwrap(),
        vec!["A", "'+", "B", "'-", "C", "'*", "D", "'^", "2"]
    );
    assert_eq!(
        tokenizer.tokenize_line("3 *' A", test_line_file()).unwrap(),
        vec!["3", "*'", "A"]
    );
    assert_eq!(
        tokenizer
            .tokenize_line("'(0, 1)", test_line_file())
            .unwrap(),
        vec!["'", "(", "0", ",", "1", ")"]
    );
}

#[test]
fn compact_numeric_set_spellings_require_adjacency() {
    let tokenizer = Tokenizer::new();
    assert_eq!(
        tokenizer
            .tokenize_line("set+ N+ Z+ Q+ R+ Z- Q- R- Z* Q* R* C*", test_line_file())
            .unwrap(),
        vec!["set", "+", "N+", "Z+", "Q+", "R+", "Z-", "Q-", "R-", "Z*", "Q*", "R*", "C*"]
    );
    assert_eq!(
        tokenizer
            .tokenize_line("set + N + Z - R *", test_line_file())
            .unwrap(),
        vec!["set", "+", "N", "+", "Z", "-", "R", "*"]
    );
    // `C*` is a standard set, while adjacent multiplication and `N*` stay split.
    assert_eq!(
        tokenizer
            .tokenize_line("C* C*x N*", test_line_file())
            .unwrap(),
        vec!["C*", "C", "*", "x", "N", "*"]
    );
    assert_eq!(
        tokenizer
            .tokenize_line("N+1 R-x Q-(a) R*x", test_line_file())
            .unwrap(),
        vec!["N", "+", "1", "R", "-", "x", "Q", "-", "(", "a", ")", "R", "*", "x"]
    );
    assert_eq!(
        tokenizer
            .tokenize_line("ℕ+1 ℝ-x ℚ-(a) ℝ*x ℕ*", test_line_file())
            .unwrap(),
        vec!["N", "+", "1", "R", "-", "x", "Q", "-", "(", "a", ")", "R", "*", "x", "N", "*"]
    );
}
