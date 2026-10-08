use crate::runtime::RealOrVirtualPath;
use crate::tokenize::Tokenizer;

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
fn hash_comments_ignore_unbalanced_quotes_and_preserve_line_numbers() {
    let source = "# Finally \"there is no x satisfying\n# P(x)\" and \"every x fails.\"\n1 = 1 # \"unfinished comment\n";
    let blocks = Tokenizer::new()
        .tokenize(source, RealOrVirtualPath::Eval)
        .unwrap();
    assert_eq!(blocks.len(), 1);
    assert_eq!(blocks[0].header, vec!["1", "=", "1"]);
    assert_eq!(blocks[0].line, 3);
}

#[test]
fn hash_comment_after_a_header_does_not_hide_its_colon() {
    let source = "forall x R: # \"unfinished comment\n    x = x # \"another comment\n";
    let blocks = Tokenizer::new()
        .tokenize(source, RealOrVirtualPath::Eval)
        .unwrap();
    assert_eq!(blocks.len(), 1);
    assert_eq!(blocks[0].body.len(), 1);
    assert_eq!(blocks[0].body[0].header, vec!["x", "=", "x"]);
}

#[test]
fn hash_in_an_inline_aside_does_not_begin_a_comment() {
    let source = "1 \"note # inside aside\" = 1 # \"ignored\n";
    let blocks = Tokenizer::new()
        .tokenize(source, RealOrVirtualPath::Eval)
        .unwrap();
    assert_eq!(blocks[0].header, vec!["1", "=", "1"]);
    let error = Tokenizer::new()
        .tokenize("1 = 1 \"unclosed # inside aside\n", RealOrVirtualPath::Eval)
        .unwrap_err();
    assert!(format!("{error:?}").contains("unclosed inline aside"));
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

#[test]
fn strips_exact_triple_quote_block_comment() {
    let source = "\"\"\"\na = b\n\"\"\"\n1 = 1\n";
    let blocks = Tokenizer::new()
        .tokenize(source, RealOrVirtualPath::Eval)
        .expect("tokenize");
    assert_eq!(blocks.len(), 1);
    assert_eq!(
        blocks[0].header,
        vec!["1", "=", "1"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>()
    );
}

#[test]
fn single_quote_line_is_not_block_delimiter() {
    let err = Tokenizer::new()
        .tokenize("\"\n1 = 1\n\"\n", RealOrVirtualPath::Eval)
        .expect_err("lone quote is inline aside");
    let msg = format!("{err:?}");
    assert!(msg.contains("unclosed inline aside"), "{msg}");
}

#[test]
fn unclosed_block_comment_is_error() {
    let err = Tokenizer::new()
        .tokenize("\"\"\"\na = b\n1 = 1\n", RealOrVirtualPath::Eval)
        .expect_err("unclosed block comment");
    let msg = format!("{err:?}");
    assert!(msg.contains("unclosed block comment"), "{msg}");
}

#[test]
fn joins_trailing_double_backslash_line_continuation() {
    let source = "a = b \\\\\n   = c \\\\\n   = 1\n";
    let blocks = Tokenizer::new()
        .tokenize(source, RealOrVirtualPath::Eval)
        .expect("tokenize");
    assert_eq!(blocks.len(), 1);
    assert_eq!(
        blocks[0].header,
        vec!["a", "=", "b", "=", "c", "=", "1"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>()
    );
}

#[test]
fn mid_line_double_backslash_is_not_continuation() {
    let blocks = Tokenizer::new()
        .tokenize("a \\\\ b = b \\\\ a", RealOrVirtualPath::Eval)
        .expect("tokenize");
    assert_eq!(blocks.len(), 1);
    assert_eq!(
        blocks[0].header,
        vec!["a", "\\", "\\", "b", "=", "b", "\\", "\\", "a"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>()
    );
}

#[test]
fn unclosed_line_continuation_is_error() {
    let err = Tokenizer::new()
        .tokenize("a = b \\\\\n", RealOrVirtualPath::Eval)
        .expect_err("unclosed continuation");
    let msg = format!("{err:?}");
    assert!(msg.contains("unclosed line continuation"), "{msg}");
}

#[test]
fn line_continuation_allows_trailing_hash_comment() {
    let source = "a = b \\\\  # asdfadfs\n   = c\n";
    let blocks = Tokenizer::new()
        .tokenize(source, RealOrVirtualPath::Eval)
        .expect("tokenize");
    assert_eq!(blocks.len(), 1);
    assert_eq!(
        blocks[0].header,
        vec!["a", "=", "b", "=", "c"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>()
    );
}

#[test]
fn tokenizes_factorial_bang_and_exist_bang() {
    let tokenizer = Tokenizer::new();
    let a = tokenizer
        .tokenize("2!", RealOrVirtualPath::Eval)
        .expect("tokenize");
    assert_eq!(a[0].header, vec!["2", "!"]);
    let b = tokenizer
        .tokenize("2 != 3", RealOrVirtualPath::Eval)
        .expect("tokenize");
    assert_eq!(b[0].header, vec!["2", "!=", "3"]);
    let c = tokenizer
        .tokenize("exist! x N", RealOrVirtualPath::Eval)
        .expect("tokenize");
    assert_eq!(c[0].header, vec!["exist", "!", "x", "N"]);
    let d = tokenizer
        .tokenize("n!", RealOrVirtualPath::Eval)
        .expect("tokenize");
    assert_eq!(d[0].header, vec!["n", "!"]);
}
