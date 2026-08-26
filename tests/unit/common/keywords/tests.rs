use super::*;

#[test]
fn output_labels_are_not_source_keywords() {
    assert!(!is_keyword(SUCCESS_COLON));
    assert!(!is_keyword(UNKNOWN_COLON));
}

#[test]
fn by_def_uses_a_contextual_keyword() {
    assert!(!is_keyword(DEF));
}

#[test]
fn let_is_a_source_keyword() {
    assert!(is_keyword(LET));
}

#[test]
fn release_is_a_source_keyword() {
    assert!(is_keyword(RELEASE));
}
