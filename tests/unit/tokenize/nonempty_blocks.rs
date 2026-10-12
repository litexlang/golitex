use crate::prelude::*;

#[test]
fn colon_blocks_reject_comment_only_bodies_at_the_header() {
    for source in [
        "sketch:\n    # comment only",
        "trust:\n    # comment only",
        "trust have x R:\n    # comment only",
        "have x R:\n    # comment only",
        "prop empty(x R):\n    # comment only",
        "witness exist x R st {x = 0} from 0:\n    # comment only",
        "release axiom_of_choice: set {{1}}:\n    # comment only",
    ] {
        let error = crate::tokenize::Tokenizer::new()
            .tokenize(source, CodeSource::Eval)
            .unwrap_err();
        let RuntimeError::ParseError(error) = error else {
            panic!("expected parse error for {source}");
        };
        assert_eq!(error.message, "block header requires a nonempty body");
        assert_eq!(error.line, 1);
        assert_eq!(error.path, CodeSource::Eval);
    }
}

#[test]
fn nested_empty_colon_body_does_not_consume_its_following_sibling() {
    let source = "by cases:\n    ? 1 = 1\n    case 1 = 1:\n        # comment only\n    case 1 != 1:\n        impossible 1 = 1";
    let RuntimeError::ParseError(error) = crate::tokenize::Tokenizer::new()
        .tokenize(source, CodeSource::Eval)
        .unwrap_err()
    else {
        panic!("expected parse error");
    };
    assert_eq!(error.line, 3);
    assert_eq!(error.message, "block header requires a nonempty body");
}

#[test]
fn a_theorem_goal_counts_as_block_content_but_not_as_claim_process() {
    for source in [
        "thm refl:\n    ? 1 = 1",
        "claim:\n    ? 1 = 1",
        "sketch:\n    1 = 1",
    ] {
        let blocks = crate::tokenize::Tokenizer::new()
            .tokenize(source, CodeSource::Eval)
            .unwrap();
        assert_eq!(blocks[0].body.len(), 1);
    }
}
