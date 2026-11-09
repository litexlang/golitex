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

#[test]
fn leading_trivia_preserves_body_and_sibling_physical_lines() {
    for source in [
        "forall x R:\n\n# comment\n\n    x = x\n1 = 1",
        "forall x R, \\\\\n    y R:\n\n# comment\n    x + y = y + x\n1 = 1",
    ] {
        let blocks = crate::tokenize::Tokenizer::new()
            .tokenize(source, CodeSource::Eval)
            .unwrap();
        assert_eq!(blocks.len(), 2);
        assert_eq!(blocks[0].line, 1);
        assert_eq!(blocks[0].body.len(), 1);
        assert_eq!(blocks[0].body[0].line, 5);
        assert_eq!(blocks[1].line, 6);
    }
}

#[test]
fn empty_trivia_body_reports_header_but_direct_bad_indent_reports_body_line() {
    for source in [
        "# prefix\nsketch:\n\n    # comment only",
        "# prefix\nsketch:\n\n    # comment only\n1 = 1",
    ] {
        let RuntimeError::ParseError(error) = crate::tokenize::Tokenizer::new()
            .tokenize(source, CodeSource::Eval)
            .unwrap_err()
        else {
            panic!("expected parse error");
        };
        assert_eq!(error.line, 2);
        assert_eq!(error.message, "block header requires a nonempty body");
    }
    for (source, message, line) in [
        ("sketch:", "block header missing body", 1),
        ("sketch:\n1 = 1", "expected indent", 2),
    ] {
        let RuntimeError::ParseError(error) = crate::tokenize::Tokenizer::new()
            .tokenize(source, CodeSource::Eval)
            .unwrap_err()
        else {
            panic!("expected parse error");
        };
        assert_eq!(error.line, line);
        assert_eq!(error.message, message);
    }
}
