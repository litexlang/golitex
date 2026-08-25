use crate::parse::Tokenizer;
use crate::prelude::*;
use std::rc::Rc;

fn parse_one_stmt_error_message(source_code: &str) -> String {
    let mut runtime = Runtime::new();
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(source_code, Rc::from("parse_stmt_diagnostic_test.lit"))
        .expect("tokenize statement");
    assert_eq!(blocks.len(), 1, "{source_code:?}");
    let err = runtime.parse_statement(&mut blocks[0]).unwrap_err();
    let RuntimeError::ParseError(parse_error) = err else {
        panic!("expected parse error, got {err:?}");
    };
    parse_error.msg
}

fn parse_one_stmt(source_code: &str) -> Result<Stmt, RuntimeError> {
    let mut runtime = Runtime::new();
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(source_code, Rc::from("parse_stmt_diagnostic_test.lit"))
        .expect("tokenize statement");
    assert_eq!(blocks.len(), 1, "{source_code:?}");
    runtime.parse_statement(&mut blocks[0])
}

#[test]
fn incomplete_have_dispatch_reports_syntax_errors() {
    let cases = [
        (
            "have",
            "have: expected object definition, `fn`, or `by preimage`",
        ),
        ("have by", "have by: expected `preimage`"),
    ];

    for (source_code, expected_message) in cases {
        let message = parse_one_stmt_error_message(source_code);
        assert_eq!(message, expected_message);
        assert!(
            !message.contains("Expected token: at index"),
            "{source_code:?} leaked a token-index error: {message}",
        );
    }
}

#[test]
fn trust_forms_and_import_boundaries_parse_as_expected() {
    for source_code in [
        "trust 1 = 1",
        "trust:\n    1 = 1",
        "trust have x R:\n    x = 1",
    ] {
        assert!(parse_one_stmt(source_code).is_ok(), "{source_code:?}");
    }
    let message = parse_one_stmt_error_message("import std basics");
    assert!(
        message.contains("only available in an isolated REPL"),
        "{message}"
    );

    let mut runtime = Runtime::new();
    runtime.start_isolated_source("isolated_import_test.lit");
    runtime.set_current_source_allows_inline_imports(true);
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(
            "import \"../algebra\" as Algebra\nimport std basics",
            Rc::from("isolated_import_test.lit"),
        )
        .expect("tokenize imports");
    assert!(runtime.parse_statement(&mut blocks[0]).is_ok());
    assert!(runtime.parse_statement(&mut blocks[1]).is_ok());
}

#[test]
fn by_def_requires_exactly_one_positive_question_goal() {
    let message = parse_one_stmt_error_message("by def $P(1):\n    1 = 1");
    assert!(
        message.contains("inline by def does not accept an indented body"),
        "{}",
        message
    );

    let tokenizer = Tokenizer::new();
    let error = tokenizer
        .parse_blocks(
            "by def $P(1)\n    1 = 1",
            Rc::from("parse_stmt_diagnostic_test.lit"),
        )
        .expect_err("an indented body without `:` should fail tokenization");
    let RuntimeError::ParseError(error) = error else {
        panic!("expected parse error");
    };
    assert!(error.msg.contains("unexpected indent"), "{}", error.msg);

    let message = parse_one_stmt_error_message("by def:\n    ? not $P(1)");
    assert!(
        message.contains("expects one positive atomic fact"),
        "{message}"
    );
    let message = parse_one_stmt_error_message("by def:\n    ? 1 = 1\n    1 = 1");
    assert!(message.contains("exactly one"), "{message}");
    assert!(parse_one_stmt("by def:\n    ? $in(1, R)").is_ok());
    assert!(parse_one_stmt("by def:\n    ? 1 = 1").is_ok());
}

#[test]
fn claim_requires_an_indented_question_goal() {
    for source_code in [
        "claim 1 = 1:\n    1 = 1",
        "claim forall x R => x = x:\n    x = x",
    ] {
        let message = parse_one_stmt_error_message(source_code);
        assert!(
            message.contains("claim requires `claim:`"),
            "{source_code:?}: {message}"
        );
    }
    assert!(parse_one_stmt("claim:\n    ? 1 = 1").is_ok());
}

#[test]
fn function_implementation_syntax_requires_for_after_have_algo() {
    assert_eq!(
        parse_one_stmt_error_message("have algo f(x):\n    x"),
        "have algo: expected `for f(...)`"
    );
}
