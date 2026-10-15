use crate::prelude::*;

#[test]
fn missing_delimiter_reports_expected_token_source_and_insertion_column() {
    let error = parse_error("have a R = (1 + 2");
    assert_eq!(error.diagnostic(), "Parse error: expected `)`, reached end of line\n --> example.lit:1:18\n  |\n1 | have a R = (1 + 2\n  |                  ^ missing `)`");
    assert_eq!(
        parse_error("have a R = {1, 2").message,
        "expected `}`, reached end of line"
    );
}

#[test]
fn wrong_delimiter_points_at_actual_token_and_missing_expression_at_end() {
    let error = parse_error("have a R = (1 + 2]");
    assert_eq!(error.message, "expected `)`, got `]`");
    assert_eq!(error.source.as_ref().unwrap().column, Some(18));
    assert!(error.diagnostic().ends_with("  |                  ^"));
    let error = parse_error("have a R =");
    assert_eq!(error.message, "expected object");
    assert_eq!(error.source.unwrap().column, Some(11));
}

#[test]
fn nested_errors_keep_the_physical_source_line_and_indentation() {
    let error = parse_error("claim:\n    ? 1 = 1\n    have a R = (1 + 2");
    assert_eq!(error.line, 3);
    assert_eq!(error.source.as_ref().unwrap().column, Some(22));
    assert!(error
        .diagnostic()
        .contains("3 |     have a R = (1 + 2\n  |                      ^ missing `)`"));
}

#[test]
fn comments_and_inline_asides_preserve_original_positions() {
    let code = "\"\"\"\nignored\n\"\"\"\nhave a R = (1 \"note\" + 2] # ignored";
    let error = parse_error(code);
    assert_eq!(error.line, 4);
    assert_eq!(error.source.as_ref().unwrap().column, Some(25));
    assert_eq!(
        error.source.unwrap().text,
        "have a R = (1 \"note\" + 2] # ignored"
    );
    let error = parse_error("have a R = (1 + 2  # missing close, not part of code");
    assert_eq!(error.source.unwrap().column, Some(18));
}

#[test]
fn continuations_and_crlf_point_to_the_original_physical_line() {
    for ending in ["\n", "\r\n"] {
        let code = format!("have a R = (1 + \\\\ # continuation{ending}    2]");
        let error = parse_error(&code);
        assert_eq!(error.line, 2);
        assert_eq!(error.source.as_ref().unwrap().column, Some(6));
        assert_eq!(error.source.unwrap().text, "    2]");
        let code = format!("have a R = (1 + \\\\{ending}    2");
        let error = parse_error(&code);
        assert_eq!(error.line, 2);
        assert_eq!(error.source.unwrap().column, Some(6));
    }
}

#[test]
fn unicode_aliases_and_asides_use_character_columns_not_utf8_bytes() {
    let error = parse_error("have a ℝ = (1 + 2]");
    assert_eq!(error.message, "expected `)`, got `]`");
    assert_eq!(error.source.as_ref().unwrap().column, Some(18));
    assert_eq!(error.source.unwrap().text, "have a ℝ = (1 + 2]");
    let error = parse_error("have a R = (1 \"中文\" + 2]");
    assert_eq!(error.source.unwrap().column, Some(23));
}

#[test]
fn tokenizer_errors_and_legacy_line_errors_capture_source_without_inventing_columns() {
    let error = parse_error("have a R = 1 \"unclosed");
    assert_eq!(error.source.as_ref().unwrap().column, Some(14));
    assert!(error.diagnostic().contains("1 | have a R = 1 \"unclosed"));
    let error = parse_error("have");
    assert_eq!(error.source.as_ref().unwrap().column, None);
    assert!(error.diagnostic().ends_with("1 | have"));
}

#[test]
fn sliced_headers_and_alias_expansion_preserve_original_token_ranges() {
    let blocks = super::Tokenizer::new()
        .tokenize("1 ∈ ℝ", CodeSource::Eval)
        .unwrap();
    let block = &blocks[0];
    assert_eq!(block.header, vec!["1", "$", "in", "R"]);
    let raw: Vec<&str> = block
        .token_spans
        .iter()
        .map(|span| &"1 ∈ ℝ"[span.clone()])
        .collect();
    assert_eq!(raw, vec!["1", "∈", "∈", "ℝ"]);
    let mut part = block.header_slice(1..3);
    part.parse_index = 1;
    let error = part.error_at_cursor("test location");
    assert_eq!(error.source.unwrap().column, Some(3));
    let blocks = super::Tokenizer::new()
        .tokenize("ab\"aside\"cd = 1", CodeSource::Eval)
        .unwrap();
    assert_eq!(blocks[0].header[0], "abcd");
    assert_eq!(
        &"ab\"aside\"cd = 1"[blocks[0].token_spans[0].clone()],
        "ab\"aside\"cd"
    );
}

#[test]
fn run_examples_parse_error_diagnostics_corrected_tracer() {
    let mut runtime = runtime();
    let result = runtime
        .run_litex_code(include_str!(
            "../../../examples/tokenize/parse_error_diagnostics.lit"
        ))
        .unwrap();
    assert!(result.success, "{:?}", result.session_error);
}

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn parse_error(code: &str) -> crate::runtime::RuntimeParseError {
    let mut runtime = runtime();
    let error = match super::Tokenizer::new().tokenize(code, CodeSource::Real("example.lit".into()))
    {
        Ok(blocks) => runtime.parse(&blocks).unwrap_err(),
        Err(error) => error,
    };
    match error {
        RuntimeError::ParseError(error) => error,
        other => panic!("expected parse error: {other}"),
    }
}
