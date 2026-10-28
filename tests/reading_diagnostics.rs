//! Source-local diagnostics reuse actual failure projections, without parsing logs.
use litex::knowledge_base::JsonValue;
use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, ReadingInput};

fn field<'a>(value: &'a JsonValue, key: &str) -> &'a JsonValue {
    value
        .as_object()
        .unwrap()
        .get(key)
        .unwrap_or_else(|| panic!("missing {key}: {}", value.stringify()))
}

#[test]
fn parser_diagnostics_keep_unicode_scalar_location_and_original_source() {
    let source = include_str!("../examples/reading/homepage/problems/undefined-name.lit");
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        let result = build_reading(&ReadingInput::Source(source.into()), true, language);
        assert!(!result.success);
        let diagnostic = field(&result.document, "diagnostics")
            .as_array()
            .unwrap()
            .iter()
            .find(|item| field(item, "kind").as_str() == Ok("source"))
            .unwrap();
        assert_eq!(field(diagnostic, "phase").as_str(), Ok("parse"));
        assert_eq!(field(diagnostic, "line").as_u64(), Ok(3));
        let line = source.lines().nth(2).unwrap();
        assert_eq!(field(diagnostic, "line_text").as_str(), Ok(line));
        let column = field(diagnostic, "column").as_u64().unwrap() as usize;
        assert!(column > 0 && column <= line.chars().count() + 1);
        assert!(!field(diagnostic, "summary").as_str().unwrap().is_empty());
        assert_eq!(field(diagnostic, "source_id").as_str(), Ok("source0"));
    }
}

#[test]
fn failed_statements_keep_fixed_diagnostic_keys_and_real_obligations() {
    for source in [
        include_str!("../examples/reading/homepage/problems/zero-divisor.lit"),
        include_str!("../examples/reading/homepage/problems/sqrt-domain.lit"),
        include_str!("../examples/reading/homepage/problems/missing-premise.lit"),
    ] {
        for language in [OutputLanguage::English, OutputLanguage::Chinese] {
            let result = build_reading(&ReadingInput::Source(source.into()), true, language);
            assert!(!result.success);
            let rejected = field(&result.document, "statements")
                .as_array()
                .unwrap()
                .iter()
                .find(|item| field(item, "status").as_str() == Ok("rejected"))
                .unwrap();
            let failure = field(rejected, "failure");
            let fields = failure.as_object().unwrap();
            assert!(
                fields.get("phase").is_some() || fields.get("category").is_some(),
                "missing machine diagnostic category: {}",
                failure.stringify()
            );
            assert!(
                fields.get("obligation").is_some() || fields.get("goal").is_some(),
                "missing actual failed obligation: {}",
                failure.stringify()
            );
            assert!(field(rejected, "produced_fact_ids")
                .as_array()
                .unwrap()
                .is_empty());
        }
    }
}

#[test]
fn accepted_statements_do_not_receive_failure_records() {
    let result = build_reading(
        &ReadingInput::Source("1 = 1".into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    for statement in field(&result.document, "statements").as_array().unwrap() {
        assert!(statement.as_object().unwrap().get("failure").is_none());
    }
}
