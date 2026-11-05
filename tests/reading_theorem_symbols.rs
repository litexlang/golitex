//! A theorem declaration identity does not assert that its call succeeded.
use litex::knowledge_base::JsonValue;
use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, ReadingInput};

fn field<'a>(value: &'a JsonValue, key: &str) -> &'a JsonValue {
    value.as_object().unwrap().get(key).unwrap()
}

fn check_identity(document: &JsonValue, name: &str, arity: u64) {
    let symbol = field(document, "symbols")
        .as_array()
        .unwrap()
        .iter()
        .find(|symbol| field(symbol, "name").as_str().unwrap() == name)
        .unwrap();
    assert_eq!(field(symbol, "kind").as_str().unwrap(), "builtin_theorem");
    let declaration = field(symbol, "builtin_theorem");
    assert_eq!(
        field(declaration, "type").as_str().unwrap(),
        "BuiltinTheoremId"
    );
    assert_eq!(field(declaration, "name").as_str().unwrap(), name);
    assert_eq!(field(declaration, "arity").as_u64().unwrap(), arity);
    let id = field(symbol, "id").as_str().unwrap();
    assert!(field(document, "occurrences")
        .as_array()
        .unwrap()
        .iter()
        .any(|mention| field(mention, "symbol_id").as_str().unwrap() == id));
}

#[test]
fn rejected_theorem_calls_keep_native_declaration_without_success_evidence() {
    for (source, name, arity) in [
        ("release thm prime_divisor(1)", "prime_divisor", 1),
        ("by thm prime_divisor(1) => 1 = 1", "prime_divisor", 1),
        (
            "release thm finite_set_has_bijective_index()",
            "finite_set_has_bijective_index",
            1,
        ),
        (
            "release thm finite_set_reduce_singleton(1, 1)",
            "finite_set_reduce_singleton",
            2,
        ),
    ] {
        let result = build_reading(
            &ReadingInput::Source(source.into()),
            true,
            OutputLanguage::English,
        );
        assert!(!result.success, "{source}");
        check_identity(&result.document, name, arity);
        let nodes = field(&result.document, "evidence_nodes")
            .as_array()
            .unwrap();
        let statements = field(&result.document, "statements").as_array().unwrap();
        let statement = statements
            .iter()
            .find(|statement| field(statement, "status").as_str().unwrap() == "rejected")
            .unwrap();
        assert!(field(statement, "produced_fact_ids")
            .as_array()
            .unwrap()
            .is_empty());
        let mut reference = field(statement, "evidence");
        let mut found_failed_call = false;
        loop {
            let id = field(reference, "evidence_id").as_str().unwrap();
            let entry = nodes
                .iter()
                .find(|entry| field(entry, "id").as_str().unwrap() == id)
                .unwrap();
            let node = field(entry, "node");
            let kind = field(node, "type").as_str().unwrap();
            // The callee's retained declaration can contain successful generic
            // applications. Check the caller's result chain, not that separate
            // declaration's proof graph.
            assert!(
                ![
                    "ExecReleaseThmStmtSuccess",
                    "ExecByThmStmtSuccess",
                    "BuiltinThmApplication"
                ]
                .contains(&kind),
                "{source}"
            );
            if ["ExecReleaseThmStmtResult", "ExecByThmStmtResult"].contains(&kind) {
                assert_eq!(field(node, "variant").as_str().unwrap(), "Failed");
                found_failed_call = true;
            }
            let Some(next) = field(node, "fields").as_object().unwrap().get("0") else {
                break;
            };
            assert_eq!(field(next, "kind").as_str().unwrap(), "evidence_reference");
            reference = next;
        }
        assert!(found_failed_call, "{source}");
    }
}

#[test]
fn accepted_release_and_selected_calls_keep_the_same_native_identity() {
    let release = std::fs::read_to_string(
        "examples/stmt_nodes/release_and_expand/builtin_thm/prime_divides_power.lit",
    )
    .unwrap();
    let selected = release.replace(
        "release thm prime_divides_power(6, 2, 2)",
        "by thm prime_divides_power(6, 2, 2) => $dvd(6, 2)",
    );
    assert_ne!(release, selected);
    for source in [release, selected] {
        let result = build_reading(&ReadingInput::Source(source), true, OutputLanguage::English);
        assert!(result.success);
        check_identity(&result.document, "prime_divides_power", 3);
    }
}

#[test]
fn user_unknown_and_qualified_names_gain_no_native_declaration() {
    let user = std::fs::read_to_string("examples/stmt_nodes/by/by_thm.lit").unwrap();
    for (source, success) in [
        (user, true),
        ("release thm no_such_theorem(1)".into(), false),
        ("release thm missing::prime_divisor(1)".into(), false),
    ] {
        let result = build_reading(&ReadingInput::Source(source), true, OutputLanguage::English);
        assert_eq!(result.success, success);
        assert!(field(&result.document, "symbols")
            .as_array()
            .unwrap()
            .iter()
            .all(|symbol| symbol.as_object().unwrap().get("builtin_theorem").is_none()));
    }
}
