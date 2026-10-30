use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, ReadingInput};
use std::collections::BTreeSet;

#[test]
fn source_expression_hints_keep_original_ast_kind_and_byte_ranges() {
    let cases = [
        (
            "examples/test_objs/interval_open_open.lit",
            "obj:interval:open_open",
        ),
        (
            "examples/test_objs/interval_open_closed.lit",
            "obj:interval:open_closed",
        ),
        (
            "examples/test_objs/interval_closed_open.lit",
            "obj:interval:closed_open",
        ),
        (
            "examples/test_objs/interval_closed_closed.lit",
            "obj:interval:closed_closed",
        ),
        (
            "examples/test_objs/one_side_interval_lower_open.lit",
            "obj:ray:lower_open",
        ),
        (
            "examples/test_objs/one_side_interval_lower_closed.lit",
            "obj:ray:lower_closed",
        ),
        (
            "examples/test_objs/one_side_interval_upper_open.lit",
            "obj:ray:upper_open",
        ),
        (
            "examples/test_objs/one_side_interval_upper_closed.lit",
            "obj:ray:upper_closed",
        ),
        ("examples/wd/obj/list_set.lit", "obj:list_set"),
        ("examples/test_objs/set_builder.lit", "obj:set_builder"),
        ("examples/wd/obj/anonymous_fn.lit", "obj:anonymous_fn"),
        ("examples/test_objs/struct_obj.lit", "obj:struct_type"),
        ("examples/test_objs/field_access.lit", "obj:field"),
        (
            "examples/test_objs/instantiated_template_obj.lit",
            "obj:template",
        ),
        (
            "examples/reading/homepage/17-reciprocal-definition.lit",
            "obj:call",
        ),
    ];
    for (relative, expected) in cases {
        let source = std::fs::read_to_string(relative).unwrap();
        let result = build_reading(
            &ReadingInput::Source(source.clone()),
            true,
            OutputLanguage::English,
        );
        assert!(result.success, "{relative}");
        let mut keys = BTreeSet::new();
        let document = result.document.as_object().unwrap();
        for statement in document.get("statements").unwrap().as_array().unwrap() {
            let statement = statement.as_object().unwrap();
            let Some(hints) = statement.get("expression_hints") else {
                continue;
            };
            for hint in hints.as_array().unwrap() {
                let fields = hint.as_object().unwrap();
                let start = fields.get("start_byte").unwrap().as_u64().unwrap() as usize;
                let end = fields.get("end_byte").unwrap().as_u64().unwrap() as usize;
                let actual = fields.get("source_text").unwrap().as_str().unwrap();
                assert_eq!(source.get(start..end), Some(actual), "{relative}");
                keys.insert(
                    fields
                        .get("reference_key")
                        .unwrap()
                        .as_str()
                        .unwrap()
                        .to_owned(),
                );
            }
        }
        assert!(
            keys.contains(expected),
            "{relative}: missing {expected}; found {keys:?}"
        );
    }
}

#[test]
fn field_path_names_do_not_take_same_spelled_variable_occurrences() {
    let source = "struct Point:\n    x R\n    y R\nforall x R, p &Point:\n    p.x + x = p.x + x\n";
    let result = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let fields = result.document.as_object().unwrap();
    let symbols = fields.get("symbols").unwrap().as_array().unwrap();
    let mut positions = BTreeSet::new();
    for occurrence in fields.get("occurrences").unwrap().as_array().unwrap() {
        let occurrence = occurrence.as_object().unwrap();
        let id = occurrence.get("symbol_id").unwrap().as_str().unwrap();
        if symbols.iter().any(|symbol| {
            let symbol = symbol.as_object().unwrap();
            symbol.get("id").unwrap().as_str().unwrap() == id
                && symbol.get("name").unwrap().as_str().unwrap() == "x"
        }) {
            let start = occurrence.get("start_byte").unwrap().as_u64().unwrap() as usize;
            assert!(
                !source[..start].ends_with('.'),
                "field token received a variable identity"
            );
            positions.insert(start);
        }
    }
    assert!(positions.contains(&(source.find("+ x").unwrap() + 2)));
    assert!(positions.contains(&(source.rfind("+ x").unwrap() + 2)));
}

#[test]
fn repeated_expression_locations_require_matching_ast_multiplicity() {
    for (relative, expected, key, expression, count) in [
        (
            "examples/test_objs/list_set.lit",
            "{1} $in {{1}, {2}}",
            "obj:list_set",
            "{1}",
            2,
        ),
        (
            "examples/proof_nodes/equal/by_builtin_rule/fn_range_of_constant_anonymous_fn.lit",
            "fn_range(fn(x R) R {1}) = {1}",
            "obj:list_set",
            "{1}",
            0,
        ),
        (
            "examples/test_objs/field_access.lit",
            "p.point.x = p.point.x",
            "obj:field",
            "p.point.x",
            2,
        ),
        (
            "examples/test_objs/field_access.lit",
            "o.f(2) = o.f(2)",
            "obj:call",
            "o.f(2)",
            2,
        ),
    ] {
        let source = std::fs::read_to_string(relative).unwrap();
        let result = build_reading(
            &ReadingInput::Source(source.clone()),
            true,
            OutputLanguage::English,
        );
        assert!(result.success, "{relative}");
        let line = source
            .lines()
            .position(|value| value.trim() == expected)
            .unwrap()
            + 1;
        let start_of_line = source
            .lines()
            .take(line - 1)
            .map(|value| value.len() + 1)
            .sum::<usize>();
        let end_of_line = start_of_line + source.lines().nth(line - 1).unwrap().len();
        let statements = result
            .document
            .as_object()
            .unwrap()
            .get("statements")
            .unwrap()
            .as_array()
            .unwrap();
        let mut ranges = BTreeSet::new();
        for statement in statements {
            let Some(hints) = statement.as_object().unwrap().get("expression_hints") else {
                continue;
            };
            for hint in hints.as_array().unwrap() {
                let fields = hint.as_object().unwrap();
                let start = fields.get("start_byte").unwrap().as_u64().unwrap() as usize;
                let end = fields.get("end_byte").unwrap().as_u64().unwrap() as usize;
                let text = fields.get("source_text").unwrap().as_str().unwrap();
                assert_eq!(source.get(start..end), Some(text), "{relative}");
                if start >= start_of_line
                    && end <= end_of_line
                    && text == expression
                    && fields.get("reference_key").unwrap().as_str().unwrap() == key
                {
                    ranges.insert((start, end));
                }
            }
        }
        assert_eq!(ranges.len(), count, "{relative}: {expected}");
    }
}
