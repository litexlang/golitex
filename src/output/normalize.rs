use crate::common::json_value::JsonValue;
use crate::prelude::*;

/// Apply [`strip_free_param_numeric_tags_in_display`] once on a finished JSON blob (CLI/REPL/file run).
/// Nested JSON is built with `strip_free_param_tags == false` so a single final strip covers the whole tree.
pub(crate) fn finalize_display_text_with_optional_strip(
    text: String,
    strip_free_param_tags: bool,
) -> String {
    if strip_free_param_tags {
        strip_free_param_numeric_tags_in_display(&text)
    } else {
        text
    }
}

pub(crate) fn json_value_for_output(_runtime: &Runtime, value: JsonValue) -> JsonValue {
    let value = remove_empty_json_fields(value);
    crate::output::localize_json_value(_runtime, value)
}

pub(crate) fn remove_empty_json_fields(value: JsonValue) -> JsonValue {
    match value {
        JsonValue::Object(fields) => {
            let mut next_fields: Vec<(String, JsonValue)> = Vec::new();
            for (key, field_value) in fields {
                let field_value = remove_empty_json_fields(field_value);
                if !json_value_is_empty_in_normal_output(&field_value) {
                    next_fields.push((key, field_value));
                }
            }
            JsonValue::Object(next_fields)
        }
        JsonValue::Array(items) => JsonValue::Array(
            items
                .into_iter()
                .map(remove_empty_json_fields)
                .collect::<Vec<_>>(),
        ),
        _ => value,
    }
}

pub(crate) fn json_value_is_empty_in_normal_output(value: &JsonValue) -> bool {
    match value {
        JsonValue::Null => true,
        JsonValue::JsonString(s) => s.is_empty(),
        JsonValue::Array(items) => items.is_empty(),
        JsonValue::Object(fields) => fields.is_empty(),
        _ => false,
    }
}
