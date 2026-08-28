use crate::output::json_value::JsonValue;
use crate::prelude::strip_free_param_numeric_tags_in_display;

pub fn finalize_display_text_with_optional_strip(
    text: String,
    strip_free_param_tags: bool,
) -> String {
    if strip_free_param_tags {
        strip_free_param_numeric_tags_in_display(&text)
    } else {
        text
    }
}

pub fn remove_empty_json_fields(value: JsonValue) -> JsonValue {
    match value {
        JsonValue::Object(fields) => {
            let mut next_fields = Vec::new();
            for (key, field_value) in fields {
                let field_value = remove_empty_json_fields(field_value);
                if !json_value_is_empty_in_normal_output(&field_value) {
                    next_fields.push((key, field_value));
                }
            }
            JsonValue::Object(next_fields)
        }
        JsonValue::Array(items) => {
            JsonValue::Array(items.into_iter().map(remove_empty_json_fields).collect())
        }
        other => other,
    }
}

pub fn json_value_is_empty_in_normal_output(value: &JsonValue) -> bool {
    match value {
        JsonValue::Null => true,
        JsonValue::JsonString(value) => value.is_empty(),
        JsonValue::Array(items) => items.is_empty(),
        JsonValue::Object(fields) => fields.is_empty(),
        JsonValue::Bool(_) | JsonValue::Number(_) => false,
    }
}
