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

pub(crate) fn json_value_for_output(runtime: &Runtime, value: JsonValue) -> JsonValue {
    let value = match runtime.effective_output_style() {
        OutputStyle::Compact => compact_output_value(value),
        OutputStyle::Normal => normal_output_value(value),
        OutputStyle::Detailed => value,
    };
    let value = remove_empty_json_fields(value);
    crate::output::localize_json_value(runtime, value)
}

fn compact_output_value(value: JsonValue) -> JsonValue {
    let JsonValue::Object(fields) = value else {
        return value;
    };

    let is_error = fields.iter().any(|(key, value)| {
        key == "result" && matches!(value, JsonValue::JsonString(text) if text == "error")
    });
    JsonValue::Object(
        fields
            .into_iter()
            .filter(|(key, _)| {
                if is_error {
                    [
                        "result",
                        "error_type",
                        "line",
                        "type",
                        "statement",
                        "message",
                    ]
                    .contains(&key.as_str())
                } else {
                    ["result", "type", "line", "statement"].contains(&key.as_str())
                }
            })
            .collect::<Vec<_>>(),
    )
}

fn normal_output_value(value: JsonValue) -> JsonValue {
    match value {
        JsonValue::Object(fields) => normal_object_value(fields),
        JsonValue::Array(items) => JsonValue::Array(
            items
                .into_iter()
                .map(normal_output_value)
                .collect::<Vec<_>>(),
        ),
        other => other,
    }
}

fn normal_object_value(fields: Vec<(String, JsonValue)>) -> JsonValue {
    let mut output = Vec::new();
    for (key, value) in fields {
        match key.as_str() {
            "phases" | "effects" | "checks" | "proof_steps" | "subgoals" | "steps"
            | "assignments" | "instantiation" | "requirements" | "proof_step_index"
            | "proof_step_count" | "then_clause_index" | "then_clause_count" | "path" => {}
            "verification" => add_normal_verification_fields(&mut output, value),
            _ => push_normal_field(&mut output, key, normal_output_value(value)),
        }
    }
    JsonValue::Object(output)
}

fn add_normal_verification_fields(output: &mut Vec<(String, JsonValue)>, value: JsonValue) {
    let JsonValue::Object(fields) = value else {
        push_normal_field(
            output,
            "why_verified".to_string(),
            normal_output_value(value),
        );
        return;
    };

    let mut why_verified = Vec::new();
    for (key, value) in fields {
        match key.as_str() {
            "parameters" | "assumptions" | "conclusions" => {
                push_normal_field(output, key, normal_output_value(value));
            }
            "type"
            | "rule"
            | "cite_source"
            | "cited_statement"
            | "prove_goal"
            | "theorems"
            | "parameter_sets"
            | "verify_what"
            | "prop"
            | "arguments"
            | "parameter_type_check"
            | "definition_clause_checks"
            | "stored_fact" => {
                why_verified.push((key, normal_output_value(value)));
            }
            _ => {}
        }
    }
    if !why_verified.is_empty() {
        push_normal_field(
            output,
            "why_verified".to_string(),
            JsonValue::Object(why_verified),
        );
    }
}

fn push_normal_field(output: &mut Vec<(String, JsonValue)>, key: String, value: JsonValue) {
    if let Some((_, existing)) = output
        .iter_mut()
        .find(|(existing_key, _)| *existing_key == key)
    {
        *existing = value;
    } else {
        output.push((key, value));
    }
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
