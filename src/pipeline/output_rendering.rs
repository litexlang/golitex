use crate::error::RuntimeError;
use crate::object::strip_free_param_numeric_tags_in_display;
use crate::output::json_value::{render_json_value_compact, JsonValue};
use crate::output::{
    display_runtime_error_json, display_stmt_exec_result_json, display_stmt_result_json_v2,
};
use crate::result::StmtResult;
use crate::runtime::Runtime;

/// Render finished user output. Internal symbol identities are always removed;
/// callers cannot opt into leaking runtime-local IDs.
pub fn render_run_output(
    runtime: &Runtime,
    stmt_results: &[StmtResult],
    runtime_error: &Option<RuntimeError>,
) -> (bool, String) {
    let mut output_text = String::new();
    for stmt_result in stmt_results.iter() {
        output_text.push('\n');
        output_text.push_str(display_stmt_exec_result_json(runtime, stmt_result, false).as_str());
        output_text.push('\n');
    }

    let ok = runtime_error.is_none();
    if let Some(error) = runtime_error {
        output_text.push('\n');
        output_text.push_str(display_runtime_error_json(runtime, error, false).as_str());
        output_text.push('\n');
    }

    let output_text = strip_free_param_numeric_tags_in_display(&output_text);

    (ok, output_text)
}

pub fn render_stream_output(
    stream: &str,
    event: &str,
    ok: bool,
    id: Option<&str>,
    statement_results: &[StmtResult],
    content: JsonValue,
    error: JsonValue,
) -> String {
    let statement_results = statement_results
        .iter()
        .map(|result| JsonValue::RawJson(display_stmt_result_json_v2(result)))
        .collect::<Vec<_>>();
    render_json_value_compact(&JsonValue::Object(vec![
        (
            "kind".to_string(),
            JsonValue::JsonString("stream".to_string()),
        ),
        ("ok".to_string(), JsonValue::Bool(ok)),
        (
            "stream".to_string(),
            JsonValue::JsonString(stream.to_string()),
        ),
        (
            "event".to_string(),
            JsonValue::JsonString(event.to_string()),
        ),
        (
            "id".to_string(),
            id.map(|id| JsonValue::JsonString(id.to_string()))
                .unwrap_or(JsonValue::Null),
        ),
        (
            "statement_results".to_string(),
            JsonValue::Array(statement_results),
        ),
        ("content".to_string(), content),
        ("error".to_string(), error),
    ]))
}
