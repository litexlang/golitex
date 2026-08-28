use crate::error::RuntimeError;
use crate::object::strip_free_param_numeric_tags_in_display;
use crate::output::json_value::{render_json_value, JsonValue};
use crate::output::{display_runtime_error_json, display_stmt_exec_result_json};
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

    if ok && !runtime.unverified_imports().is_empty() {
        output_text.push('\n');
        output_text.push_str(unverified_import_warning_json(runtime).as_str());
        output_text.push('\n');
    }

    let output_text = strip_free_param_numeric_tags_in_display(&output_text);

    (ok, output_text)
}

fn unverified_import_warning_json(runtime: &Runtime) -> String {
    let imports = runtime
        .unverified_imports()
        .iter()
        .map(|entry| {
            JsonValue::Object(vec![
                (
                    "kind".to_string(),
                    JsonValue::JsonString(entry.kind.clone()),
                ),
                (
                    "name".to_string(),
                    JsonValue::JsonString(entry.name.clone()),
                ),
                ("line".to_string(), JsonValue::Number(entry.line_file.0)),
                (
                    "file".to_string(),
                    JsonValue::JsonString(entry.line_file.1.to_string()),
                ),
            ])
        })
        .collect();
    render_json_value(
        &JsonValue::Object(vec![
            (
                "result".to_string(),
                JsonValue::JsonString("success".to_string()),
            ),
            (
                "type".to_string(),
                JsonValue::JsonString("unverified import warning".to_string()),
            ),
            (
                "message".to_string(),
                JsonValue::JsonString(
                    "configured imports, terminal imports, and -f prefix exports are trusted by default for faster runs; rerun with -strict to verify loaded dependencies"
                        .to_string(),
                ),
            ),
            ("unverified_imports".to_string(), JsonValue::Array(imports)),
        ]),
        0,
    )
}
