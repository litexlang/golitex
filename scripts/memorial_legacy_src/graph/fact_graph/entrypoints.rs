//! Fact graph rendering and target-error entrypoints.

use super::*;

/// Render only the proof-facing dependency graph from already executed statements.
///
/// The graph omits `prop`, function, and object-definition nodes. Its edges are
/// taken from the verifier's actual citation and `forall`-requirement evidence.
pub fn render_fact_graph_from_stmt_results(
    target_kind: RunTargetKind,
    target_path: Option<&str>,
    hide_file_paths: bool,
    runtime: &Runtime,
    stmt_results: &[StmtResult],
    runtime_error: Option<&RuntimeError>,
) -> (bool, String) {
    let ok = runtime_error.is_none();
    let graph = FactGraphBuilder::from_stmt_results(stmt_results);
    let mut fields = vec![
        (
            "graph".to_string(),
            JsonValue::JsonString(FACT_GRAPH_NAME.to_string()),
        ),
        (
            "graph_version".to_string(),
            JsonValue::JsonString(FACT_GRAPH_VERSION.to_string()),
        ),
        (
            "result".to_string(),
            JsonValue::JsonString(if ok { "success" } else { "error" }.to_string()),
        ),
        ("ok".to_string(), JsonValue::Bool(ok)),
        (
            "partial".to_string(),
            JsonValue::Bool(runtime_error.is_some()),
        ),
        (
            "target".to_string(),
            run_target_json_value(target_kind.json_name(), target_path, hide_file_paths),
        ),
    ];
    if let Some(error) = runtime_error {
        fields.push((
            "error".to_string(),
            JsonValue::JsonString(render_runtime_error_json(runtime, error, true)),
        ));
    } else {
        fields.push(("error".to_string(), JsonValue::Null));
    }
    fields.push(("summary".to_string(), graph.summary_json()));
    fields.push(("nodes".to_string(), graph.nodes_json(!hide_file_paths)));
    fields.push(("edges".to_string(), graph.edges_json()));
    fields.push(("longest_chain".to_string(), graph.longest_chain_json()));
    fields.push((
        "mermaid".to_string(),
        JsonValue::JsonString(graph.mermaid()),
    ));

    (ok, render_json_value(&JsonValue::Object(fields), 0))
}

pub fn fact_graph_target_error_output(
    target_kind: RunTargetKind,
    target_path: Option<&str>,
    hide_file_paths: bool,
    message: String,
) -> (bool, String) {
    let output = JsonValue::Object(vec![
        (
            "graph".to_string(),
            JsonValue::JsonString(FACT_GRAPH_NAME.to_string()),
        ),
        (
            "graph_version".to_string(),
            JsonValue::JsonString(FACT_GRAPH_VERSION.to_string()),
        ),
        (
            "result".to_string(),
            JsonValue::JsonString("error".to_string()),
        ),
        ("ok".to_string(), JsonValue::Bool(false)),
        ("partial".to_string(), JsonValue::Bool(false)),
        (
            "target".to_string(),
            run_target_json_value(target_kind.json_name(), target_path, hide_file_paths),
        ),
        ("error".to_string(), JsonValue::JsonString(message)),
        (
            "summary".to_string(),
            FactGraphBuilder::empty_summary_json(),
        ),
        ("nodes".to_string(), JsonValue::Array(vec![])),
        ("edges".to_string(), JsonValue::Array(vec![])),
        (
            "longest_chain".to_string(),
            FactGraphBuilder::empty_longest_chain_json(),
        ),
        (
            "mermaid".to_string(),
            JsonValue::JsonString("flowchart LR".to_string()),
        ),
    ]);
    (false, render_json_value(&output, 0))
}
