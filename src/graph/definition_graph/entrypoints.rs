//! Definition graph runtime and file-target entrypoints.

use super::*;

/// Render the definition inventory retained by the active environment.
///
/// Unlike the relation graph, this projection starts from environment tables,
/// so named definitions and reusable interfaces appear as the definitions later code can
/// actually resolve.
pub fn render_definition_graph_from_stmt_results(
    target_kind: RunTargetKind,
    target_label: &str,
    hide_file_paths: bool,
    runtime: &mut Runtime,
    _stmt_results: &[StmtResult],
    runtime_error: Option<&RuntimeError>,
) -> (bool, String) {
    render_definition_graph_result(
        target_kind,
        target_label,
        hide_file_paths,
        runtime,
        _stmt_results,
        runtime_error,
        None,
    )
}

pub fn render_definition_graph_result(
    target_kind: RunTargetKind,
    target_label: &str,
    hide_file_paths: bool,
    runtime: &mut Runtime,
    stmt_results: &[StmtResult],
    runtime_error: Option<&RuntimeError>,
    selected_target: Option<RepositoryFileTarget>,
) -> (bool, String) {
    let ok = runtime_error.is_none();
    let error = runtime_error.map(|error| display_runtime_error_json(runtime, error, true));
    let graph = DefinitionGraphBuilder::from_runtime(runtime, selected_target, stmt_results);
    let mut fields = vec![
        (
            "graph".to_string(),
            JsonValue::JsonString(DEFINITION_GRAPH_NAME.to_string()),
        ),
        (
            "graph_version".to_string(),
            JsonValue::JsonString(DEFINITION_GRAPH_VERSION.to_string()),
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
            definition_graph_target_json_value(target_kind, target_label, hide_file_paths),
        ),
        (
            "error".to_string(),
            error.map(JsonValue::JsonString).unwrap_or(JsonValue::Null),
        ),
        ("summary".to_string(), graph.summary_json()),
        ("nodes".to_string(), graph.nodes_json(!hide_file_paths)),
        ("edges".to_string(), graph.edges_json()),
        ("is_dag".to_string(), JsonValue::Bool(graph.is_dag())),
        (
            "topological_order".to_string(),
            JsonValue::Array(
                graph
                    .topological_order()
                    .into_iter()
                    .map(JsonValue::JsonString)
                    .collect(),
            ),
        ),
        (
            "cycle_nodes".to_string(),
            JsonValue::Array(
                graph
                    .cycle_nodes()
                    .into_iter()
                    .map(JsonValue::JsonString)
                    .collect(),
            ),
        ),
        (
            "mermaid".to_string(),
            JsonValue::JsonString(graph.mermaid()),
        ),
    ];
    fields.sort_by(|left, right| left.0.cmp(&right.0));
    (ok, render_json_value(&JsonValue::Object(fields), 0))
}

pub fn definition_graph_target_error_output(
    target_kind: RunTargetKind,
    target_label: &str,
    hide_file_paths: bool,
    message: String,
) -> (bool, String) {
    let output = JsonValue::Object(vec![
        (
            "graph".to_string(),
            JsonValue::JsonString(DEFINITION_GRAPH_NAME.to_string()),
        ),
        (
            "graph_version".to_string(),
            JsonValue::JsonString(DEFINITION_GRAPH_VERSION.to_string()),
        ),
        (
            "result".to_string(),
            JsonValue::JsonString("error".to_string()),
        ),
        ("ok".to_string(), JsonValue::Bool(false)),
        ("partial".to_string(), JsonValue::Bool(false)),
        (
            "target".to_string(),
            definition_graph_target_json_value(target_kind, target_label, hide_file_paths),
        ),
        ("error".to_string(), JsonValue::JsonString(message)),
        (
            "summary".to_string(),
            DefinitionGraphBuilder::empty_summary_json(),
        ),
        ("nodes".to_string(), JsonValue::Array(vec![])),
        ("edges".to_string(), JsonValue::Array(vec![])),
        ("is_dag".to_string(), JsonValue::Bool(true)),
        ("topological_order".to_string(), JsonValue::Array(vec![])),
        ("cycle_nodes".to_string(), JsonValue::Array(vec![])),
        (
            "mermaid".to_string(),
            JsonValue::JsonString("flowchart LR".to_string()),
        ),
    ]);
    (false, render_json_value(&output, 0))
}

fn definition_graph_target_json_value(
    target_kind: RunTargetKind,
    target_label: &str,
    hide_file_paths: bool,
) -> JsonValue {
    let label = if hide_file_paths && target_kind != RunTargetKind::Code {
        "entry".to_string()
    } else {
        target_label.to_string()
    };
    JsonValue::Object(vec![
        (
            "kind".to_string(),
            JsonValue::JsonString(target_kind.json_name().to_string()),
        ),
        ("label".to_string(), JsonValue::JsonString(label)),
    ])
}

pub fn definition_graph_file_target(
    runtime: &Runtime,
    resolved_path: &str,
) -> Option<RepositoryFileTarget> {
    let canonical_path = fs::canonicalize(resolved_path)
        .ok()
        .and_then(|path| path.to_str().map(str::to_string));
    let mut targets = vec![];
    for module in runtime.module_manager.modules.values() {
        for file in module.files.iter() {
            if file.source_path == resolved_path
                || canonical_path.as_deref() == Some(file.source_path.as_str())
            {
                targets.push(RepositoryFileTarget::File {
                    module_id: module.id,
                    file_id: file.id,
                });
            }
        }
    }
    if targets.len() == 1 {
        Some(targets[0])
    } else {
        None
    }
}
