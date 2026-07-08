use crate::common::json_value::json_string_literal;
use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;

const MAIN_DOT_LIT: &str = "main.lit";
const SCHEMA_VERSION: &str = "litex_concept_graph.v1";

#[derive(Clone, Copy)]
enum GraphOutputFormat {
    Json,
    Dot,
}

#[derive(Clone)]
struct GraphTarget {
    kind: String,
    label: String,
}

#[derive(Clone)]
struct GraphSource {
    line: usize,
    source_kind: String,
    source: String,
}

#[derive(Clone)]
struct ConceptNode {
    id: String,
    kind: String,
    label: String,
    source: GraphSource,
    formal_name: Option<String>,
    text: Option<String>,
    status: Option<String>,
    aliases: Vec<String>,
}

#[derive(Clone)]
struct ConceptEdge {
    from: String,
    to: String,
    kind: String,
    source: GraphSource,
    provenance: String,
    detail: Option<String>,
}

struct ConceptGraph {
    result: String,
    target: GraphTarget,
    nodes: Vec<ConceptNode>,
    edges: Vec<ConceptEdge>,
    error: Option<ConceptGraphError>,
}

struct ConceptGraphError {
    error_type: String,
    message: String,
    source: GraphSource,
}

#[derive(Clone)]
struct SourceItem {
    kind: String,
    number: String,
    label: String,
    text: String,
    line: usize,
}

#[derive(Clone)]
enum KgComment {
    Node {
        id: String,
        kind: String,
        label: Option<String>,
        status: Option<String>,
        aliases: Vec<String>,
    },
    Bind {
        from: String,
        to: String,
    },
    Edge {
        kind: String,
        from: String,
        to: String,
        detail: Option<String>,
    },
}

struct ConceptGraphBuilder {
    target: GraphTarget,
    source_kind: String,
    source_label: String,
    nodes: Vec<ConceptNode>,
    edges: Vec<ConceptEdge>,
    node_ids: HashSet<String>,
    edge_keys: HashSet<String>,
    formal_nodes_by_name: HashMap<String, String>,
    chapter_id: Option<String>,
    current_source_item_id: Option<String>,
    current_formal_id: Option<String>,
}

pub fn concept_graph_json_for_source(
    target_kind: &str,
    target_label: &str,
    source_code: &str,
    runtime_error: &Option<RuntimeError>,
) -> String {
    let graph = ConceptGraphBuilder::build(target_kind, target_label, source_code, runtime_error);
    render_json_value(&graph_to_json(&graph), 0)
}

pub fn concept_graph_dot_for_source(
    target_kind: &str,
    target_label: &str,
    source_code: &str,
    runtime_error: &Option<RuntimeError>,
) -> String {
    let graph = ConceptGraphBuilder::build(target_kind, target_label, source_code, runtime_error);
    graph_to_dot(&graph)
}

pub fn run_concept_graph_json_for_code(
    code: &str,
    label: &str,
    detail_output: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_concept_graph_on_source(
        "code",
        label,
        remove_windows_carriage_return(code).as_str(),
        detail_output,
        strict_mode,
        GraphOutputFormat::Json,
    )
}

pub fn run_concept_graph_dot_for_code(
    code: &str,
    label: &str,
    detail_output: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_concept_graph_on_source(
        "code",
        label,
        remove_windows_carriage_return(code).as_str(),
        detail_output,
        strict_mode,
        GraphOutputFormat::Dot,
    )
}

pub fn run_concept_graph_json_for_file(
    file_path: &str,
    detail_output: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_concept_graph_for_file(
        file_path,
        detail_output,
        strict_mode,
        GraphOutputFormat::Json,
    )
}

pub fn run_concept_graph_dot_for_file(
    file_path: &str,
    detail_output: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_concept_graph_for_file(
        file_path,
        detail_output,
        strict_mode,
        GraphOutputFormat::Dot,
    )
}

pub fn run_concept_graph_json_for_repo(
    repo_path: &str,
    detail_output: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_concept_graph_for_repo(
        repo_path,
        detail_output,
        strict_mode,
        GraphOutputFormat::Json,
    )
}

pub fn run_concept_graph_dot_for_repo(
    repo_path: &str,
    detail_output: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_concept_graph_for_repo(
        repo_path,
        detail_output,
        strict_mode,
        GraphOutputFormat::Dot,
    )
}

#[cfg(test)]
fn scan_source_items_for_test(source_code: &str) -> Vec<(String, String)> {
    scan_source_items(source_code)
        .into_iter()
        .map(|item| (item.kind, item.label))
        .collect()
}

#[cfg(test)]
fn parse_concept_graph_comment_for_test(comment: &str) -> Option<String> {
    let parsed = parse_kg_comment(comment, 1)?;
    match parsed {
        KgComment::Node { id, .. } => Some(format!("node {}", id)),
        KgComment::Bind { from, to } => Some(format!("bind {} {}", from, to)),
        KgComment::Edge { kind, from, to, .. } => Some(format!("edge {} {} {}", kind, from, to)),
    }
}

impl ConceptGraphBuilder {
    fn build(
        target_kind: &str,
        target_label: &str,
        source_code: &str,
        runtime_error: &Option<RuntimeError>,
    ) -> ConceptGraph {
        let mut builder = ConceptGraphBuilder::new(target_kind, target_label);
        builder.scan_source(source_code);
        let error = runtime_error
            .as_ref()
            .map(|error| builder.runtime_error_to_graph_error(error));
        ConceptGraph {
            result: if runtime_error.is_none() {
                "success".to_string()
            } else {
                "error".to_string()
            },
            target: builder.target.clone(),
            nodes: builder.nodes,
            edges: builder.edges,
            error,
        }
    }

    fn new(target_kind: &str, target_label: &str) -> Self {
        let source_label = stable_source_label(target_kind, target_label);
        ConceptGraphBuilder {
            target: GraphTarget {
                kind: target_kind.to_string(),
                label: source_label.clone(),
            },
            source_kind: target_kind.to_string(),
            source_label,
            nodes: Vec::new(),
            edges: Vec::new(),
            node_ids: HashSet::new(),
            edge_keys: HashSet::new(),
            formal_nodes_by_name: HashMap::new(),
            chapter_id: None,
            current_source_item_id: None,
            current_formal_id: None,
        }
    }

    fn scan_source(&mut self, source_code: &str) {
        let mut in_source_block = false;
        let mut source_block_start = 0;
        let mut source_block_lines: Vec<String> = Vec::new();

        for (index, line) in source_code.lines().enumerate() {
            let line_number = index + 1;
            let trimmed = line.trim();

            if !in_source_block && trimmed.starts_with("\"\"\"") {
                in_source_block = true;
                source_block_start = line_number;
                source_block_lines.clear();
                let after_open = trimmed.trim_start_matches("\"\"\"");
                if !after_open.trim().is_empty() {
                    source_block_lines.push(after_open.trim().to_string());
                }
                if after_open.trim_end().ends_with("\"\"\"") {
                    in_source_block = false;
                    let block_text = source_block_lines.join("\n");
                    self.add_source_item_from_text(&block_text, source_block_start);
                }
                continue;
            }

            if in_source_block {
                if trimmed.ends_with("\"\"\"") {
                    let before_close = trimmed.trim_end_matches("\"\"\"");
                    if !before_close.trim().is_empty() {
                        source_block_lines.push(before_close.trim().to_string());
                    }
                    in_source_block = false;
                    let block_text = source_block_lines.join("\n");
                    self.add_source_item_from_text(&block_text, source_block_start);
                } else {
                    source_block_lines.push(line.to_string());
                }
                continue;
            }

            if line_number == 1 {
                self.maybe_add_chapter_node(line, line_number);
            }

            if trimmed.starts_with("# kg:") {
                self.apply_kg_comment(trimmed, line_number);
                continue;
            }
            if trimmed.starts_with('#') || trimmed.is_empty() {
                continue;
            }

            self.scan_formal_statement(trimmed, line_number);
            self.scan_low_risk_edges(trimmed, line_number);
        }
    }

    fn maybe_add_chapter_node(&mut self, line: &str, line_number: usize) {
        let trimmed = line.trim();
        if !trimmed.starts_with("# ") {
            return;
        }
        let label = trimmed.trim_start_matches("# ").trim();
        if label.is_empty() {
            return;
        }
        let id = format!("chapter:{}", stable_id_part(label));
        self.chapter_id = Some(id.clone());
        self.add_node(
            id,
            "chapter",
            label,
            self.source(line_number),
            None,
            Some(label.to_string()),
            None,
            Vec::new(),
        );
    }

    fn add_source_item_from_text(&mut self, text: &str, line_number: usize) {
        let Some(item) = parse_source_item(text, line_number) else {
            return;
        };
        let id = format!("source:{}:{}", item.kind, stable_id_part(&item.number));
        self.add_node(
            id.clone(),
            item.kind.as_str(),
            item.label.as_str(),
            self.source(item.line),
            None,
            Some(item.text.clone()),
            None,
            Vec::new(),
        );
        if let Some(chapter_id) = self.chapter_id.clone() {
            self.add_edge(
                &chapter_id,
                &id,
                "contains",
                self.source(item.line),
                "source_label_scan",
                None,
            );
        }
        self.current_source_item_id = Some(id);
        self.current_formal_id = None;
    }

    fn scan_formal_statement(&mut self, trimmed: &str, line_number: usize) {
        if let Some(name) = parse_named_formal(trimmed, "prop") {
            self.add_formal_statement("prop", &name, trimmed, line_number);
            return;
        }
        if let Some(name) = parse_named_formal(trimmed, "abstract_prop") {
            self.add_formal_statement("abstract_prop", &name, trimmed, line_number);
            return;
        }
        if let Some(name) = parse_have_fn_name(trimmed) {
            self.add_formal_statement("fn", &name, trimmed, line_number);
            return;
        }
        if let Some(names) = parse_thm_names(trimmed) {
            let mut first_id = None;
            for name in names {
                let id = self.add_formal_statement("thm", &name, trimmed, line_number);
                if first_id.is_none() {
                    first_id = Some(id);
                }
            }
            self.current_formal_id = first_id;
            return;
        }
        if trimmed == "claim:" || trimmed.starts_with("claim:") {
            let id =
                self.add_formal_statement("claim", &line_number.to_string(), trimmed, line_number);
            self.current_formal_id = Some(id);
            return;
        }
        if trimmed.starts_with("proof_debt") {
            self.add_proof_debt_node(trimmed, line_number);
        }
    }

    fn add_formal_statement(
        &mut self,
        formal_kind: &str,
        name: &str,
        text: &str,
        line_number: usize,
    ) -> String {
        let formal_name = format!("{}:{}", formal_kind, name);
        let id = format!("formal:{}:{}", formal_kind, stable_id_part(name));
        self.add_node(
            id.clone(),
            "formal_statement",
            format!("{} {}", formal_kind, name),
            self.source(line_number),
            Some(formal_name.clone()),
            Some(text.to_string()),
            None,
            Vec::new(),
        );
        self.formal_nodes_by_name.insert(formal_name, id.clone());
        if let Some(source_item_id) = self.current_source_item_id.clone() {
            let edge_kind = if source_item_id.starts_with("source:definition:") {
                "defines"
            } else {
                "formalizes"
            };
            self.add_edge(
                &source_item_id,
                &id,
                edge_kind,
                self.source(line_number),
                "source_label_scan",
                None,
            );
        }
        self.current_formal_id = Some(id.clone());
        id
    }

    fn scan_low_risk_edges(&mut self, trimmed: &str, line_number: usize) {
        if trimmed.starts_with("proof_debt") {
            return;
        }
        if let Some(theorem_name) = parse_by_thm_name(trimmed) {
            if let Some(from_id) = self.current_formal_id.clone() {
                let to_id =
                    self.ensure_ref_node(&format!("formal:thm:{}", theorem_name), line_number);
                self.add_edge(
                    &from_id,
                    &to_id,
                    "depends_on",
                    self.source(line_number),
                    "auto_by_thm",
                    None,
                );
            }
        }
        let Some(from_id) = self.current_formal_id.clone() else {
            return;
        };
        for prop_name in prop_refs_in_line(trimmed) {
            let to_id = self.ensure_ref_node(&format!("formal:prop:{}", prop_name), line_number);
            self.add_edge(
                &from_id,
                &to_id,
                "uses_symbol",
                self.source(line_number),
                "auto_symbol_use",
                None,
            );
        }
    }

    fn add_proof_debt_node(&mut self, trimmed: &str, line_number: usize) {
        let id = format!("proof_debt:{}", line_number);
        self.add_node(
            id.clone(),
            "proof_debt",
            format!("proof_debt at line {}", line_number),
            self.source(line_number),
            None,
            Some(trimmed.to_string()),
            Some("proof_debt".to_string()),
            Vec::new(),
        );
        let from_id = self
            .current_formal_id
            .clone()
            .or_else(|| self.current_source_item_id.clone())
            .or_else(|| self.chapter_id.clone());
        if let Some(from_id) = from_id {
            self.add_edge(
                &from_id,
                &id,
                "has_proof_debt",
                self.source(line_number),
                "auto_proof_debt",
                None,
            );
        }
    }

    fn apply_kg_comment(&mut self, trimmed: &str, line_number: usize) {
        let Some(comment) = parse_kg_comment(trimmed, line_number) else {
            return;
        };
        match comment {
            KgComment::Node {
                id,
                kind,
                label,
                status,
                aliases,
            } => {
                self.add_node(
                    id.clone(),
                    kind.as_str(),
                    label.unwrap_or_else(|| default_label_for_ref(&id)),
                    self.source(line_number),
                    formal_name_from_ref(&id),
                    None,
                    status,
                    aliases,
                );
            }
            KgComment::Bind { from, to } => {
                let from_id = self.ensure_ref_node(&from, line_number);
                let to_id = self.ensure_ref_node(&to, line_number);
                self.add_edge(
                    &from_id,
                    &to_id,
                    "formalizes",
                    self.source(line_number),
                    "kg_comment",
                    None,
                );
            }
            KgComment::Edge {
                kind,
                from,
                to,
                detail,
            } => {
                let from_id = self.ensure_ref_node(&from, line_number);
                let to_id = self.ensure_ref_node(&to, line_number);
                self.add_edge(
                    &from_id,
                    &to_id,
                    &kind,
                    self.source(line_number),
                    "kg_comment",
                    detail,
                );
            }
        }
    }

    fn ensure_ref_node(&mut self, reference: &str, line_number: usize) -> String {
        let id = normalize_ref_id(reference);
        if self.node_ids.contains(&id) {
            return id;
        }
        let (kind, label, formal_name) = node_fields_for_ref(&id);
        self.add_node(
            id.clone(),
            kind.as_str(),
            label,
            self.source(line_number),
            formal_name,
            None,
            None,
            Vec::new(),
        );
        id
    }

    fn add_node(
        &mut self,
        id: String,
        kind: &str,
        label: impl Into<String>,
        source: GraphSource,
        formal_name: Option<String>,
        text: Option<String>,
        status: Option<String>,
        aliases: Vec<String>,
    ) {
        let label = label.into();
        if !self.node_ids.insert(id.clone()) {
            return;
        }
        self.nodes.push(ConceptNode {
            id,
            kind: kind.to_string(),
            label,
            source,
            formal_name,
            text,
            status,
            aliases,
        });
    }

    fn add_edge(
        &mut self,
        from: &str,
        to: &str,
        kind: &str,
        source: GraphSource,
        provenance: &str,
        detail: Option<String>,
    ) {
        if from == to {
            return;
        }
        let key = format!(
            "{}->{}:{}:{}:{}",
            from,
            to,
            kind,
            provenance,
            detail.clone().unwrap_or_default()
        );
        if !self.edge_keys.insert(key) {
            return;
        }
        self.edges.push(ConceptEdge {
            from: from.to_string(),
            to: to.to_string(),
            kind: kind.to_string(),
            source,
            provenance: provenance.to_string(),
            detail,
        });
    }

    fn source(&self, line: usize) -> GraphSource {
        GraphSource {
            line,
            source_kind: self.source_kind.clone(),
            source: self.source_label.clone(),
        }
    }

    fn runtime_error_to_graph_error(&self, error: &RuntimeError) -> ConceptGraphError {
        ConceptGraphError {
            error_type: error.display_label().to_string(),
            message: runtime_error_message(error),
            source: self.source(error.line_file().0),
        }
    }
}

fn run_concept_graph_for_file(
    file_path: &str,
    detail_output: bool,
    strict_mode: bool,
    format: GraphOutputFormat,
) -> (bool, String) {
    let resolved_path = match crate::runner::resolve_litex_file_path(file_path) {
        Ok(path) => path,
        Err(message) => return target_error_graph("file", message, format),
    };
    let source_code = match fs::read_to_string(resolved_path.as_str()) {
        Ok(content) => content,
        Err(error) => {
            return target_error_graph("file", format!("could not read file: {}", error), format)
        }
    };
    run_concept_graph_on_source(
        "file",
        resolved_path.as_str(),
        source_code.as_str(),
        detail_output,
        strict_mode,
        format,
    )
}

fn run_concept_graph_for_repo(
    repo_path: &str,
    detail_output: bool,
    strict_mode: bool,
    format: GraphOutputFormat,
) -> (bool, String) {
    let joined = Path::new(repo_path).join(MAIN_DOT_LIT);
    let Some(joined_string) = joined.to_str() else {
        return target_error_graph("repo", "repo path is not valid UTF-8".to_string(), format);
    };
    let resolved_path = match crate::runner::resolve_litex_file_path(joined_string) {
        Ok(path) => path,
        Err(message) => return target_error_graph("repo", message, format),
    };
    let source_code = match fs::read_to_string(resolved_path.as_str()) {
        Ok(content) => content,
        Err(error) => {
            return target_error_graph("repo", format!("could not read file: {}", error), format);
        }
    };
    run_concept_graph_on_source(
        "repo",
        resolved_path.as_str(),
        source_code.as_str(),
        detail_output,
        strict_mode,
        format,
    )
}

fn run_concept_graph_on_source(
    target_kind: &str,
    target_label: &str,
    source_code: &str,
    detail_output: bool,
    strict_mode: bool,
    format: GraphOutputFormat,
) -> (bool, String) {
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(target_label);
    runtime.detail_output = detail_output;
    runtime.strict_mode = strict_mode;
    let normalized_source = remove_windows_carriage_return(source_code);
    let (_stmt_results, runtime_error) = run_source_code(normalized_source.as_str(), &mut runtime);
    let ok = runtime_error.is_none();
    let output = match format {
        GraphOutputFormat::Json => concept_graph_json_for_source(
            target_kind,
            target_label,
            normalized_source.as_str(),
            &runtime_error,
        ),
        GraphOutputFormat::Dot => concept_graph_dot_for_source(
            target_kind,
            target_label,
            normalized_source.as_str(),
            &runtime_error,
        ),
    };
    (ok, strip_free_param_numeric_tags_in_display(&output))
}

fn target_error_graph(
    target_kind: &str,
    message: String,
    format: GraphOutputFormat,
) -> (bool, String) {
    let target = GraphTarget {
        kind: target_kind.to_string(),
        label: stable_source_label(target_kind, ""),
    };
    let error = ConceptGraphError {
        error_type: "TargetError".to_string(),
        message,
        source: GraphSource {
            line: 0,
            source_kind: target_kind.to_string(),
            source: target.label.clone(),
        },
    };
    let graph = ConceptGraph {
        result: "error".to_string(),
        target,
        nodes: Vec::new(),
        edges: Vec::new(),
        error: Some(error),
    };
    let output = match format {
        GraphOutputFormat::Json => render_json_value(&graph_to_json(&graph), 0),
        GraphOutputFormat::Dot => graph_to_dot(&graph),
    };
    (false, output)
}

fn graph_to_json(graph: &ConceptGraph) -> JsonValue {
    JsonValue::Object(vec![
        (
            "schema_version".to_string(),
            JsonValue::JsonString(SCHEMA_VERSION.to_string()),
        ),
        (
            "result".to_string(),
            JsonValue::JsonString(graph.result.clone()),
        ),
        ("target".to_string(), target_to_json(&graph.target)),
        (
            "nodes".to_string(),
            JsonValue::Array(graph.nodes.iter().map(node_to_json).collect()),
        ),
        (
            "edges".to_string(),
            JsonValue::Array(graph.edges.iter().map(edge_to_json).collect()),
        ),
        (
            "error".to_string(),
            graph
                .error
                .as_ref()
                .map(error_to_json)
                .unwrap_or(JsonValue::Null),
        ),
    ])
}

fn target_to_json(target: &GraphTarget) -> JsonValue {
    JsonValue::Object(vec![
        (
            "kind".to_string(),
            JsonValue::JsonString(target.kind.clone()),
        ),
        (
            "label".to_string(),
            JsonValue::JsonString(target.label.clone()),
        ),
    ])
}

fn node_to_json(node: &ConceptNode) -> JsonValue {
    let mut fields = vec![
        ("id".to_string(), JsonValue::JsonString(node.id.clone())),
        ("kind".to_string(), JsonValue::JsonString(node.kind.clone())),
        (
            "label".to_string(),
            JsonValue::JsonString(node.label.clone()),
        ),
        ("source".to_string(), source_to_json(&node.source)),
    ];
    if let Some(formal_name) = &node.formal_name {
        fields.push((
            "formal_name".to_string(),
            JsonValue::JsonString(formal_name.clone()),
        ));
    }
    if let Some(text) = &node.text {
        fields.push(("text".to_string(), JsonValue::JsonString(text.clone())));
    }
    if let Some(status) = &node.status {
        fields.push(("status".to_string(), JsonValue::JsonString(status.clone())));
    }
    if !node.aliases.is_empty() {
        fields.push((
            "aliases".to_string(),
            JsonValue::Array(
                node.aliases
                    .iter()
                    .map(|alias| JsonValue::JsonString(alias.clone()))
                    .collect(),
            ),
        ));
    }
    JsonValue::Object(fields)
}

fn edge_to_json(edge: &ConceptEdge) -> JsonValue {
    let mut fields = vec![
        ("from".to_string(), JsonValue::JsonString(edge.from.clone())),
        ("to".to_string(), JsonValue::JsonString(edge.to.clone())),
        ("kind".to_string(), JsonValue::JsonString(edge.kind.clone())),
        ("source".to_string(), source_to_json(&edge.source)),
        (
            "provenance".to_string(),
            JsonValue::JsonString(edge.provenance.clone()),
        ),
    ];
    if let Some(detail) = &edge.detail {
        fields.push(("detail".to_string(), JsonValue::JsonString(detail.clone())));
    }
    JsonValue::Object(fields)
}

fn source_to_json(source: &GraphSource) -> JsonValue {
    JsonValue::Object(vec![
        (
            "line".to_string(),
            if source.line == 0 {
                JsonValue::Null
            } else {
                JsonValue::Number(source.line)
            },
        ),
        (
            "source_kind".to_string(),
            JsonValue::JsonString(source.source_kind.clone()),
        ),
        (
            "source".to_string(),
            JsonValue::JsonString(source.source.clone()),
        ),
    ])
}

fn error_to_json(error: &ConceptGraphError) -> JsonValue {
    JsonValue::Object(vec![
        (
            "error_type".to_string(),
            JsonValue::JsonString(error.error_type.clone()),
        ),
        (
            "message".to_string(),
            JsonValue::JsonString(error.message.clone()),
        ),
        ("source".to_string(), source_to_json(&error.source)),
    ])
}

fn graph_to_dot(graph: &ConceptGraph) -> String {
    let mut out = String::new();
    out.push_str("digraph litex_concept_graph {\n");
    out.push_str("  rankdir=LR;\n");
    out.push_str("  node [shape=box, style=rounded];\n");
    for node in &graph.nodes {
        let label = format!("{}\\n{}", node.kind, compact_dot_label(&node.label));
        out.push_str(&format!(
            "  {} [label={}];\n",
            dot_id(&node.id),
            dot_string(&label)
        ));
    }
    for edge in &graph.edges {
        out.push_str(&format!(
            "  {} -> {} [label={}];\n",
            dot_id(&edge.from),
            dot_id(&edge.to),
            dot_string(&edge.kind)
        ));
    }
    out.push_str("}\n");
    out
}

fn parse_source_item(text: &str, line_number: usize) -> Option<SourceItem> {
    let compact = text
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>()
        .join(" ");
    let (raw_kind, rest) = split_first_word(&compact)?;
    let kind = source_item_kind(raw_kind)?;
    let number = parse_source_number(rest)?;
    let label_kind = match raw_kind {
        "Definitions" => "Definition",
        "Examples" => "Example",
        other => other,
    };
    let label = format!("{} {}", label_kind, number);
    Some(SourceItem {
        kind,
        number,
        label,
        text: compact,
        line: line_number,
    })
}

fn source_item_kind(word: &str) -> Option<String> {
    match word {
        "Definition" | "Definitions" => Some("definition".to_string()),
        "Theorem" => Some("theorem".to_string()),
        "Proposition" => Some("theorem".to_string()),
        "Lemma" => Some("lemma".to_string()),
        "Corollary" => Some("corollary".to_string()),
        "Example" | "Examples" => Some("example".to_string()),
        "Remark" => Some("remark".to_string()),
        "Exercise" => Some("exercise".to_string()),
        _ => None,
    }
}

fn parse_source_number(rest: &str) -> Option<String> {
    let trimmed = rest.trim_start();
    let mut number = String::new();
    for ch in trimmed.chars() {
        if ch.is_ascii_digit() || ch == '.' {
            number.push(ch);
        } else {
            break;
        }
    }
    if number.is_empty() {
        None
    } else {
        Some(number.trim_end_matches('.').to_string())
    }
}

#[cfg(test)]
fn scan_source_items(source_code: &str) -> Vec<SourceItem> {
    let mut items = Vec::new();
    let mut in_source_block = false;
    let mut source_block_start = 0;
    let mut source_block_lines: Vec<String> = Vec::new();

    for (index, line) in source_code.lines().enumerate() {
        let line_number = index + 1;
        let trimmed = line.trim();
        if !in_source_block && trimmed.starts_with("\"\"\"") {
            in_source_block = true;
            source_block_start = line_number;
            source_block_lines.clear();
            continue;
        }
        if in_source_block {
            if trimmed.ends_with("\"\"\"") {
                in_source_block = false;
                let block_text = source_block_lines.join("\n");
                if let Some(item) = parse_source_item(&block_text, source_block_start) {
                    items.push(item);
                }
            } else {
                source_block_lines.push(line.to_string());
            }
        }
    }
    items
}

fn parse_kg_comment(line: &str, _line_number: usize) -> Option<KgComment> {
    let rest = line.trim().strip_prefix("# kg:")?.trim();
    let tokens = tokenize_kg_comment(rest);
    if tokens.is_empty() {
        return None;
    }
    match tokens[0].as_str() {
        "node" => parse_kg_node(&tokens),
        "bind" => {
            if tokens.len() < 3 {
                None
            } else {
                Some(KgComment::Bind {
                    from: normalize_ref_id(&tokens[1]),
                    to: normalize_ref_id(&tokens[2]),
                })
            }
        }
        "edge" => parse_kg_edge(&tokens),
        _ => None,
    }
}

fn parse_kg_node(tokens: &[String]) -> Option<KgComment> {
    if tokens.len() < 3 {
        return None;
    }
    let kind = tokens[1].clone();
    let id = if tokens[2].contains(':') {
        normalize_ref_id(&tokens[2])
    } else {
        format!("{}:{}", kind, stable_id_part(&tokens[2]))
    };
    let attrs = kg_attrs(&tokens[3..]);
    Some(KgComment::Node {
        id,
        kind,
        label: attrs.get("label").cloned(),
        status: attrs.get("status").cloned(),
        aliases: attrs
            .get("aliases")
            .map(|aliases| {
                aliases
                    .split(',')
                    .map(str::trim)
                    .filter(|alias| !alias.is_empty())
                    .map(str::to_string)
                    .collect()
            })
            .unwrap_or_default(),
    })
}

fn parse_kg_edge(tokens: &[String]) -> Option<KgComment> {
    if tokens.len() < 4 {
        return None;
    }
    let attrs = kg_attrs(&tokens[4..]);
    let detail = attrs
        .get("detail")
        .cloned()
        .or_else(|| attrs.get("source").cloned());
    Some(KgComment::Edge {
        kind: tokens[1].clone(),
        from: normalize_ref_id(&tokens[2]),
        to: normalize_ref_id(&tokens[3]),
        detail,
    })
}

fn tokenize_kg_comment(text: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut in_quote = false;
    for ch in text.chars() {
        match ch {
            '"' => {
                in_quote = !in_quote;
            }
            c if c.is_whitespace() && !in_quote => {
                if !current.is_empty() {
                    tokens.push(current.clone());
                    current.clear();
                }
            }
            c => current.push(c),
        }
    }
    if !current.is_empty() {
        tokens.push(current);
    }
    tokens
}

fn kg_attrs(tokens: &[String]) -> HashMap<String, String> {
    let mut attrs = HashMap::new();
    for token in tokens {
        let Some((key, value)) = token.split_once('=') else {
            continue;
        };
        attrs.insert(key.to_string(), value.to_string());
    }
    attrs
}

fn parse_named_formal(line: &str, keyword: &str) -> Option<String> {
    let rest = line.strip_prefix(keyword)?;
    let rest = rest.trim_start();
    if rest.is_empty() {
        return None;
    }
    Some(take_identifier(rest))
}

fn parse_have_fn_name(line: &str) -> Option<String> {
    let rest = line.strip_prefix("have")?.trim_start();
    let rest = rest.strip_prefix("fn")?.trim_start();
    let rest = rest
        .strip_prefix("as algo")
        .map(str::trim_start)
        .unwrap_or(rest);
    if rest.is_empty() {
        return None;
    }
    Some(take_identifier(rest))
}

fn parse_thm_names(line: &str) -> Option<Vec<String>> {
    let rest = line.strip_prefix("thm")?.trim_start();
    let before_colon = rest.split(':').next().unwrap_or(rest);
    let names = before_colon
        .split(',')
        .map(str::trim)
        .filter(|name| !name.is_empty())
        .map(take_identifier)
        .collect::<Vec<_>>();
    if names.is_empty() {
        None
    } else {
        Some(names)
    }
}

fn parse_by_thm_name(line: &str) -> Option<String> {
    let rest = line.strip_prefix("by thm")?.trim_start();
    if rest.is_empty() {
        return None;
    }
    Some(take_identifier(rest))
}

fn prop_refs_in_line(line: &str) -> Vec<String> {
    let mut refs = Vec::new();
    let chars = line.chars().collect::<Vec<_>>();
    let mut index = 0;
    while index < chars.len() {
        if chars[index] != '$' {
            index += 1;
            continue;
        }
        index += 1;
        let start = index;
        while index < chars.len()
            && (chars[index].is_ascii_alphanumeric() || chars[index] == '_' || chars[index] == ':')
        {
            index += 1;
        }
        if index > start {
            let name = chars[start..index].iter().collect::<String>();
            if !refs.contains(&name) {
                refs.push(name);
            }
        }
    }
    refs
}

fn take_identifier(text: &str) -> String {
    text.chars()
        .take_while(|ch| ch.is_ascii_alphanumeric() || *ch == '_' || *ch == ':')
        .collect()
}

fn split_first_word(text: &str) -> Option<(&str, &str)> {
    let trimmed = text.trim_start();
    let mut split_at = trimmed.len();
    for (index, ch) in trimmed.char_indices() {
        if ch.is_whitespace() {
            split_at = index;
            break;
        }
    }
    if split_at == 0 {
        return None;
    }
    let word = &trimmed[..split_at];
    let rest = &trimmed[split_at..];
    Some((word, rest))
}

fn normalize_ref_id(reference: &str) -> String {
    let parts = reference.split(':').collect::<Vec<_>>();
    if parts.len() >= 2 {
        let prefix = parts[..parts.len() - 1].join(":");
        let name = parts[parts.len() - 1];
        return format!("{}:{}", prefix, stable_id_part(name));
    }
    stable_id_part(reference)
}

fn node_fields_for_ref(reference: &str) -> (String, String, Option<String>) {
    let parts = reference.split(':').collect::<Vec<_>>();
    if parts.first() == Some(&"concept") {
        return (
            "concept".to_string(),
            default_label_for_ref(reference),
            None,
        );
    }
    if parts.first() == Some(&"formal") && parts.len() >= 3 {
        let formal_name = parts[1..].join(":");
        return (
            "formal_statement".to_string(),
            formal_name.clone(),
            Some(formal_name),
        );
    }
    if parts.first() == Some(&"symbol") {
        return ("symbol".to_string(), default_label_for_ref(reference), None);
    }
    (
        "concept".to_string(),
        default_label_for_ref(reference),
        None,
    )
}

fn formal_name_from_ref(reference: &str) -> Option<String> {
    let parts = reference.split(':').collect::<Vec<_>>();
    if parts.first() == Some(&"formal") && parts.len() >= 3 {
        Some(parts[1..].join(":"))
    } else {
        None
    }
}

fn default_label_for_ref(reference: &str) -> String {
    reference
        .split(':')
        .last()
        .unwrap_or(reference)
        .replace('_', " ")
}

fn stable_source_label(target_kind: &str, target_label: &str) -> String {
    match target_kind {
        "code" => "code".to_string(),
        "repo" => "main.lit".to_string(),
        "file" => Path::new(target_label)
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("entry")
            .to_string(),
        _ => "entry".to_string(),
    }
}

fn stable_id_part(text: &str) -> String {
    let mut out = String::new();
    let mut last_was_underscore = false;
    for ch in text.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
            last_was_underscore = false;
        } else if !last_was_underscore {
            out.push('_');
            last_was_underscore = true;
        }
    }
    let trimmed = out.trim_matches('_').to_string();
    if trimmed.is_empty() {
        "unnamed".to_string()
    } else {
        trimmed
    }
}

fn runtime_error_message(error: &RuntimeError) -> String {
    match error {
        RuntimeError::ArithmeticError(e)
        | RuntimeError::NewFactError(e)
        | RuntimeError::StoreFactError(e)
        | RuntimeError::ParseError(e)
        | RuntimeError::ExecStmtError(e)
        | RuntimeError::WellDefinedError(e)
        | RuntimeError::VerifyError(e)
        | RuntimeError::UnknownError(e)
        | RuntimeError::InferError(e)
        | RuntimeError::NameAlreadyUsedError(e)
        | RuntimeError::DefineParamsError(e)
        | RuntimeError::InstantiateError(e) => e.msg.clone(),
    }
}

fn dot_id(id: &str) -> String {
    json_string_literal(id)
}

fn dot_string(text: &str) -> String {
    json_string_literal(text)
}

fn compact_dot_label(text: &str) -> String {
    let one_line = text
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>()
        .join(" ");
    if one_line.len() <= 96 {
        one_line
    } else {
        format!("{}...", &one_line[..96])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_label_scanner_recognizes_main_item_kinds() {
        let source = r#"
"""
Definition 6.1.1. A definition.
"""
"""
Proposition 6.1.2. A proposition.
"""
"""
Lemma 6.1.3. A lemma.
"""
"""
Corollary 6.1.4. A corollary.
"""
"""
Example 6.1.5. An example.
"""
"""
Remark 6.1.6. A remark.
"""
"""
Exercise 6.1.7. An exercise.
"""
"#;
        let items = scan_source_items_for_test(source);
        assert_eq!(
            items[0],
            ("definition".to_string(), "Definition 6.1.1".to_string())
        );
        assert_eq!(
            items[1],
            ("theorem".to_string(), "Proposition 6.1.2".to_string())
        );
        assert_eq!(items[2], ("lemma".to_string(), "Lemma 6.1.3".to_string()));
        assert_eq!(
            items[3],
            ("corollary".to_string(), "Corollary 6.1.4".to_string())
        );
        assert_eq!(
            items[4],
            ("example".to_string(), "Example 6.1.5".to_string())
        );
        assert_eq!(items[5], ("remark".to_string(), "Remark 6.1.6".to_string()));
        assert_eq!(
            items[6],
            ("exercise".to_string(), "Exercise 6.1.7".to_string())
        );
    }

    #[test]
    fn kg_comment_parser_recognizes_node_bind_and_edge() {
        assert_eq!(
            parse_concept_graph_comment_for_test(
                "# kg: node concept sequence_limit label=\"limit of a sequence\""
            ),
            Some("node concept:sequence_limit".to_string())
        );
        assert_eq!(
            parse_concept_graph_comment_for_test(
                "# kg: bind concept:sequence_limit formal:prop:has_limit"
            ),
            Some("bind concept:sequence_limit formal:prop:has_limit".to_string())
        );
        assert_eq!(
            parse_concept_graph_comment_for_test(
                "# kg: edge depends_on concept:sequence_limit concept:epsilon_closeness source=\"Definition 6.1.5\""
            ),
            Some(
                "edge depends_on concept:sequence_limit concept:epsilon_closeness".to_string()
            )
        );
    }
}
