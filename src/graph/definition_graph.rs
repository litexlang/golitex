use super::graph::{by_thm_names_in_stmts, DepCollector};
use crate::prelude::*;
use std::collections::HashMap;

const DEFINITION_GRAPH_NAME: &str = "litex-definition-graph";
const DEFINITION_GRAPH_VERSION: &str = "0.1";

struct DefinitionGraphNode {
    id: String,
    kind: String,
    definition_kind: String,
    name: String,
    label: String,
    defined: bool,
    line_file: Option<LineFile>,
    statement: Option<String>,
}

struct DefinitionGraphEdge {
    from: String,
    to: String,
    kind: String,
    count: usize,
}

struct DefinitionGraphBuilder {
    nodes: Vec<DefinitionGraphNode>,
    node_index: HashMap<String, usize>,
    edges: Vec<DefinitionGraphEdge>,
    edge_index: HashMap<String, usize>,
}

pub fn run_definition_graph_for_code(
    code: &str,
    label: &str,
    hide_file_paths: bool,
) -> (bool, String) {
    run_definition_graph_for_code_with_language(
        code,
        label,
        hide_file_paths,
        OutputLanguage::English,
    )
}

pub fn run_definition_graph_for_code_with_language(
    code: &str,
    label: &str,
    hide_file_paths: bool,
    _output_language: OutputLanguage,
) -> (bool, String) {
    run_definition_graph_on_source("code", label, code, hide_file_paths, false)
}

pub fn run_definition_graph_for_code_strict(
    code: &str,
    label: &str,
    hide_file_paths: bool,
) -> (bool, String) {
    run_definition_graph_for_code_strict_with_language(
        code,
        label,
        hide_file_paths,
        OutputLanguage::English,
    )
}

pub fn run_definition_graph_for_code_strict_with_language(
    code: &str,
    label: &str,
    hide_file_paths: bool,
    _output_language: OutputLanguage,
) -> (bool, String) {
    run_definition_graph_on_source("code", label, code, hide_file_paths, true)
}

pub fn run_definition_graph_for_file(file_path: &str, hide_file_paths: bool) -> (bool, String) {
    run_definition_graph_for_file_with_strict(file_path, hide_file_paths, false)
}

pub fn run_definition_graph_for_file_with_strict(
    file_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_definition_graph_for_file_with_strict_and_language(
        file_path,
        hide_file_paths,
        strict_mode,
        OutputLanguage::English,
    )
}

pub fn run_definition_graph_for_file_with_strict_and_language(
    file_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
) -> (bool, String) {
    run_definition_graph_for_file_with_strict_language_and_isolation(
        file_path,
        hide_file_paths,
        strict_mode,
        output_language,
        false,
    )
}

pub fn run_definition_graph_for_file_with_strict_language_and_isolation(
    file_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
    _output_language: OutputLanguage,
    force_isolated: bool,
) -> (bool, String) {
    let resolved_path = match resolve_litex_file_path(file_path) {
        Ok(path) => path,
        Err(message) => {
            return definition_graph_target_error_output(
                "file",
                file_path,
                hide_file_paths,
                message,
            );
        }
    };

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.detail_output = !hide_file_paths;
    runtime.strict_mode = strict_mode;
    let (stmt_results, runtime_error) = crate::pipeline::run_file_with_project_context(
        resolved_path.as_str(),
        &mut runtime,
        force_isolated,
    );
    render_definition_graph_result(
        "file",
        resolved_path.as_str(),
        hide_file_paths,
        &mut runtime,
        stmt_results.as_slice(),
        runtime_error.as_ref(),
    )
}

pub fn run_definition_graph_for_repo(repo_path: &str, hide_file_paths: bool) -> (bool, String) {
    run_definition_graph_for_repo_with_strict(repo_path, hide_file_paths, false)
}

pub fn run_definition_graph_for_repo_with_strict(
    repo_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_definition_graph_for_repo_with_strict_and_language(
        repo_path,
        hide_file_paths,
        strict_mode,
        OutputLanguage::English,
    )
}

pub fn run_definition_graph_for_repo_with_strict_and_language(
    repo_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
    _output_language: OutputLanguage,
) -> (bool, String) {
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.detail_output = !hide_file_paths;
    runtime.strict_mode = strict_mode;
    if let Err(error) = discover_repository(&mut runtime, repo_path) {
        return render_definition_graph_result(
            "repo",
            repo_path,
            hide_file_paths,
            &mut runtime,
            &[],
            Some(&error),
        );
    }
    let entry_module_id = runtime.current_module_id();
    let (stmt_results, runtime_error) = crate::pipeline::run_repository_file_target(
        &mut runtime,
        RepositoryFileTarget::Module(entry_module_id),
    );
    render_definition_graph_result(
        "repo",
        repo_path,
        hide_file_paths,
        &mut runtime,
        stmt_results.as_slice(),
        runtime_error.as_ref(),
    )
}

fn run_definition_graph_on_source(
    target_kind: &str,
    target_label: &str,
    source_code: &str,
    hide_file_paths: bool,
    strict_mode: bool,
) -> (bool, String) {
    let normalized_source = remove_windows_carriage_return(source_code);
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(target_label);
    runtime.detail_output = !hide_file_paths;
    runtime.strict_mode = strict_mode;
    let (stmt_results, runtime_error) = run_source_code(normalized_source.as_str(), &mut runtime);
    render_definition_graph_result(
        target_kind,
        target_label,
        hide_file_paths,
        &mut runtime,
        stmt_results.as_slice(),
        runtime_error.as_ref(),
    )
}

/// Render the definition inventory retained by the active environment.
///
/// Unlike the relation graph, this projection starts from environment tables,
/// so aliases and reusable interfaces appear as the definitions later code can
/// actually resolve.
pub fn render_definition_graph_from_stmt_results(
    target_kind: &str,
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
    )
}

fn render_definition_graph_result(
    target_kind: &str,
    target_label: &str,
    hide_file_paths: bool,
    runtime: &mut Runtime,
    _stmt_results: &[StmtResult],
    runtime_error: Option<&RuntimeError>,
) -> (bool, String) {
    let ok = runtime_error.is_none();
    let error = runtime_error.map(|error| display_runtime_error_json(runtime, error, true));
    let graph = DefinitionGraphBuilder::from_environment(runtime.top_level_env());
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
        (
            "mermaid".to_string(),
            JsonValue::JsonString(graph.mermaid()),
        ),
    ];
    fields.sort_by(|left, right| left.0.cmp(&right.0));
    (ok, render_json_value(&JsonValue::Object(fields), 0))
}

fn definition_graph_target_error_output(
    target_kind: &str,
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
        (
            "mermaid".to_string(),
            JsonValue::JsonString("flowchart LR".to_string()),
        ),
    ]);
    (false, render_json_value(&output, 0))
}

fn definition_graph_target_json_value(
    target_kind: &str,
    target_label: &str,
    hide_file_paths: bool,
) -> JsonValue {
    let label = if hide_file_paths && target_kind != "code" {
        "entry".to_string()
    } else {
        target_label.to_string()
    };
    JsonValue::Object(vec![
        (
            "kind".to_string(),
            JsonValue::JsonString(target_kind.to_string()),
        ),
        ("label".to_string(), JsonValue::JsonString(label)),
    ])
}

impl DefinitionGraphBuilder {
    fn new() -> Self {
        Self {
            nodes: vec![],
            node_index: HashMap::new(),
            edges: vec![],
            edge_index: HashMap::new(),
        }
    }

    fn from_environment(environment: &Environment) -> Self {
        let mut builder = Self::new();
        builder.add_identifiers(environment);
        builder.add_props(environment);
        builder.add_functions(environment);
        builder.add_algorithms(environment);
        builder.add_structs(environment);
        builder.add_templates(environment);
        builder.add_theorems(environment);
        builder.add_strategies(environment);
        builder
    }

    fn add_identifiers(&mut self, environment: &Environment) {
        let mut identifiers = environment.defined_identifiers.iter().collect::<Vec<_>>();
        identifiers.sort_by(|left, right| left.0.cmp(right.0));
        for (name, kind) in identifiers {
            self.ensure_node(
                definition_id("identifier", name),
                "identifier",
                "identifier",
                name,
                true,
                None,
                Some(&format!("identifier {}: {:?}", name, kind)),
            );
        }
    }

    fn add_props(&mut self, environment: &Environment) {
        let mut abstract_props = environment
            .defined_abstract_props
            .iter()
            .collect::<Vec<_>>();
        abstract_props.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in abstract_props {
            self.ensure_node(
                definition_id("prop", name),
                "prop",
                "abstract_prop",
                name,
                true,
                Some(&definition.line_file),
                Some(&definition.to_string()),
            );
        }

        let mut props = environment.defined_def_props.iter().collect::<Vec<_>>();
        props.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in props {
            let node_id = definition_id("prop", name);
            self.ensure_node(
                node_id.clone(),
                "prop",
                "prop",
                name,
                true,
                Some(&definition.line_file),
                Some(&definition.to_string()),
            );
            let mut collector = DepCollector::new();
            collector.collect_param_def_with_type_deps(&definition.params_def_with_type);
            collector.add_param_def_with_type(&definition.params_def_with_type);
            for fact in &definition.iff_facts {
                collector.collect_fact(fact);
            }
            self.add_dependency_edges(&node_id, collector);
        }
    }

    fn add_functions(&mut self, environment: &Environment) {
        let mut functions = environment.known_objs_in_fn_sets.iter().collect::<Vec<_>>();
        functions.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in functions {
            let node_id = definition_id("fn", name);
            let line_file = definition
                .equal_to
                .as_ref()
                .map(|(_, line_file)| line_file)
                .or_else(|| definition.fn_set.as_ref().map(|(_, line_file)| line_file))
                .or_else(|| {
                    definition
                        .restrict_to
                        .as_ref()
                        .and_then(|items| items.first().map(|(_, line_file)| line_file))
                });
            self.ensure_node(
                node_id.clone(),
                "fn",
                "function",
                name,
                true,
                line_file,
                Some(&format!("have fn {}", name)),
            );
            let mut collector = DepCollector::new();
            collector.add_local_name(name);
            if let Some((fn_set, _)) = definition.fn_set.as_ref() {
                collector.collect_fn_set_body(fn_set);
            }
            if let Some((equal_to, _)) = definition.equal_to.as_ref() {
                collector.collect_obj(equal_to);
            }
            if let Some(restrictions) = definition.restrict_to.as_ref() {
                for (fn_set, _) in restrictions {
                    collector.collect_fn_set_body(fn_set);
                }
            }
            self.add_dependency_edges(&node_id, collector);
        }
    }

    fn add_algorithms(&mut self, environment: &Environment) {
        let mut algorithms = environment.defined_algorithms.iter().collect::<Vec<_>>();
        algorithms.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in algorithms {
            let node_id = definition_id("algorithm", name);
            self.ensure_node(
                node_id.clone(),
                "algorithm",
                "algorithm",
                name,
                true,
                Some(&definition.line_file),
                Some(&definition.to_string()),
            );
            let mut collector = DepCollector::new();
            for parameter in &definition.params {
                collector.add_local_name(parameter);
            }
            for case in &definition.cases {
                collector.collect_atomic_fact(&case.condition);
                collector.collect_obj(&case.return_stmt.value);
            }
            if let Some(default_return) = definition.default_return.as_ref() {
                collector.collect_obj(&default_return.value);
            }
            self.add_dependency_edges(&node_id, collector);
        }
    }

    fn add_structs(&mut self, environment: &Environment) {
        let mut structs = environment.defined_structs.iter().collect::<Vec<_>>();
        structs.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in structs {
            let node_id = definition_id("struct", name);
            self.ensure_node(
                node_id.clone(),
                "struct",
                "structure",
                name,
                true,
                Some(&definition.line_file),
                Some(&definition.to_string()),
            );
            let mut collector = DepCollector::new();
            if let Some((params, dom_facts)) = definition.param_def_with_dom.as_ref() {
                collector.collect_param_def_with_type_deps(params);
                collector.add_param_def_with_type(params);
                for fact in dom_facts {
                    collector.collect_or_and_chain_atomic_fact(fact);
                }
            }
            for (_, field) in &definition.fields {
                collector.collect_obj(field);
            }
            for fact in &definition.equivalent_facts {
                collector.collect_fact(fact);
            }
            self.add_dependency_edges(&node_id, collector);
        }
    }

    fn add_templates(&mut self, environment: &Environment) {
        let mut templates = environment.defined_templates.iter().collect::<Vec<_>>();
        templates.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in templates {
            let node_id = definition_id("template", name);
            self.ensure_node(
                node_id.clone(),
                "template",
                "template",
                name,
                true,
                Some(&definition.line_file),
                Some(&format!("template {}", name)),
            );
            let mut collector = DepCollector::new();
            collector.collect_param_def_with_type_deps(&definition.template_arg_def);
            collector.add_param_def_with_type(&definition.template_arg_def);
            for fact in &definition.template_arg_dom {
                collector.collect_or_and_chain_atomic_fact(fact);
            }
            collect_template_definition_dependencies(&mut collector, &definition.template_def_stmt);
            self.add_dependency_edges(&node_id, collector);
        }
    }

    fn add_theorems(&mut self, environment: &Environment) {
        let mut theorems = environment.defined_thm_stmts.iter().collect::<Vec<_>>();
        theorems.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in theorems {
            let definition_kind = if definition.is_axiom() {
                "axiom"
            } else {
                "theorem"
            };
            let node_id = definition_id("theorem", name);
            self.ensure_node(
                node_id.clone(),
                "theorem",
                definition_kind,
                name,
                true,
                Some(&definition.line_file),
                Some(&definition.to_string()),
            );
            let mut collector = DepCollector::new();
            collector.collect_forall_fact(&definition.forall_fact);
            self.add_dependency_edges(&node_id, collector);
            self.add_theorem_edges(&node_id, &definition.prove_process);
        }
    }

    fn add_strategies(&mut self, environment: &Environment) {
        let mut strategies = environment
            .defined_strategy_stmts
            .iter()
            .collect::<Vec<_>>();
        strategies.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in strategies {
            let node_id = definition_id("strategy", name);
            self.ensure_node(
                node_id.clone(),
                "strategy",
                "strategy",
                name,
                true,
                Some(&definition.line_file),
                Some(&definition.to_string()),
            );
            let mut collector = DepCollector::new();
            collector.collect_forall_fact(&definition.forall_fact);
            self.add_dependency_edges(&node_id, collector);
            self.add_theorem_edges(&node_id, &definition.prove_process);
        }
    }

    fn add_dependency_edges(&mut self, target_id: &str, collector: DepCollector) {
        for name in collector.deps.props {
            let source_id = definition_id("prop", &name);
            self.ensure_node(source_id.clone(), "prop", "prop", &name, false, None, None);
            self.add_edge(&source_id, target_id, "uses_prop");
        }
        for name in collector.deps.fns {
            let source_id = definition_id("fn", &name);
            self.ensure_node(
                source_id.clone(),
                "fn",
                "function",
                &name,
                false,
                None,
                None,
            );
            self.add_edge(&source_id, target_id, "uses_fn");
        }
        for name in collector.deps.structs {
            let source_id = definition_id("struct", &name);
            self.ensure_node(
                source_id.clone(),
                "struct",
                "structure",
                &name,
                false,
                None,
                None,
            );
            self.add_edge(&source_id, target_id, "uses_struct");
        }
        for name in collector.deps.templates {
            let source_id = definition_id("template", &name);
            self.ensure_node(
                source_id.clone(),
                "template",
                "template",
                &name,
                false,
                None,
                None,
            );
            self.add_edge(&source_id, target_id, "uses_template");
        }
    }

    fn add_theorem_edges(&mut self, target_id: &str, prove_process: &[Stmt]) {
        for name in by_thm_names_in_stmts(prove_process) {
            let source_id = definition_id("theorem", &name);
            self.ensure_node(
                source_id.clone(),
                "theorem",
                "theorem",
                &name,
                false,
                None,
                None,
            );
            self.add_edge(&source_id, target_id, "uses_theorem");
        }
    }

    fn ensure_node(
        &mut self,
        id: String,
        kind: &str,
        definition_kind: &str,
        name: &str,
        defined: bool,
        line_file: Option<&LineFile>,
        statement: Option<&str>,
    ) {
        if let Some(index) = self.node_index.get(&id).copied() {
            let node = &mut self.nodes[index];
            if defined {
                node.defined = true;
                node.definition_kind = definition_kind.to_string();
                node.line_file = line_file.cloned();
                node.statement = statement.map(str::to_string);
            }
            return;
        }
        self.node_index.insert(id.clone(), self.nodes.len());
        self.nodes.push(DefinitionGraphNode {
            id,
            kind: kind.to_string(),
            definition_kind: definition_kind.to_string(),
            name: name.to_string(),
            label: name.to_string(),
            defined,
            line_file: line_file.cloned(),
            statement: statement.map(str::to_string),
        });
    }

    fn add_edge(&mut self, from: &str, to: &str, kind: &str) {
        if from == to {
            return;
        }
        let key = format!("{}|{}|{}", from, to, kind);
        if let Some(index) = self.edge_index.get(&key).copied() {
            self.edges[index].count += 1;
            return;
        }
        self.edge_index.insert(key, self.edges.len());
        self.edges.push(DefinitionGraphEdge {
            from: from.to_string(),
            to: to.to_string(),
            kind: kind.to_string(),
            count: 1,
        });
    }

    fn nodes_json(&self, include_source: bool) -> JsonValue {
        JsonValue::Array(
            self.nodes
                .iter()
                .map(|node| node.json_value(include_source))
                .collect(),
        )
    }

    fn edges_json(&self) -> JsonValue {
        JsonValue::Array(
            self.edges
                .iter()
                .map(DefinitionGraphEdge::json_value)
                .collect(),
        )
    }

    fn summary_json(&self) -> JsonValue {
        let mut kinds = HashMap::<String, usize>::new();
        let mut defined_nodes = 0;
        for node in &self.nodes {
            if node.defined {
                defined_nodes += 1;
            }
            *kinds.entry(node.definition_kind.clone()).or_insert(0) += 1;
        }
        let mut fields = vec![
            ("nodes".to_string(), JsonValue::Number(self.nodes.len())),
            (
                "defined_nodes".to_string(),
                JsonValue::Number(defined_nodes),
            ),
            ("edges".to_string(), JsonValue::Number(self.edges.len())),
            (
                "edge_uses".to_string(),
                JsonValue::Number(self.edges.iter().map(|edge| edge.count).sum()),
            ),
        ];
        let mut kinds = kinds.into_iter().collect::<Vec<_>>();
        kinds.sort_by(|left, right| left.0.cmp(&right.0));
        for (kind, count) in kinds {
            fields.push((kind, JsonValue::Number(count)));
        }
        JsonValue::Object(fields)
    }

    fn empty_summary_json() -> JsonValue {
        JsonValue::Object(vec![
            ("nodes".to_string(), JsonValue::Number(0)),
            ("defined_nodes".to_string(), JsonValue::Number(0)),
            ("edges".to_string(), JsonValue::Number(0)),
            ("edge_uses".to_string(), JsonValue::Number(0)),
        ])
    }

    fn mermaid(&self) -> String {
        let mut output = String::from("flowchart LR\n");
        for node in &self.nodes {
            output.push_str(
                format!("    {}{}\n", mermaid_id(&node.id), mermaid_node_shape(node)).as_str(),
            );
        }
        for edge in &self.edges {
            output.push_str(
                format!(
                    "    {} -->|{}| {}\n",
                    mermaid_id(&edge.from),
                    edge.kind,
                    mermaid_id(&edge.to)
                )
                .as_str(),
            );
        }
        output.trim_end().to_string()
    }
}

impl DefinitionGraphNode {
    fn json_value(&self, include_source: bool) -> JsonValue {
        let mut fields = vec![
            ("id".to_string(), JsonValue::JsonString(self.id.clone())),
            ("kind".to_string(), JsonValue::JsonString(self.kind.clone())),
            (
                "definition_kind".to_string(),
                JsonValue::JsonString(self.definition_kind.clone()),
            ),
            ("name".to_string(), JsonValue::JsonString(self.name.clone())),
            (
                "label".to_string(),
                JsonValue::JsonString(self.label.clone()),
            ),
            ("defined".to_string(), JsonValue::Bool(self.defined)),
        ];
        if let Some(line_file) = self.line_file.as_ref() {
            fields.push(("line".to_string(), JsonValue::Number(line_file.0)));
        }
        if include_source {
            if let Some(statement) = self.statement.as_ref() {
                fields.push((
                    "statement".to_string(),
                    JsonValue::JsonString(statement.clone()),
                ));
            }
        }
        JsonValue::Object(fields)
    }
}

impl DefinitionGraphEdge {
    fn json_value(&self) -> JsonValue {
        JsonValue::Object(vec![
            ("from".to_string(), JsonValue::JsonString(self.from.clone())),
            ("to".to_string(), JsonValue::JsonString(self.to.clone())),
            ("kind".to_string(), JsonValue::JsonString(self.kind.clone())),
            ("count".to_string(), JsonValue::Number(self.count)),
        ])
    }
}

fn collect_template_definition_dependencies(
    collector: &mut DepCollector,
    definition: &TemplateDefEnum,
) {
    match definition {
        TemplateDefEnum::HaveObjInNonemptySetStmt(statement) => {
            collector.collect_param_def_with_type_deps(&statement.param_def);
            collector.add_param_def_with_type(&statement.param_def);
        }
        TemplateDefEnum::HaveObjEqualStmt(statement) => {
            collector.collect_param_def_with_type_deps(&statement.param_def);
            collector.add_param_def_with_type(&statement.param_def);
            for value in &statement.objs_equal_to {
                collector.collect_obj(value);
            }
        }
        TemplateDefEnum::HaveObjByExistFactsStmt(statement) => {
            collector.collect_param_def_with_type_deps(&statement.param_def);
            collector.add_param_def_with_type(&statement.param_def);
            for fact in &statement.facts {
                collector.collect_exist_body_fact(fact);
            }
        }
        TemplateDefEnum::TrustHaveStmt(statement) => {
            collector.collect_param_def_with_type_deps(&statement.param_def);
            collector.add_param_def_with_type(&statement.param_def);
            for fact in &statement.facts {
                collector.collect_fact(fact);
            }
        }
        TemplateDefEnum::HaveByExistStmt(statement) => {
            collector.collect_exist_fact(&statement.exist_fact_in_have_obj_st);
        }
        TemplateDefEnum::HaveFnEqualStmt(statement) => {
            collector.add_local_name(&statement.name);
            collector.collect_anonymous_fn(&statement.equal_to_anonymous_fn);
        }
        TemplateDefEnum::HaveFnEqualCaseByCaseStmt(statement) => {
            collector.add_local_name(&statement.name);
            collector.collect_fn_set_clause(&statement.fn_set_clause);
            for condition in &statement.cases {
                collector.collect_and_chain_atomic_fact(condition);
            }
            for value in &statement.equal_tos {
                collector.collect_obj(value);
            }
        }
        TemplateDefEnum::HaveFnByInducStmt(statement) => {
            collector.add_local_name(&statement.name);
            collector.collect_fn_set_clause(&statement.fn_set_clause);
            collector.collect_obj(&statement.measure);
            collector.collect_obj(&statement.lower_bound);
            for case in &statement.cases {
                collector.collect_have_fn_by_induc_case(case);
            }
        }
        TemplateDefEnum::HaveFnByForallExistUniqueStmt(statement) => {
            collector.add_local_name(&statement.fn_name);
            collector.collect_forall_fact(&statement.forall);
        }
        TemplateDefEnum::HaveTupleStmt(statement) => {
            collector.add_local_name(&statement.index_name);
            collector.collect_obj(&statement.dimension);
            collector.collect_obj(&statement.value);
        }
        TemplateDefEnum::HaveCartStmt(statement) => {
            collector.add_local_name(&statement.index_name);
            collector.collect_obj(&statement.dimension);
            collector.collect_obj(&statement.value);
        }
        TemplateDefEnum::HaveSeqStmt(statement) => {
            collector.add_local_name(&statement.index_name);
            collector.collect_obj(&statement.seq_set.clone().into());
            collector.collect_obj(&statement.value);
        }
        TemplateDefEnum::HaveFiniteSeqStmt(statement) => {
            collector.add_local_name(&statement.index_name);
            collector.collect_obj(&statement.finite_seq_set.clone().into());
            collector.collect_obj(&statement.bound);
            collector.collect_obj(&statement.value);
        }
        TemplateDefEnum::HaveMatrixStmt(statement) => {
            collector.add_local_name(&statement.row_index_name);
            collector.add_local_name(&statement.col_index_name);
            collector.collect_obj(&statement.matrix_set.clone().into());
            collector.collect_obj(&statement.row_bound);
            collector.collect_obj(&statement.col_bound);
            collector.collect_obj(&statement.value);
        }
    }
}

fn definition_id(kind: &str, name: &str) -> String {
    format!("definition:{}:{}", kind, name)
}

fn mermaid_id(id: &str) -> String {
    let mut out = String::from("n_");
    for ch in id.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    out
}

fn mermaid_node_shape(node: &DefinitionGraphNode) -> String {
    let label = node.label.replace('"', "'");
    match node.kind.as_str() {
        "prop" => format!("([\"{}\"])", label),
        "fn" => format!("{{\"{}\"}}", label),
        "theorem" => format!("[/\"{}\"/]", label),
        _ => format!("[\"{}\"]", label),
    }
}

#[cfg(test)]
mod tests {
    use super::run_definition_graph_for_code;

    fn definition_graph_output(source: &'static str) -> String {
        std::thread::Builder::new()
            .name("definition_graph_output_large_stack".to_string())
            .stack_size(64 * 1024 * 1024)
            .spawn(move || run_definition_graph_for_code(source, "definition_graph_test", true).1)
            .expect("spawn definition graph output test")
            .join()
            .expect("definition graph output test panicked")
    }

    #[test]
    fn definition_graph_reads_environment_stored_props_and_functions() {
        let output = definition_graph_output(
            "abstract_prop p(x)\nprop q(x R):\n    $p(x)\nhave fn f(x R: $q(x)) R = x\n",
        );

        assert!(output.contains(r#""graph": "litex-definition-graph""#));
        assert!(output.contains(r#""id": "definition:prop:p""#));
        assert!(output.contains(r#""id": "definition:prop:q""#));
        assert!(output.contains(r#""id": "definition:fn:f""#));
        assert!(output.contains(r#""kind": "uses_prop""#));
        assert!(output.contains(r#""line": 1"#));
    }
}
