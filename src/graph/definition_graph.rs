use super::graph::DepCollector;
use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;
use std::rc::Rc;

const DEFINITION_GRAPH_NAME: &str = "litex-definition-graph";
const DEFINITION_GRAPH_VERSION: &str = "0.2";

struct DefinitionGraphNode {
    id: String,
    kind: String,
    definition_kind: String,
    name: String,
    label: String,
    defined: bool,
    semantic_role: String,
    litex_form: String,
    knowledge_status: String,
    trust_kind: Option<String>,
    line_file: Option<LineFile>,
    statement: Option<String>,
}

#[derive(Clone)]
struct DefinitionGraphEdge {
    from: String,
    to: String,
    kind: String,
    reference_kind: String,
    count: usize,
}

struct DefinitionGraphBuilder {
    nodes: Vec<DefinitionGraphNode>,
    node_index: HashMap<String, usize>,
    edges: Vec<DefinitionGraphEdge>,
    edge_index: HashMap<String, usize>,
    active_canonical_name: Option<String>,
    canonical_name_by_source: HashMap<String, String>,
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

    let mut runtime = Runtime::new();
    runtime.detail_output = !hide_file_paths;
    runtime.strict_mode = strict_mode;
    let (stmt_results, runtime_error) = crate::pipeline::run_file_with_project_context(
        resolved_path.as_str(),
        &mut runtime,
        force_isolated,
    );
    let selected_target = if force_isolated {
        None
    } else {
        definition_graph_file_target(&runtime, resolved_path.as_str())
    };
    render_definition_graph_result(
        "file",
        resolved_path.as_str(),
        hide_file_paths,
        &mut runtime,
        stmt_results.as_slice(),
        runtime_error.as_ref(),
        selected_target,
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
    let mut runtime = Runtime::new();
    runtime.detail_output = !hide_file_paths;
    runtime.strict_mode = strict_mode;
    let target = match discover_repository(&mut runtime, repo_path) {
        Ok(target) => target,
        Err(error) => {
            return render_definition_graph_result(
                "repo",
                repo_path,
                hide_file_paths,
                &mut runtime,
                &[],
                Some(&error),
                None,
            );
        }
    };
    let (stmt_results, runtime_error) =
        crate::pipeline::run_repository_file_target(&mut runtime, target);
    render_definition_graph_result(
        "repo",
        repo_path,
        hide_file_paths,
        &mut runtime,
        stmt_results.as_slice(),
        runtime_error.as_ref(),
        Some(target),
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
    let mut runtime = Runtime::new();
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
        None,
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
        None,
    )
}

fn render_definition_graph_result(
    target_kind: &str,
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

fn definition_graph_file_target(
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

impl DefinitionGraphBuilder {
    fn new() -> Self {
        Self {
            nodes: vec![],
            node_index: HashMap::new(),
            edges: vec![],
            edge_index: HashMap::new(),
            active_canonical_name: None,
            canonical_name_by_source: HashMap::new(),
        }
    }

    fn from_runtime(
        runtime: &Runtime,
        selected_target: Option<RepositoryFileTarget>,
        stmt_results: &[StmtResult],
    ) -> Self {
        let mut builder = Self::new();
        match selected_target {
            Some(RepositoryFileTarget::File { module_id, file_id }) => {
                if let Some(file) = runtime
                    .module_manager
                    .module(module_id)
                    .and_then(|module| module.file(file_id))
                {
                    let node_ids = builder.add_environment(
                        file.environment.as_ref(),
                        Some(file.canonical_name.as_str()),
                        Some(file.source_path.as_str()),
                    );
                    builder.add_execution_source_for_nodes(
                        runtime,
                        file.execution_mode,
                        file.canonical_name.as_str(),
                        file.source_path.as_str(),
                        node_ids.as_slice(),
                    );
                }
            }
            Some(RepositoryFileTarget::Module(module_id)) => {
                builder.add_module_environments(runtime, module_id);
            }
            None => {
                if let Some(module_id) = runtime.module_manager.entry_module_id {
                    if let Some(module) = runtime.module_manager.module(module_id) {
                        let node_ids = builder.add_environment(
                            module.main_environment.as_ref(),
                            Some(module.module_name.as_str()),
                            Some(module.main_file_path.as_str()),
                        );
                        builder.add_execution_source_for_nodes(
                            runtime,
                            module.execution_mode,
                            module.module_name.as_str(),
                            module.main_file_path.as_str(),
                            node_ids.as_slice(),
                        );
                    }
                }
            }
        }
        builder.add_result_provenance(runtime, stmt_results);
        builder.propagate_knowledge_status();
        builder
    }

    fn add_module_environments(&mut self, runtime: &Runtime, target_module_id: ModuleId) {
        let mut module_ids = runtime
            .module_manager
            .modules
            .keys()
            .copied()
            .filter(|module_id| {
                definition_graph_module_is_descendant(runtime, *module_id, target_module_id)
            })
            .collect::<Vec<_>>();
        module_ids.sort_by_key(|module_id| module_id.0);
        for module_id in module_ids {
            let Some(module) = runtime.module_manager.module(module_id) else {
                continue;
            };
            let main_node_ids = self.add_environment(
                module.main_environment.as_ref(),
                Some(module.module_name.as_str()),
                Some(module.main_file_path.as_str()),
            );
            self.add_execution_source_for_nodes(
                runtime,
                module.execution_mode,
                module.module_name.as_str(),
                module.main_file_path.as_str(),
                main_node_ids.as_slice(),
            );
            for file in module.files.iter() {
                if file.status != FileStatus::Loaded {
                    continue;
                }
                let node_ids = self.add_environment(
                    file.environment.as_ref(),
                    Some(file.canonical_name.as_str()),
                    Some(file.source_path.as_str()),
                );
                self.add_execution_source_for_nodes(
                    runtime,
                    file.execution_mode,
                    file.canonical_name.as_str(),
                    file.source_path.as_str(),
                    node_ids.as_slice(),
                );
            }
        }
    }

    fn add_environment(
        &mut self,
        environment: &Environment,
        canonical_name: Option<&str>,
        source_path: Option<&str>,
    ) -> Vec<String> {
        let previous_canonical_name = self.active_canonical_name.clone();
        self.active_canonical_name = canonical_name
            .filter(|name| !name.is_empty())
            .map(str::to_string);
        if let (Some(canonical_name), Some(source_path)) =
            (self.active_canonical_name.as_ref(), source_path)
        {
            self.canonical_name_by_source
                .insert(source_path.to_string(), canonical_name.clone());
        }
        let defined_before = self
            .nodes
            .iter()
            .filter(|node| node.defined)
            .map(|node| node.id.clone())
            .collect::<HashSet<_>>();
        self.add_identifiers(environment);
        self.add_props(environment);
        self.add_functions(environment);
        self.add_algorithms(environment);
        self.add_structs(environment);
        self.add_templates(environment);
        self.add_theorems(environment);
        self.add_strategies(environment);
        let node_ids = self
            .nodes
            .iter()
            .filter(|node| node.defined && !defined_before.contains(&node.id))
            .map(|node| node.id.clone())
            .collect();
        self.active_canonical_name = previous_canonical_name;
        node_ids
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
            let mut signature = DepCollector::new();
            signature.collect_param_def_with_type_deps(&definition.params_def_with_type);
            self.add_dependency_edges(&node_id, signature, "signature");

            let mut definition_body = DepCollector::new();
            definition_body.add_param_def_with_type(&definition.params_def_with_type);
            for fact in &definition.iff_facts {
                definition_body.collect_fact(fact);
            }
            self.add_dependency_edges(&node_id, definition_body, "definition");
        }
    }

    fn add_functions(&mut self, environment: &Environment) {
        let mut functions = environment.known_objs_in_fn_sets.iter().collect::<Vec<_>>();
        functions.sort_by(|left, right| left.0.cmp(right.0));
        for (stored_name, definition) in functions {
            let name = self.normalized_dependency_name(stored_name);
            let node_id = definition_id("fn", name.as_str());
            let line_file = definition
                .equal_to
                .as_ref()
                .map(|(_, line_file)| line_file)
                .or_else(|| definition.fn_set.as_ref().map(|(_, line_file)| line_file));
            self.ensure_node(
                node_id.clone(),
                "fn",
                "function",
                name.as_str(),
                true,
                line_file,
                Some(&format!("have fn {}", name)),
            );
            let mut signature = DepCollector::new();
            signature.add_local_name(name.as_str());
            let mut well_definedness = DepCollector::new();
            well_definedness.add_local_name(name.as_str());
            if let Some((fn_set, _)) = definition.fn_set.as_ref() {
                signature.collect_param_def_with_set_deps(&fn_set.params_def_with_set);
                signature.add_param_def_with_set(&fn_set.params_def_with_set);
                signature.collect_obj(&fn_set.ret_set);

                well_definedness.add_param_def_with_set(&fn_set.params_def_with_set);
                for fact in fn_set.dom_facts.iter() {
                    well_definedness.collect_or_and_chain_atomic_fact(fact);
                }
            }
            self.add_dependency_edges(&node_id, signature, "signature");
            self.add_dependency_edges(&node_id, well_definedness, "well_definedness");

            let mut definition_body = DepCollector::new();
            definition_body.add_local_name(name.as_str());
            if let Some((equal_to, _)) = definition.equal_to.as_ref() {
                definition_body.collect_obj(equal_to);
            }
            self.add_dependency_edges(&node_id, definition_body, "definition");
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
            let mut definition_body = DepCollector::new();
            for parameter in &definition.params {
                definition_body.add_local_name(parameter);
            }
            for case in &definition.cases {
                definition_body.collect_atomic_fact(&case.condition);
                definition_body.collect_obj(&case.return_stmt.value);
            }
            if let Some(default_return) = definition.default_return.as_ref() {
                definition_body.collect_obj(&default_return.value);
            }
            self.add_dependency_edges(&node_id, definition_body, "definition");
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
            let mut signature = DepCollector::new();
            let mut well_definedness = DepCollector::new();
            if let Some((params, dom_facts)) = definition.param_def_with_dom.as_ref() {
                signature.collect_param_def_with_type_deps(params);
                signature.add_param_def_with_type(params);
                well_definedness.add_param_def_with_type(params);
                for fact in dom_facts {
                    well_definedness.collect_or_and_chain_atomic_fact(fact);
                }
            }
            for (_, field) in &definition.fields {
                signature.collect_obj(field);
            }
            self.add_dependency_edges(&node_id, signature, "signature");
            self.add_dependency_edges(&node_id, well_definedness, "well_definedness");

            let mut definition_body = DepCollector::new();
            if let Some((params, _)) = definition.param_def_with_dom.as_ref() {
                definition_body.add_param_def_with_type(params);
            }
            for fact in &definition.equivalent_facts {
                definition_body.collect_fact(fact);
            }
            self.add_dependency_edges(&node_id, definition_body, "definition");
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
            let mut signature = DepCollector::new();
            signature.collect_param_def_with_type_deps(&definition.template_arg_def);
            self.add_dependency_edges(&node_id, signature, "signature");

            let mut well_definedness = DepCollector::new();
            well_definedness.add_param_def_with_type(&definition.template_arg_def);
            for fact in &definition.template_arg_dom {
                well_definedness.collect_or_and_chain_atomic_fact(fact);
            }
            self.add_dependency_edges(&node_id, well_definedness, "well_definedness");

            let mut definition_body = DepCollector::new();
            definition_body.add_param_def_with_type(&definition.template_arg_def);
            collect_template_definition_dependencies(
                &mut definition_body,
                &definition.template_def_stmt,
            );
            self.add_dependency_edges(&node_id, definition_body, "definition");
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
            let mut signature = DepCollector::new();
            signature
                .collect_param_def_with_type_deps(&definition.forall_fact.params_def_with_type);
            signature.add_param_def_with_type(&definition.forall_fact.params_def_with_type);
            for fact in definition.forall_fact.then_facts.iter() {
                signature.collect_exist_or_and_chain_atomic_fact(fact);
            }
            self.add_dependency_edges(&node_id, signature, "signature");

            let mut well_definedness = DepCollector::new();
            well_definedness.add_param_def_with_type(&definition.forall_fact.params_def_with_type);
            for fact in definition.forall_fact.dom_facts.iter() {
                well_definedness.collect_fact(fact);
            }
            self.add_dependency_edges(&node_id, well_definedness, "well_definedness");

            if let Some(trust_summary) = environment.defined_thm_trust_summaries.get(name) {
                self.set_node_knowledge_status(&node_id, "trust", Some("indirect"));
                self.add_trust_summary_edges(&node_id, trust_summary);
            }
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
            let mut signature = DepCollector::new();
            signature
                .collect_param_def_with_type_deps(&definition.forall_fact.params_def_with_type);
            signature.add_param_def_with_type(&definition.forall_fact.params_def_with_type);
            for fact in definition.forall_fact.then_facts.iter() {
                signature.collect_exist_or_and_chain_atomic_fact(fact);
            }
            self.add_dependency_edges(&node_id, signature, "signature");

            let mut well_definedness = DepCollector::new();
            well_definedness.add_param_def_with_type(&definition.forall_fact.params_def_with_type);
            for fact in definition.forall_fact.dom_facts.iter() {
                well_definedness.collect_fact(fact);
            }
            self.add_dependency_edges(&node_id, well_definedness, "well_definedness");
        }
    }

    fn add_dependency_edges(
        &mut self,
        target_id: &str,
        collector: DepCollector,
        dependency_kind: &str,
    ) {
        for name in collector.deps.props {
            let name = self.normalized_dependency_name(name.as_str());
            let source_id = definition_id("prop", &name);
            self.ensure_node(source_id.clone(), "prop", "prop", &name, false, None, None);
            self.add_edge(&source_id, target_id, dependency_kind);
        }
        for name in collector.deps.fns {
            let name = self.normalized_dependency_name(name.as_str());
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
            self.add_edge(&source_id, target_id, dependency_kind);
        }
        for name in collector.deps.structs {
            let name = self.normalized_dependency_name(name.as_str());
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
            self.add_edge(&source_id, target_id, dependency_kind);
        }
        for name in collector.deps.templates {
            let name = self.normalized_dependency_name(name.as_str());
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
            self.add_edge(&source_id, target_id, dependency_kind);
        }
    }

    fn normalized_dependency_name(&self, name: &str) -> String {
        let Some(canonical_name) = self.active_canonical_name.as_ref() else {
            return name.to_string();
        };
        let local_prefix = format!("{}{}", canonical_name, MOD_SIGN);
        name.strip_prefix(local_prefix.as_str())
            .map(str::to_string)
            .unwrap_or_else(|| name.to_string())
    }

    fn add_execution_source_for_nodes(
        &mut self,
        runtime: &Runtime,
        execution_mode: ExecutionMode,
        canonical_name: &str,
        source_path: &str,
        node_ids: &[String],
    ) {
        if execution_mode == ExecutionMode::Verified || node_ids.is_empty() {
            return;
        }
        let unverified = runtime
            .unverified_imports
            .iter()
            .find(|entry| entry.name == canonical_name);
        let source_kind = unverified
            .map(|entry| entry.kind.as_str())
            .unwrap_or("trusted_execution");
        let line_file = unverified
            .map(|entry| entry.line_file.clone())
            .unwrap_or_else(|| (0, Rc::from(source_path)));
        let source_name = if canonical_name.is_empty() {
            source_path
        } else {
            canonical_name
        };
        let source_id = trust_source_id(source_kind, Some(source_name), &line_file);
        self.ensure_node(
            source_id.clone(),
            "source",
            "unverified_import",
            source_name,
            true,
            Some(&line_file),
            Some(&format!("{} {}", source_kind, source_name)),
        );
        for node_id in node_ids {
            self.set_node_knowledge_status(node_id, "trust", Some("direct"));
            self.add_edge(&source_id, node_id, "trust_source");
        }
    }

    fn add_result_provenance(&mut self, runtime: &Runtime, stmt_results: &[StmtResult]) {
        for result in stmt_results {
            self.add_one_result_provenance(runtime, result);
        }
    }

    fn add_one_result_provenance(&mut self, runtime: &Runtime, result: &StmtResult) {
        let Some(success) = result.non_factual_success() else {
            return;
        };
        match &success.stmt {
            Stmt::DefThmStmt(statement) => {
                let previous_canonical_name = self.active_canonical_name.clone();
                self.active_canonical_name = self
                    .canonical_name_by_source
                    .get(statement.line_file.1.as_ref())
                    .cloned();
                let sources = self.proof_source_ids_from_results(&success.inside_results);
                let direct_trust = stmt_results_contain_direct_trust(&success.inside_results);
                for name in statement.names.iter() {
                    let name = self.normalized_dependency_name(name);
                    let target_id = definition_id("theorem", name.as_str());
                    if !self.node_is_defined(&target_id) {
                        continue;
                    }
                    for source_id in sources.iter() {
                        self.add_edge(source_id, &target_id, "proof");
                    }
                    if direct_trust {
                        self.set_node_knowledge_status(&target_id, "trust", Some("direct"));
                    }
                    let summary = runtime
                        .proof_trust_summary_from_stmt_results(success.inside_results.as_slice());
                    self.add_trust_summary_edges(&target_id, &summary);
                }
                self.active_canonical_name = previous_canonical_name;
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnByForallExistUniqueStmt(statement)) => {
                self.add_selection_certificate(runtime, statement, success);
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(statement)) => {
                let source_id =
                    self.ensure_direct_trust_source("trust_have", None, &statement.line_file);
                for name in statement.param_def.collect_param_names() {
                    let target_id = definition_id("identifier", name.as_str());
                    if !self.node_is_defined(&target_id) {
                        continue;
                    }
                    self.set_node_knowledge_status(&target_id, "trust", Some("direct"));
                    self.add_edge(&source_id, &target_id, "trust_source");
                }
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(statement)) => {
                self.ensure_direct_trust_source("trust", None, &statement.line_file);
            }
            _ => {}
        }
    }

    fn add_selection_certificate(
        &mut self,
        runtime: &Runtime,
        statement: &HaveFnByForallExistUniqueStmt,
        success: &NonFactualStmtSuccess,
    ) {
        let function_id = definition_id("fn", &statement.fn_name);
        if !self.node_is_defined(&function_id) {
            return;
        }
        let certificate_id = selection_certificate_id(&statement.fn_name, &statement.line_file);
        self.ensure_node(
            certificate_id.clone(),
            "certificate",
            "selection_certificate",
            format!("{} exist!", statement.fn_name).as_str(),
            true,
            Some(&statement.line_file),
            Some(&statement.forall.to_string()),
        );
        self.set_node_source_if_default(
            &function_id,
            &statement.line_file,
            statement.to_string().as_str(),
        );
        self.inherit_selection_function_trust(&function_id, &certificate_id);
        self.set_node_semantic_role(&function_id, "canonical_selection");
        self.set_node_litex_form(&function_id, "have_fn_by_exist_unique");

        let previous_canonical_name = self.active_canonical_name.clone();
        self.active_canonical_name = self
            .canonical_name_by_source
            .get(statement.line_file.1.as_ref())
            .cloned();
        let mut signature = DepCollector::new();
        signature.collect_param_def_with_type_deps(&statement.forall.params_def_with_type);
        signature.add_param_def_with_type(&statement.forall.params_def_with_type);
        for fact in statement.forall.then_facts.iter() {
            signature.collect_exist_or_and_chain_atomic_fact(fact);
        }
        self.add_dependency_edges(&certificate_id, signature, "signature");

        let mut well_definedness = DepCollector::new();
        well_definedness.add_param_def_with_type(&statement.forall.params_def_with_type);
        for fact in statement.forall.dom_facts.iter() {
            well_definedness.collect_fact(fact);
        }
        self.add_dependency_edges(&certificate_id, well_definedness, "well_definedness");

        for source_id in self.proof_source_ids_from_results(&success.inside_results) {
            self.add_edge(&source_id, &certificate_id, "proof");
        }
        let direct_trust = stmt_results_contain_direct_trust(&success.inside_results);
        let summary = runtime.proof_trust_summary_from_stmt_results(&success.inside_results);
        if !summary.is_empty() {
            let trust_kind = if direct_trust { "direct" } else { "indirect" };
            self.set_node_knowledge_status(&certificate_id, "trust", Some(trust_kind));
            self.set_node_knowledge_status(&function_id, "trust", Some(trust_kind));
            self.add_trust_summary_edges(&certificate_id, &summary);
        }
        self.add_edge(&certificate_id, &function_id, "selection");
        self.active_canonical_name = previous_canonical_name;
    }

    fn inherit_selection_function_trust(&mut self, function_id: &str, certificate_id: &str) {
        let Some(function_index) = self.node_index.get(function_id).copied() else {
            return;
        };
        let function_status = self.nodes[function_index].knowledge_status.clone();
        let function_trust_kind = self.nodes[function_index].trust_kind.clone();
        if function_status == "trust" {
            self.set_node_knowledge_status(
                certificate_id,
                "trust",
                function_trust_kind.as_deref().or(Some("indirect")),
            );
        } else if function_status == "axiom" {
            self.set_node_knowledge_status(certificate_id, "trust", Some("indirect"));
        } else {
            return;
        }
        let source_ids = self
            .edges
            .iter()
            .filter(|edge| edge.to == function_id && edge.kind == "trust_source")
            .map(|edge| edge.from.clone())
            .collect::<Vec<_>>();
        for source_id in source_ids {
            self.add_edge(&source_id, certificate_id, "trust_source");
        }
    }

    fn proof_source_ids_from_results(&mut self, results: &[StmtResult]) -> Vec<String> {
        let mut source_ids = vec![];
        for result in results {
            self.collect_proof_source_ids_from_result(result, &mut source_ids);
        }
        source_ids.sort();
        source_ids.dedup();
        source_ids
    }

    fn collect_proof_source_ids_from_result(
        &mut self,
        result: &StmtResult,
        source_ids: &mut Vec<String>,
    ) {
        if let Some(success) = result.factual_success() {
            self.collect_verified_by_source_ids(&success.verified_by, source_ids);
            return;
        }
        let Some(success) = result.non_factual_success() else {
            return;
        };
        if let Some(ByVerificationResult::Theorem(verification)) = success.by_verification.as_ref()
        {
            let theorem_name = self.normalized_dependency_name(verification.theorem.as_str());
            let source_id = definition_id("theorem", theorem_name.as_str());
            self.ensure_node(
                source_id.clone(),
                "theorem",
                "theorem",
                theorem_name.as_str(),
                false,
                None,
                None,
            );
            source_ids.push(source_id);
        }
        match &success.stmt {
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(statement)) => {
                source_ids.push(self.ensure_direct_trust_source(
                    "trust",
                    None,
                    &statement.line_file,
                ));
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(statement)) => {
                source_ids.push(self.ensure_direct_trust_source(
                    "trust_have",
                    None,
                    &statement.line_file,
                ));
            }
            Stmt::DefThmStmt(statement) if statement.is_axiom() => {
                for name in statement.names.iter() {
                    let name = self.normalized_dependency_name(name);
                    let source_id = definition_id("theorem", name.as_str());
                    self.ensure_node(
                        source_id.clone(),
                        "theorem",
                        "axiom",
                        name.as_str(),
                        false,
                        Some(&statement.line_file),
                        Some(&statement.to_string()),
                    );
                    source_ids.push(source_id);
                }
            }
            _ => {}
        }
        for inside in success.inside_results.iter() {
            self.collect_proof_source_ids_from_result(inside, source_ids);
        }
    }

    fn collect_verified_by_source_ids(
        &mut self,
        verified_by: &VerifiedByResult,
        source_ids: &mut Vec<String>,
    ) {
        match verified_by {
            VerifiedByResult::BuiltinRule(result) => {
                for subgoal in result.subgoals.iter() {
                    self.collect_proof_source_ids_from_result(subgoal, source_ids);
                }
            }
            VerifiedByResult::Fact(result) => {
                self.collect_cited_stmt_source_ids(result.cite_what.as_ref(), source_ids);
            }
            VerifiedByResult::KnownForallInstantiation(result) => {
                self.collect_cited_stmt_source_ids(result.cite_what.as_ref(), source_ids);
                for requirement in result.requirements.iter() {
                    self.collect_proof_source_ids_from_result(
                        requirement.result.as_ref(),
                        source_ids,
                    );
                }
            }
            VerifiedByResult::VerifiedBys(result) => {
                for item in result.cite_what.iter() {
                    match item {
                        VerifiedBysEnum::ByBuiltinRule(result) => {
                            for subgoal in result.subgoals.iter() {
                                self.collect_proof_source_ids_from_result(subgoal, source_ids);
                            }
                        }
                        VerifiedBysEnum::ByFact(result) => self
                            .collect_cited_stmt_source_ids(result.cite_what.as_ref(), source_ids),
                        VerifiedBysEnum::ByKnownForall(result) => {
                            self.collect_cited_stmt_source_ids(
                                result.result.cite_what.as_ref(),
                                source_ids,
                            );
                            for requirement in result.result.requirements.iter() {
                                self.collect_proof_source_ids_from_result(
                                    requirement.result.as_ref(),
                                    source_ids,
                                );
                            }
                        }
                    }
                }
            }
            VerifiedByResult::ForallProof(result) => {
                for proved in result.proves.iter() {
                    self.collect_proof_source_ids_from_result(proved.result.as_ref(), source_ids);
                }
            }
        }
    }

    fn collect_cited_stmt_source_ids(&mut self, statement: &Stmt, source_ids: &mut Vec<String>) {
        match statement {
            Stmt::DefThmStmt(statement) => {
                for name in statement.names.iter() {
                    let name = self.normalized_dependency_name(name);
                    let source_id = definition_id("theorem", name.as_str());
                    self.ensure_node(
                        source_id.clone(),
                        "theorem",
                        if statement.is_axiom() {
                            "axiom"
                        } else {
                            "theorem"
                        },
                        name.as_str(),
                        false,
                        Some(&statement.line_file),
                        Some(&statement.to_string()),
                    );
                    source_ids.push(source_id);
                }
            }
            Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(statement)) => {
                let name = self.normalized_dependency_name(&statement.name);
                let source_id = definition_id("prop", &name);
                self.ensure_node(
                    source_id.clone(),
                    "prop",
                    "prop",
                    &name,
                    false,
                    Some(&statement.line_file),
                    Some(&statement.to_string()),
                );
                source_ids.push(source_id);
            }
            Stmt::DefPredicateStmt(DefPredicateStmt::DefAbstractPropStmt(statement)) => {
                let name = self.normalized_dependency_name(&statement.name);
                let source_id = definition_id("prop", &name);
                self.ensure_node(
                    source_id.clone(),
                    "prop",
                    "abstract_prop",
                    &name,
                    false,
                    Some(&statement.line_file),
                    Some(&statement.to_string()),
                );
                source_ids.push(source_id);
            }
            Stmt::Fact(fact) => {
                let line_file = fact.line_file();
                for node in self.nodes.iter() {
                    if node.defined && node.line_file.as_ref() == Some(&line_file) {
                        source_ids.push(node.id.clone());
                    }
                }
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(statement)) => {
                source_ids.push(self.ensure_direct_trust_source(
                    "trust",
                    None,
                    &statement.line_file,
                ));
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(statement)) => {
                source_ids.push(self.ensure_direct_trust_source(
                    "trust_have",
                    None,
                    &statement.line_file,
                ));
            }
            _ => {}
        }
    }

    fn add_trust_summary_edges(&mut self, target_id: &str, summary: &ProofTrustSummary) {
        for dependency in summary.dependencies.iter() {
            let source_id = if dependency.kind == "axiom" {
                if let Some(name) = dependency.name.as_ref() {
                    let name = self.normalized_dependency_name(name);
                    let source_id = definition_id("theorem", name.as_str());
                    self.ensure_node(
                        source_id.clone(),
                        "theorem",
                        "axiom",
                        name.as_str(),
                        false,
                        Some(&dependency.line_file),
                        None,
                    );
                    source_id
                } else {
                    self.ensure_direct_trust_source("axiom", None, &dependency.line_file)
                }
            } else {
                self.ensure_direct_trust_source(
                    dependency.kind.as_str(),
                    dependency.name.as_deref(),
                    &dependency.line_file,
                )
            };
            self.add_edge(&source_id, target_id, "trust_source");
        }
    }

    fn ensure_direct_trust_source(
        &mut self,
        kind: &str,
        name: Option<&str>,
        line_file: &LineFile,
    ) -> String {
        let source_id = trust_source_id(kind, name, line_file);
        let label = name
            .map(str::to_string)
            .unwrap_or_else(|| format!("{}@{}", kind, definition_line_label(line_file)));
        let definition_kind = if kind == "axiom" {
            "axiom_source"
        } else {
            "trust_source"
        };
        self.ensure_node(
            source_id.clone(),
            "source",
            definition_kind,
            label.as_str(),
            true,
            Some(line_file),
            Some(&format!("{} source", kind)),
        );
        source_id
    }

    fn node_is_defined(&self, node_id: &str) -> bool {
        self.node_index
            .get(node_id)
            .is_some_and(|index| self.nodes[*index].defined)
    }

    fn set_node_litex_form(&mut self, node_id: &str, litex_form: &str) {
        let Some(index) = self.node_index.get(node_id).copied() else {
            return;
        };
        self.nodes[index].litex_form = litex_form.to_string();
    }

    fn set_node_source_if_default(&mut self, node_id: &str, line_file: &LineFile, statement: &str) {
        let Some(index) = self.node_index.get(node_id).copied() else {
            return;
        };
        let node = &mut self.nodes[index];
        if node
            .line_file
            .as_ref()
            .map(|existing| existing.0 == 0)
            .unwrap_or(true)
        {
            node.line_file = Some(line_file.clone());
            node.statement = Some(statement.to_string());
        }
    }

    fn set_node_semantic_role(&mut self, node_id: &str, semantic_role: &str) {
        let Some(index) = self.node_index.get(node_id).copied() else {
            return;
        };
        self.nodes[index].semantic_role = semantic_role.to_string();
    }

    fn set_node_knowledge_status(
        &mut self,
        node_id: &str,
        knowledge_status: &str,
        trust_kind: Option<&str>,
    ) -> bool {
        let Some(index) = self.node_index.get(node_id).copied() else {
            return false;
        };
        let node = &mut self.nodes[index];
        if node.knowledge_status == "axiom" {
            return false;
        }
        if knowledge_status == "axiom" {
            let changed = node.knowledge_status != "axiom";
            node.knowledge_status = "axiom".to_string();
            node.trust_kind = Some("direct".to_string());
            return changed;
        }
        if knowledge_status != "trust" {
            return false;
        }
        let was_status = node.knowledge_status.clone();
        let was_kind = node.trust_kind.clone();
        node.knowledge_status = "trust".to_string();
        if trust_kind == Some("direct") || node.trust_kind.is_none() {
            node.trust_kind = trust_kind.map(str::to_string);
        }
        node.knowledge_status != was_status || node.trust_kind != was_kind
    }

    fn propagate_knowledge_status(&mut self) {
        loop {
            let mut changed = false;
            let mut inherited_edges = vec![];
            for edge in self.edges.clone() {
                let Some(source_index) = self.node_index.get(&edge.from).copied() else {
                    continue;
                };
                let source_status = self.nodes[source_index].knowledge_status.as_str();
                if source_status != "axiom" && source_status != "trust" {
                    continue;
                }
                if self.set_node_knowledge_status(&edge.to, "trust", Some("indirect")) {
                    changed = true;
                }
                if edge.kind != "trust_source" {
                    inherited_edges.push((edge.from.clone(), edge.to.clone()));
                }
            }
            for (from, to) in inherited_edges {
                self.add_edge(&from, &to, "trust_source");
            }
            if !changed {
                break;
            }
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
                node.semantic_role = definition_semantic_role(kind, definition_kind).to_string();
                node.litex_form = definition_litex_form(kind, definition_kind).to_string();
                let (knowledge_status, trust_kind) =
                    default_definition_knowledge_status(definition_kind);
                node.knowledge_status = knowledge_status.to_string();
                node.trust_kind = trust_kind.map(str::to_string);
                node.line_file = line_file.cloned();
                node.statement = statement.map(str::to_string);
            }
            return;
        }
        self.node_index.insert(id.clone(), self.nodes.len());
        let (knowledge_status, trust_kind) = default_definition_knowledge_status(definition_kind);
        self.nodes.push(DefinitionGraphNode {
            id,
            kind: kind.to_string(),
            definition_kind: definition_kind.to_string(),
            name: name.to_string(),
            label: name.to_string(),
            defined,
            semantic_role: definition_semantic_role(kind, definition_kind).to_string(),
            litex_form: definition_litex_form(kind, definition_kind).to_string(),
            knowledge_status: knowledge_status.to_string(),
            trust_kind: trust_kind.map(str::to_string),
            line_file: line_file.cloned(),
            statement: statement.map(str::to_string),
        });
    }

    fn add_edge(&mut self, from: &str, to: &str, kind: &str) {
        if from == to {
            return;
        }
        let reference_kind = self
            .node_index
            .get(from)
            .map(|index| self.nodes[*index].kind.clone())
            .unwrap_or_else(|| "unknown".to_string());
        let key = format!("{}|{}|{}|{}", from, to, kind, reference_kind);
        if let Some(index) = self.edge_index.get(&key).copied() {
            self.edges[index].count += 1;
            return;
        }
        self.edge_index.insert(key, self.edges.len());
        self.edges.push(DefinitionGraphEdge {
            from: from.to_string(),
            to: to.to_string(),
            kind: kind.to_string(),
            reference_kind,
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
        let mut edge_kinds = HashMap::<String, usize>::new();
        let mut knowledge_statuses = HashMap::<String, usize>::new();
        let mut defined_nodes = 0;
        for node in &self.nodes {
            if node.defined {
                defined_nodes += 1;
            }
            *kinds.entry(node.definition_kind.clone()).or_insert(0) += 1;
            *knowledge_statuses
                .entry(node.knowledge_status.clone())
                .or_insert(0) += 1;
        }
        for edge in &self.edges {
            *edge_kinds.entry(edge.kind.clone()).or_insert(0) += edge.count;
        }
        let edge_kind_counts = sorted_count_object(edge_kinds);
        let knowledge_status_counts = sorted_count_object(knowledge_statuses);
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
            ("is_dag".to_string(), JsonValue::Bool(self.is_dag())),
            (
                "topological_nodes".to_string(),
                JsonValue::Number(self.topological_order().len()),
            ),
            (
                "cycle_nodes".to_string(),
                JsonValue::Number(self.cycle_nodes().len()),
            ),
            ("edge_kinds".to_string(), edge_kind_counts),
            ("knowledge_statuses".to_string(), knowledge_status_counts),
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
            ("is_dag".to_string(), JsonValue::Bool(true)),
            ("topological_nodes".to_string(), JsonValue::Number(0)),
            ("cycle_nodes".to_string(), JsonValue::Number(0)),
            ("edge_kinds".to_string(), JsonValue::Object(vec![])),
            ("knowledge_statuses".to_string(), JsonValue::Object(vec![])),
        ])
    }

    fn is_dag(&self) -> bool {
        self.cycle_nodes().is_empty()
    }

    fn topological_order(&self) -> Vec<String> {
        let (order, _) = self.topology();
        order
    }

    fn cycle_nodes(&self) -> Vec<String> {
        let (_, cycle_nodes) = self.topology();
        cycle_nodes
    }

    fn topology(&self) -> (Vec<String>, Vec<String>) {
        let mut indegree = self
            .nodes
            .iter()
            .map(|node| (node.id.clone(), 0usize))
            .collect::<HashMap<_, _>>();
        let mut outgoing = HashMap::<String, Vec<String>>::new();
        for edge in self.edges.iter() {
            if !indegree.contains_key(&edge.from) || !indegree.contains_key(&edge.to) {
                continue;
            }
            *indegree.entry(edge.to.clone()).or_insert(0) += 1;
            outgoing
                .entry(edge.from.clone())
                .or_default()
                .push(edge.to.clone());
        }
        let mut ready = indegree
            .iter()
            .filter(|(_, degree)| **degree == 0)
            .map(|(node_id, _)| node_id.clone())
            .collect::<Vec<_>>();
        ready.sort();
        let mut order = vec![];
        while !ready.is_empty() {
            let node_id = ready.remove(0);
            order.push(node_id.clone());
            let mut next_nodes = outgoing.get(&node_id).cloned().unwrap_or_default();
            next_nodes.sort();
            for next in next_nodes {
                let Some(degree) = indegree.get_mut(&next) else {
                    continue;
                };
                *degree -= 1;
                if *degree == 0 {
                    ready.push(next);
                    ready.sort();
                }
            }
        }
        let unresolved_nodes = indegree
            .into_iter()
            .filter(|(node_id, degree)| *degree > 0 && !order.contains(node_id))
            .map(|(node_id, _)| node_id)
            .collect::<Vec<_>>();
        let unresolved = unresolved_nodes.iter().cloned().collect::<HashSet<_>>();
        let mut cycle_nodes = unresolved_nodes
            .into_iter()
            .filter(|node_id| node_is_in_cycle(node_id, &outgoing, &unresolved))
            .collect::<Vec<_>>();
        cycle_nodes.sort();
        (order, cycle_nodes)
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
            (
                "semantic_role".to_string(),
                JsonValue::JsonString(self.semantic_role.clone()),
            ),
            (
                "litex_form".to_string(),
                JsonValue::JsonString(self.litex_form.clone()),
            ),
            (
                "knowledge_status".to_string(),
                JsonValue::JsonString(self.knowledge_status.clone()),
            ),
            (
                "trust_kind".to_string(),
                self.trust_kind
                    .as_ref()
                    .map(|kind| JsonValue::JsonString(kind.clone()))
                    .unwrap_or(JsonValue::Null),
            ),
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
            (
                "referenced_kind".to_string(),
                JsonValue::JsonString(self.reference_kind.clone()),
            ),
            (
                "reference_kind".to_string(),
                JsonValue::JsonString(self.reference_kind.clone()),
            ),
            ("count".to_string(), JsonValue::Number(self.count)),
        ])
    }
}

fn definition_graph_module_is_descendant(
    runtime: &Runtime,
    module_id: ModuleId,
    ancestor_module_id: ModuleId,
) -> bool {
    let mut current = Some(module_id);
    while let Some(current_module_id) = current {
        if current_module_id == ancestor_module_id {
            return true;
        }
        current = runtime
            .module_manager
            .module(current_module_id)
            .and_then(|module| module.parent_module_id);
    }
    false
}

fn definition_semantic_role(kind: &str, definition_kind: &str) -> &'static str {
    match kind {
        "identifier" => "object",
        "prop" => "property",
        "fn" | "algorithm" => "function",
        "struct" => "structure",
        "template" => "parameterized_declaration",
        "theorem" | "certificate" => "fact",
        "strategy" => "proof_rule",
        "source" => "external_source",
        _ if definition_kind == "selection_certificate" => "fact",
        _ => "unknown",
    }
}

fn definition_litex_form(kind: &str, definition_kind: &str) -> &'static str {
    match definition_kind {
        "abstract_prop" => "abstract_prop",
        "axiom" => "axiom",
        "selection_certificate" => "exist_unique_certificate",
        "axiom_source" => "axiom",
        "trust_source" => "trust",
        "unverified_import" => "import",
        _ => match kind {
            "identifier" => "have",
            "prop" => "prop",
            "fn" => "have_fn",
            "algorithm" => "have_algo",
            "struct" => "struct",
            "template" => "template",
            "theorem" => "thm",
            "strategy" => "strategy",
            "certificate" => "exist_unique_certificate",
            "source" => "trust",
            _ => "unknown",
        },
    }
}

fn default_definition_knowledge_status(
    definition_kind: &str,
) -> (&'static str, Option<&'static str>) {
    match definition_kind {
        "axiom" | "axiom_source" => ("axiom", Some("direct")),
        "trust_source" | "unverified_import" => ("trust", Some("direct")),
        _ => ("checked", None),
    }
}

fn stmt_results_contain_direct_trust(results: &[StmtResult]) -> bool {
    for result in results {
        let Some(success) = result.non_factual_success() else {
            continue;
        };
        if matches!(
            &success.stmt,
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(_))
                | Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(_))
        ) {
            return true;
        }
        if stmt_results_contain_direct_trust(&success.inside_results) {
            return true;
        }
    }
    false
}

fn trust_source_id(kind: &str, name: Option<&str>, line_file: &LineFile) -> String {
    format!(
        "source:{}:{}:{}",
        kind,
        name.unwrap_or("anonymous"),
        definition_line_key(line_file)
    )
}

fn selection_certificate_id(function_name: &str, line_file: &LineFile) -> String {
    format!(
        "certificate:exist_unique:{}:{}",
        function_name,
        definition_line_key(line_file)
    )
}

fn definition_line_key(line_file: &LineFile) -> String {
    let path = Path::new(line_file.1.as_ref());
    let mut source_label = None;
    let mut ancestor = path.parent();
    while let Some(directory) = ancestor {
        if directory.join("litex.config").is_file() {
            source_label = path
                .strip_prefix(directory)
                .ok()
                .map(|relative| relative.to_string_lossy().into_owned());
            break;
        }
        ancestor = directory.parent();
    }
    let source_label = source_label
        .or_else(|| {
            path.file_name()
                .map(|name| name.to_string_lossy().into_owned())
        })
        .unwrap_or_else(|| "source".to_string());
    format!("{}:{}", source_label, line_file.0)
}

fn definition_line_label(line_file: &LineFile) -> String {
    if *line_file == default_line_file() {
        "unknown".to_string()
    } else {
        line_file.0.to_string()
    }
}

fn sorted_count_object(counts: HashMap<String, usize>) -> JsonValue {
    let mut entries = counts.into_iter().collect::<Vec<_>>();
    entries.sort_by(|left, right| left.0.cmp(&right.0));
    JsonValue::Object(
        entries
            .into_iter()
            .map(|(kind, count)| (kind, JsonValue::Number(count)))
            .collect(),
    )
}

fn node_is_in_cycle(
    start: &str,
    outgoing: &HashMap<String, Vec<String>>,
    unresolved: &HashSet<String>,
) -> bool {
    let mut stack = outgoing.get(start).cloned().unwrap_or_default();
    let mut visited = HashSet::new();
    while let Some(node_id) = stack.pop() {
        if node_id == start {
            return true;
        }
        if !unresolved.contains(&node_id) || !visited.insert(node_id.clone()) {
            continue;
        }
        if let Some(next_nodes) = outgoing.get(&node_id) {
            stack.extend(next_nodes.iter().cloned());
        }
    }
    false
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
    use super::{
        run_definition_graph_for_code, run_definition_graph_for_file,
        run_definition_graph_for_file_with_strict, DefinitionGraphBuilder,
    };
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::sync::atomic::{AtomicUsize, Ordering};

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
        assert!(output.contains(r#""graph_version": "0.2""#));
        assert!(output.contains(r#""kind": "definition""#));
        assert!(output.contains(r#""kind": "well_definedness""#));
        assert!(output.contains(r#""referenced_kind": "prop""#));
        assert!(output.contains(r#""semantic_role": "property""#));
        assert!(output.contains(r#""knowledge_status": "checked""#));
        assert!(output.contains(r#""is_dag": true"#));
        assert!(output.contains(r#""line": 1"#));
    }

    #[test]
    fn definition_graph_records_selection_certificate_and_actual_trust_source() {
        let output = definition_graph_output(
            "abstract_prop F(x, y)\nhave A set\nhave B set\nhave fn f by exist!:\n    ? forall x A:\n        exist! y B st {$F(x, y)}\n    trust exist! y B st {$F(x, y)}\n",
        );

        assert!(output.contains("certificate:exist_unique:f"), "{output}");
        assert!(output.contains(r#""kind": "selection""#), "{output}");
        assert!(output.contains(r#""kind": "proof""#), "{output}");
        assert!(output.contains(r#""kind": "trust_source""#), "{output}");
        assert!(
            output.contains(r#""litex_form": "have_fn_by_exist_unique""#),
            "{output}"
        );
        assert!(
            output.contains(r#""semantic_role": "canonical_selection""#),
            "{output}"
        );
        assert!(output.contains(r#""trust_kind": "direct""#), "{output}");
    }

    #[test]
    fn definition_graph_proof_edges_follow_actual_by_theorem_results() {
        let output = definition_graph_output(
            "abstract_prop P(x)\naxiom base_p:\n    ? forall x R:\n        $P(x)\nthm derived_p:\n    ? forall x R:\n        $P(x)\n    by thm base_p(x)\n",
        );

        assert!(
            output.contains(
                r#""from": "definition:theorem:base_p",
      "to": "definition:theorem:derived_p",
      "kind": "proof""#
            ),
            "{output}"
        );
        assert!(
            output.contains(r#""knowledge_status": "axiom""#),
            "{output}"
        );
        assert!(output.contains(r#""trust_kind": "indirect""#), "{output}");
    }

    #[test]
    fn definition_graph_file_uses_selected_export_environment() {
        let fixture = DefinitionGraphFixture::new("selected-export");
        write_file(
            &fixture.path("litex.config"),
            "[hierarchy]\nmodule\n\n[export]\nfirst = \"./first.lit\"\ntarget = \"./target.lit\"\n",
        );
        write_file(
            &fixture.path("first.lit"),
            "prop first_prop(x R):\n    x = x\n",
        );
        let target = fixture.path("target.lit");
        write_file(
            &target,
            "prop local_prop(x R):\n    x = x\n\nprop target_prop(x R):\n    $local_prop(x)\n    $first::first_prop(x)\n\nabstract_prop Choice(x, y)\nhave A set\nhave B set\nhave fn selected by exist!:\n    ? forall x A:\n        exist! y B st {$Choice(x, y)}\n",
        );
        let hidden_root = fixture
            .root
            .to_str()
            .expect("fixture root is UTF-8")
            .to_string();
        let target_string = target.to_str().expect("fixture path is UTF-8").to_string();
        let output = std::thread::Builder::new()
            .name("definition_graph_selected_export".to_string())
            .stack_size(64 * 1024 * 1024)
            .spawn(move || run_definition_graph_for_file(target_string.as_str(), true).1)
            .expect("spawn selected export definition graph test")
            .join()
            .expect("selected export definition graph test panicked");

        assert!(output.contains("definition:prop:target_prop"), "{output}");
        assert!(
            output.contains(
                r#""from": "definition:prop:local_prop",
      "to": "definition:prop:target_prop",
      "kind": "definition""#
            ),
            "{output}"
        );
        assert!(
            !output.contains("definition:prop:target::local_prop"),
            "{output}"
        );
        assert!(
            output.contains("definition:prop:first::first_prop"),
            "{output}"
        );
        assert!(
            output.contains(r#""definition_kind": "unverified_import""#),
            "{output}"
        );
        let certificate_id = r#""id": "certificate:exist_unique:selected:"#;
        let certificate_index = output
            .find(certificate_id)
            .expect("selection certificate node");
        let certificate_end = (certificate_index + 900).min(output.len());
        let certificate_window = &output[certificate_index..certificate_end];
        assert!(
            certificate_window.contains(r#""knowledge_status": "trust""#),
            "{certificate_window}"
        );
        assert!(
            certificate_window.contains(r#""trust_kind": "direct""#),
            "{certificate_window}"
        );
        assert!(
            output.contains(r#""to": "certificate:exist_unique:selected:target.lit:"#),
            "{output}"
        );
        let function_index = output
            .find(r#""id": "definition:fn:selected""#)
            .expect("selected function node");
        let function_end = (function_index + 900).min(output.len());
        let function_window = &output[function_index..function_end];
        assert!(
            function_window.contains(r#""line": 11"#),
            "{function_window}"
        );
        assert!(!output.contains(hidden_root.as_str()), "{output}");
    }

    #[test]
    fn definition_graph_project_proof_sources_normalize_local_qualifier() {
        let fixture = DefinitionGraphFixture::new("local-proof-source");
        write_file(
            &fixture.path("litex.config"),
            "[hierarchy]\nmodule\n\n[export]\ntarget = \"./target.lit\"\n",
        );
        let target = fixture.path("target.lit");
        write_file(
            &target,
            "thm local_base:\n    ? forall x R:\n        x = x\nthm local_derived:\n    ? forall x R:\n        x = x\n    by thm local_base(x)\n",
        );
        let target_string = target.to_str().expect("fixture path is UTF-8").to_string();
        let output = std::thread::Builder::new()
            .name("definition_graph_local_proof_source".to_string())
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                run_definition_graph_for_file_with_strict(target_string.as_str(), true, true).1
            })
            .expect("spawn local proof-source definition graph test")
            .join()
            .expect("local proof-source definition graph test panicked");

        assert!(
            output.contains(
                r#""from": "definition:theorem:local_base",
      "to": "definition:theorem:local_derived",
      "kind": "proof""#
            ),
            "{output}"
        );
        assert!(
            !output.contains("definition:theorem:target::local_base"),
            "{output}"
        );
        assert!(
            !output.contains("definition:theorem:target::local_derived"),
            "{output}"
        );
    }

    #[test]
    fn definition_graph_cycle_nodes_exclude_downstream_nodes() {
        let mut graph = DefinitionGraphBuilder::new();
        for name in ["a", "b", "downstream"] {
            graph.ensure_node(name.to_string(), "prop", "prop", name, true, None, None);
        }
        graph.add_edge("a", "b", "definition");
        graph.add_edge("b", "a", "definition");
        graph.add_edge("b", "downstream", "definition");

        assert_eq!(graph.cycle_nodes(), vec!["a".to_string(), "b".to_string()]);
        assert!(!graph.is_dag());
    }

    fn write_file(path: &Path, source: &str) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("create definition graph fixture directory");
        }
        fs::write(path, source).expect("write definition graph fixture file");
    }

    struct DefinitionGraphFixture {
        root: PathBuf,
    }

    impl DefinitionGraphFixture {
        fn new(name: &str) -> Self {
            static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
            let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
            let root = std::env::temp_dir().join(format!(
                "litex-definition-graph-{name}-{}-{id}",
                std::process::id()
            ));
            if root.exists() {
                fs::remove_dir_all(&root).expect("remove stale definition graph fixture");
            }
            fs::create_dir_all(&root).expect("create definition graph fixture root");
            Self { root }
        }

        fn path(&self, name: &str) -> PathBuf {
            self.root.join(name)
        }
    }
}
