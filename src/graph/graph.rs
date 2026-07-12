use crate::prelude::*;
use std::collections::{HashMap, HashSet};

const GRAPH_NAME: &str = "litex-relation-graph";
const GRAPH_VERSION: &str = "0.1";

#[derive(Clone)]
struct GraphNode {
    id: String,
    kind: String,
    name: String,
    label: String,
    defined: bool,
    fact_kind: Option<String>,
    line_file: Option<LineFile>,
    statement: Option<String>,
}

struct GraphEdge {
    from: String,
    to: String,
    kind: String,
    count: usize,
}

#[derive(Default)]
struct DepSet {
    props: Vec<String>,
    fns: Vec<String>,
}

struct DepCollector {
    deps: DepSet,
    local_names: HashSet<String>,
}

struct GraphBuilder {
    nodes: Vec<GraphNode>,
    node_index: HashMap<String, usize>,
    edges: Vec<GraphEdge>,
    edge_index: HashMap<String, usize>,
}

pub fn run_graph_for_code(code: &str, label: &str, hide_file_paths: bool) -> (bool, String) {
    run_graph_for_code_with_language(code, label, hide_file_paths, OutputLanguage::English)
}

pub fn run_graph_for_code_with_language(
    code: &str,
    label: &str,
    hide_file_paths: bool,
    _output_language: OutputLanguage,
) -> (bool, String) {
    run_graph_on_source("code", label, code, hide_file_paths, false)
}

pub fn run_graph_for_code_strict(code: &str, label: &str, hide_file_paths: bool) -> (bool, String) {
    run_graph_for_code_strict_with_language(code, label, hide_file_paths, OutputLanguage::English)
}

pub fn run_graph_for_code_strict_with_language(
    code: &str,
    label: &str,
    hide_file_paths: bool,
    _output_language: OutputLanguage,
) -> (bool, String) {
    run_graph_on_source("code", label, code, hide_file_paths, true)
}

pub fn run_graph_for_file(file_path: &str, hide_file_paths: bool) -> (bool, String) {
    run_graph_for_file_with_strict(file_path, hide_file_paths, false)
}

pub fn run_graph_for_file_with_strict(
    file_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_graph_for_file_with_strict_and_language(
        file_path,
        hide_file_paths,
        strict_mode,
        OutputLanguage::English,
    )
}

pub fn run_graph_for_file_with_strict_and_language(
    file_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
) -> (bool, String) {
    run_graph_for_file_with_strict_language_and_isolation(
        file_path,
        hide_file_paths,
        strict_mode,
        output_language,
        false,
    )
}

pub fn run_graph_for_file_with_strict_language_and_isolation(
    file_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
    _output_language: OutputLanguage,
    force_isolated: bool,
) -> (bool, String) {
    let resolved_path = match resolve_litex_file_path(file_path) {
        Ok(path) => path,
        Err(message) => {
            return graph_target_error_output("file", file_path, hide_file_paths, message);
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
    render_graph_result(
        "file",
        resolved_path.as_str(),
        hide_file_paths,
        runtime,
        stmt_results,
        runtime_error,
    )
}

pub fn run_graph_for_repo(repo_path: &str, hide_file_paths: bool) -> (bool, String) {
    run_graph_for_repo_with_strict(repo_path, hide_file_paths, false)
}

pub fn run_graph_for_repo_with_strict(
    repo_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_graph_for_repo_with_strict_and_language(
        repo_path,
        hide_file_paths,
        strict_mode,
        OutputLanguage::English,
    )
}

pub fn run_graph_for_repo_with_strict_and_language(
    repo_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
    _output_language: OutputLanguage,
) -> (bool, String) {
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.detail_output = !hide_file_paths;
    runtime.strict_mode = strict_mode;
    match discover_repository(&mut runtime, repo_path) {
        Ok(path) => path,
        Err(error) => {
            return render_graph_result(
                "repo",
                repo_path,
                hide_file_paths,
                runtime,
                vec![],
                Some(error),
            );
        }
    };
    let entry_module_id = runtime.current_module_id();
    let (stmt_results, runtime_error) = crate::pipeline::run_repository_file_target(
        &mut runtime,
        RepositoryFileTarget::Entrance(entry_module_id),
    );
    render_graph_result(
        "repo",
        repo_path,
        hide_file_paths,
        runtime,
        stmt_results,
        runtime_error,
    )
}

fn run_graph_on_source(
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
    render_graph_result(
        target_kind,
        target_label,
        hide_file_paths,
        runtime,
        stmt_results,
        runtime_error,
    )
}

fn render_graph_result(
    target_kind: &str,
    target_label: &str,
    hide_file_paths: bool,
    runtime: Runtime,
    stmt_results: Vec<StmtResult>,
    runtime_error: Option<RuntimeError>,
) -> (bool, String) {
    let ok = runtime_error.is_none();
    let graph = GraphBuilder::from_stmt_results(&stmt_results);
    let mut fields = vec![
        (
            "graph".to_string(),
            JsonValue::JsonString(GRAPH_NAME.to_string()),
        ),
        (
            "graph_version".to_string(),
            JsonValue::JsonString(GRAPH_VERSION.to_string()),
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
            target_json_value(target_kind, target_label, hide_file_paths),
        ),
    ];
    if let Some(error) = runtime_error.as_ref() {
        fields.push((
            "error".to_string(),
            JsonValue::JsonString(display_runtime_error_json(&runtime, error, true)),
        ));
    } else {
        fields.push(("error".to_string(), JsonValue::Null));
    }
    fields.push(("summary".to_string(), graph.summary_json()));
    fields.push(("nodes".to_string(), graph.nodes_json(!hide_file_paths)));
    fields.push(("edges".to_string(), graph.edges_json()));
    fields.push(("usage".to_string(), graph.usage_json()));
    fields.push((
        "mermaid".to_string(),
        JsonValue::JsonString(graph.mermaid()),
    ));

    (ok, render_json_value(&JsonValue::Object(fields), 0))
}

fn graph_target_error_output(
    target_kind: &str,
    target_label: &str,
    hide_file_paths: bool,
    message: String,
) -> (bool, String) {
    let output = JsonValue::Object(vec![
        (
            "graph".to_string(),
            JsonValue::JsonString(GRAPH_NAME.to_string()),
        ),
        (
            "graph_version".to_string(),
            JsonValue::JsonString(GRAPH_VERSION.to_string()),
        ),
        (
            "result".to_string(),
            JsonValue::JsonString("error".to_string()),
        ),
        ("ok".to_string(), JsonValue::Bool(false)),
        ("partial".to_string(), JsonValue::Bool(false)),
        (
            "target".to_string(),
            target_json_value(target_kind, target_label, hide_file_paths),
        ),
        ("error".to_string(), JsonValue::JsonString(message)),
        ("summary".to_string(), GraphBuilder::empty_summary_json()),
        ("nodes".to_string(), JsonValue::Array(vec![])),
        ("edges".to_string(), JsonValue::Array(vec![])),
        ("usage".to_string(), JsonValue::Array(vec![])),
        (
            "mermaid".to_string(),
            JsonValue::JsonString("flowchart LR".to_string()),
        ),
    ]);
    (false, render_json_value(&output, 0))
}

fn target_json_value(target_kind: &str, target_label: &str, hide_file_paths: bool) -> JsonValue {
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

impl GraphBuilder {
    fn new() -> Self {
        Self {
            nodes: Vec::new(),
            node_index: HashMap::new(),
            edges: Vec::new(),
            edge_index: HashMap::new(),
        }
    }

    fn from_stmt_results(stmt_results: &[StmtResult]) -> Self {
        let mut builder = Self::new();
        for result in stmt_results.iter() {
            if let Some(success) = result.non_factual_success() {
                builder.add_stmt(&success.stmt);
            } else if let Some(success) = result.factual_success() {
                builder.add_standalone_fact(&success.stmt);
            }
        }
        builder
    }

    fn add_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::DefPredicateStmt(DefPredicateStmt::DefAbstractPropStmt(s)) => {
                let node_id = prop_id(&s.name);
                self.ensure_node(
                    node_id,
                    "prop",
                    &s.name,
                    true,
                    None,
                    Some(&s.line_file),
                    Some(&stmt.to_string()),
                );
            }
            Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(s)) => {
                let node_id = prop_id(&s.name);
                self.ensure_node(
                    node_id.clone(),
                    "prop",
                    &s.name,
                    true,
                    None,
                    Some(&s.line_file),
                    Some(&stmt.to_string()),
                );
                let mut collector = DepCollector::new();
                collector.add_param_def_with_type(&s.params_def_with_type);
                collector.collect_param_def_with_type_deps(&s.params_def_with_type);
                for fact in s.iff_facts.iter() {
                    collector.collect_fact(fact);
                }
                self.add_dependency_edges(&node_id, &collector.deps);
            }
            Stmt::DefObjStmt(def_obj_stmt) => self.add_def_obj_stmt(def_obj_stmt, stmt),
            Stmt::DefThmStmt(s) => self.add_def_thm_stmt(s, stmt),
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(s)) => self.add_claim_stmt(s, stmt),
            _ => {}
        }
    }

    fn add_standalone_fact(&mut self, fact: &Fact) {
        let name = format!("fact@{}", line_label(&fact.line_file()));
        let node_id = fact_id("fact", &name);
        self.ensure_node(
            node_id.clone(),
            "fact",
            &name,
            true,
            Some("fact"),
            Some(&fact.line_file()),
            Some(&fact.to_string()),
        );
        let mut collector = DepCollector::new();
        collector.collect_fact(fact);
        self.add_dependency_edges(&node_id, &collector.deps);
    }

    fn add_def_obj_stmt(&mut self, stmt: &DefObjStmt, full_stmt: &Stmt) {
        match stmt {
            DefObjStmt::HaveFnEqualStmt(s) => {
                let node_id = self.add_fn_node(&s.name, &s.line_file, full_stmt);
                let mut collector = DepCollector::new();
                collector.add_local_name(&s.name);
                collector.collect_anonymous_fn(&s.equal_to_anonymous_fn);
                self.add_dependency_edges(&node_id, &collector.deps);
            }
            DefObjStmt::HaveFnEqualCaseByCaseStmt(s) => {
                let node_id = self.add_fn_node(&s.name, &s.line_file, full_stmt);
                let mut collector = DepCollector::new();
                collector.add_local_name(&s.name);
                collector.collect_fn_set_clause(&s.fn_set_clause);
                for case_fact in s.cases.iter() {
                    collector.collect_and_chain_atomic_fact(case_fact);
                }
                for obj in s.equal_tos.iter() {
                    collector.collect_obj(obj);
                }
                self.add_dependency_edges(&node_id, &collector.deps);
            }
            DefObjStmt::HaveFnByInducStmt(s) => {
                let node_id = self.add_fn_node(&s.name, &s.line_file, full_stmt);
                let mut collector = DepCollector::new();
                collector.add_local_name(&s.name);
                collector.collect_fn_set_clause(&s.fn_set_clause);
                collector.collect_obj(&s.measure);
                collector.collect_obj(&s.lower_bound);
                for case in s.cases.iter() {
                    collector.collect_have_fn_by_induc_case(case);
                }
                self.add_dependency_edges(&node_id, &collector.deps);
            }
            DefObjStmt::HaveFnByForallExistUniqueStmt(s) => {
                let node_id = self.add_fn_node(&s.fn_name, &s.line_file, full_stmt);
                let mut collector = DepCollector::new();
                collector.add_local_name(&s.fn_name);
                collector.collect_forall_fact(&s.forall);
                self.add_dependency_edges(&node_id, &collector.deps);
                for thm_name in by_thm_names_in_stmts(&s.prove_process) {
                    let fact_id = fact_id("thm", &thm_name);
                    self.ensure_node(
                        fact_id.clone(),
                        "fact",
                        &thm_name,
                        false,
                        Some("thm"),
                        None,
                        None,
                    );
                    self.add_edge(&fact_id, &node_id, "justified_by");
                }
            }
            _ => {}
        }
    }

    fn add_def_thm_stmt(&mut self, stmt: &DefThmStmt, full_stmt: &Stmt) {
        let fact_kind = if stmt.is_axiom() { "axiom" } else { "thm" };
        for name in stmt.names.iter() {
            let node_id = fact_id(fact_kind, name);
            self.ensure_node(
                node_id.clone(),
                "fact",
                name,
                true,
                Some(fact_kind),
                Some(&stmt.line_file),
                Some(&full_stmt.to_string()),
            );
            let mut collector = DepCollector::new();
            collector.collect_forall_fact(&stmt.forall_fact);
            self.add_dependency_edges(&node_id, &collector.deps);
            self.add_by_thm_edges_to(&node_id, &stmt.prove_process);
        }
    }

    fn add_claim_stmt(&mut self, stmt: &ClaimStmt, full_stmt: &Stmt) {
        let name = format!("claim@{}", line_label(&stmt.line_file));
        let node_id = fact_id("claim", &name);
        self.ensure_node(
            node_id.clone(),
            "fact",
            &name,
            true,
            Some("claim"),
            Some(&stmt.line_file),
            Some(&full_stmt.to_string()),
        );
        let mut collector = DepCollector::new();
        collector.collect_fact(&stmt.fact);
        self.add_dependency_edges(&node_id, &collector.deps);
        self.add_by_thm_edges_to(&node_id, &stmt.proof);
    }

    fn add_fn_node(&mut self, name: &str, line_file: &LineFile, stmt: &Stmt) -> String {
        let node_id = fn_id(name);
        self.ensure_node(
            node_id.clone(),
            "fn",
            name,
            true,
            None,
            Some(line_file),
            Some(&stmt.to_string()),
        );
        node_id
    }

    fn add_dependency_edges(&mut self, target_id: &str, deps: &DepSet) {
        for prop_name in deps.props.iter() {
            let source_id = prop_id(prop_name);
            self.ensure_node(
                source_id.clone(),
                "prop",
                prop_name,
                false,
                None,
                None,
                None,
            );
            self.add_edge(&source_id, target_id, "uses_prop");
        }
        for fn_name in deps.fns.iter() {
            let source_id = fn_id(fn_name);
            self.ensure_node(source_id.clone(), "fn", fn_name, false, None, None, None);
            self.add_edge(&source_id, target_id, "uses_fn");
        }
    }

    fn add_by_thm_edges_to(&mut self, target_id: &str, stmts: &[Stmt]) {
        for thm_name in by_thm_names_in_stmts(stmts) {
            let fact_id = fact_id("thm", &thm_name);
            self.ensure_node(
                fact_id.clone(),
                "fact",
                &thm_name,
                false,
                Some("thm"),
                None,
                None,
            );
            self.add_edge(&fact_id, target_id, "justified_by");
        }
    }

    fn ensure_node(
        &mut self,
        id: String,
        kind: &str,
        name: &str,
        defined: bool,
        fact_kind: Option<&str>,
        line_file: Option<&LineFile>,
        statement: Option<&str>,
    ) {
        if let Some(index) = self.node_index.get(&id).copied() {
            let node = &mut self.nodes[index];
            if defined {
                node.defined = true;
                node.line_file = line_file.cloned();
                node.statement = statement.map(|s| s.to_string());
                if let Some(fact_kind) = fact_kind {
                    node.fact_kind = Some(fact_kind.to_string());
                }
            }
            return;
        }
        self.node_index.insert(id.clone(), self.nodes.len());
        self.nodes.push(GraphNode {
            id,
            kind: kind.to_string(),
            name: name.to_string(),
            label: name.to_string(),
            defined,
            fact_kind: fact_kind.map(|s| s.to_string()),
            line_file: line_file.cloned(),
            statement: statement.map(|s| s.to_string()),
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
        self.edges.push(GraphEdge {
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
                .map(|node| node.json_value(include_source, self))
                .collect(),
        )
    }

    fn edges_json(&self) -> JsonValue {
        JsonValue::Array(self.edges.iter().map(GraphEdge::json_value).collect())
    }

    fn summary_json(&self) -> JsonValue {
        let mut defined_nodes = 0;
        let mut prop_nodes = 0;
        let mut defined_props = 0;
        let mut fn_nodes = 0;
        let mut defined_fns = 0;
        let mut fact_nodes = 0;
        let mut defined_facts = 0;
        let mut thm_nodes = 0;
        let mut axiom_nodes = 0;
        let mut claim_nodes = 0;

        for node in self.nodes.iter() {
            if node.defined {
                defined_nodes += 1;
            }
            match node.kind.as_str() {
                "prop" => {
                    prop_nodes += 1;
                    if node.defined {
                        defined_props += 1;
                    }
                }
                "fn" => {
                    fn_nodes += 1;
                    if node.defined {
                        defined_fns += 1;
                    }
                }
                "fact" => {
                    fact_nodes += 1;
                    if node.defined {
                        defined_facts += 1;
                    }
                    match node.fact_kind.as_deref() {
                        Some("thm") => thm_nodes += 1,
                        Some("axiom") => axiom_nodes += 1,
                        Some("claim") => claim_nodes += 1,
                        _ => {}
                    }
                }
                _ => {}
            }
        }

        JsonValue::Object(vec![
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
            ("props".to_string(), JsonValue::Number(prop_nodes)),
            (
                "defined_props".to_string(),
                JsonValue::Number(defined_props),
            ),
            ("functions".to_string(), JsonValue::Number(fn_nodes)),
            (
                "defined_functions".to_string(),
                JsonValue::Number(defined_fns),
            ),
            ("facts".to_string(), JsonValue::Number(fact_nodes)),
            (
                "defined_facts".to_string(),
                JsonValue::Number(defined_facts),
            ),
            ("theorems".to_string(), JsonValue::Number(thm_nodes)),
            ("axioms".to_string(), JsonValue::Number(axiom_nodes)),
            ("claims".to_string(), JsonValue::Number(claim_nodes)),
        ])
    }

    fn empty_summary_json() -> JsonValue {
        JsonValue::Object(vec![
            ("nodes".to_string(), JsonValue::Number(0)),
            ("defined_nodes".to_string(), JsonValue::Number(0)),
            ("edges".to_string(), JsonValue::Number(0)),
            ("edge_uses".to_string(), JsonValue::Number(0)),
            ("props".to_string(), JsonValue::Number(0)),
            ("defined_props".to_string(), JsonValue::Number(0)),
            ("functions".to_string(), JsonValue::Number(0)),
            ("defined_functions".to_string(), JsonValue::Number(0)),
            ("facts".to_string(), JsonValue::Number(0)),
            ("defined_facts".to_string(), JsonValue::Number(0)),
            ("theorems".to_string(), JsonValue::Number(0)),
            ("axioms".to_string(), JsonValue::Number(0)),
            ("claims".to_string(), JsonValue::Number(0)),
        ])
    }

    fn usage_json(&self) -> JsonValue {
        let mut items = self
            .nodes
            .iter()
            .map(|node| {
                (
                    self.outgoing_edge_use_count(&node.id),
                    self.incoming_edge_use_count(&node.id),
                    node.name.clone(),
                    node.usage_json_value(self),
                )
            })
            .collect::<Vec<_>>();
        items.sort_by(|left, right| {
            right
                .0
                .cmp(&left.0)
                .then_with(|| right.1.cmp(&left.1))
                .then_with(|| left.2.cmp(&right.2))
        });
        JsonValue::Array(items.into_iter().map(|(_, _, _, value)| value).collect())
    }

    fn incoming_edge_use_count(&self, node_id: &str) -> usize {
        self.edges
            .iter()
            .filter(|edge| edge.to == node_id)
            .map(|edge| edge.count)
            .sum()
    }

    fn outgoing_edge_use_count(&self, node_id: &str) -> usize {
        self.edges
            .iter()
            .filter(|edge| edge.from == node_id)
            .map(|edge| edge.count)
            .sum()
    }

    fn mermaid(&self) -> String {
        let mut lines = vec!["flowchart LR".to_string()];
        for node in self.nodes.iter() {
            lines.push(format!(
                "    {}{}",
                mermaid_id(&node.id),
                mermaid_node_shape(node)
            ));
        }
        for edge in self.edges.iter() {
            let arrow = if edge.kind == "justified_by" {
                "-.->"
            } else {
                "-->"
            };
            let label = if edge.count > 1 {
                format!("{} x{}", edge.kind, edge.count)
            } else {
                edge.kind.clone()
            };
            lines.push(format!(
                "    {} {}|{}| {}",
                mermaid_id(&edge.from),
                arrow,
                label,
                mermaid_id(&edge.to)
            ));
        }
        lines.join("\n")
    }
}

impl GraphNode {
    fn json_value(&self, include_source: bool, builder: &GraphBuilder) -> JsonValue {
        let mut fields = vec![
            ("id".to_string(), JsonValue::JsonString(self.id.clone())),
            ("kind".to_string(), JsonValue::JsonString(self.kind.clone())),
            ("name".to_string(), JsonValue::JsonString(self.name.clone())),
            (
                "label".to_string(),
                JsonValue::JsonString(self.label.clone()),
            ),
            ("defined".to_string(), JsonValue::Bool(self.defined)),
            (
                "uses_count".to_string(),
                JsonValue::Number(builder.incoming_edge_use_count(&self.id)),
            ),
            (
                "used_by_count".to_string(),
                JsonValue::Number(builder.outgoing_edge_use_count(&self.id)),
            ),
        ];
        if let Some(fact_kind) = self.fact_kind.as_ref() {
            fields.push((
                "fact_kind".to_string(),
                JsonValue::JsonString(fact_kind.clone()),
            ));
        }
        if let Some(line_file) = self.line_file.as_ref() {
            fields.push(("line".to_string(), line_json_value(line_file)));
            if include_source && !is_default_line_file(line_file) {
                fields.push((
                    "source".to_string(),
                    JsonValue::JsonString(line_file.1.as_ref().to_string()),
                ));
            }
        }
        if let Some(statement) = self.statement.as_ref() {
            fields.push((
                "statement".to_string(),
                JsonValue::JsonString(strip_free_param_numeric_tags_in_display(statement)),
            ));
        }
        JsonValue::Object(fields)
    }

    fn usage_json_value(&self, builder: &GraphBuilder) -> JsonValue {
        let mut fields = vec![
            ("id".to_string(), JsonValue::JsonString(self.id.clone())),
            ("kind".to_string(), JsonValue::JsonString(self.kind.clone())),
            ("name".to_string(), JsonValue::JsonString(self.name.clone())),
            ("defined".to_string(), JsonValue::Bool(self.defined)),
            (
                "uses_count".to_string(),
                JsonValue::Number(builder.incoming_edge_use_count(&self.id)),
            ),
            (
                "used_by_count".to_string(),
                JsonValue::Number(builder.outgoing_edge_use_count(&self.id)),
            ),
        ];
        if let Some(fact_kind) = self.fact_kind.as_ref() {
            fields.push((
                "fact_kind".to_string(),
                JsonValue::JsonString(fact_kind.clone()),
            ));
        }
        JsonValue::Object(fields)
    }
}

impl GraphEdge {
    fn json_value(&self) -> JsonValue {
        JsonValue::Object(vec![
            ("from".to_string(), JsonValue::JsonString(self.from.clone())),
            ("to".to_string(), JsonValue::JsonString(self.to.clone())),
            ("kind".to_string(), JsonValue::JsonString(self.kind.clone())),
            ("count".to_string(), JsonValue::Number(self.count)),
        ])
    }
}

impl DepSet {
    fn push_prop(&mut self, name: String) {
        if !self.props.contains(&name) {
            self.props.push(name);
        }
    }

    fn push_fn(&mut self, name: String) {
        if !self.fns.contains(&name) {
            self.fns.push(name);
        }
    }
}

impl DepCollector {
    fn new() -> Self {
        Self {
            deps: DepSet::default(),
            local_names: HashSet::new(),
        }
    }

    fn add_local_name(&mut self, name: &str) {
        self.local_names.insert(name.to_string());
    }

    fn add_param_def_with_type(&mut self, params: &ParamDefWithType) {
        for name in params.collect_param_names() {
            self.add_local_name(&name);
        }
    }

    fn add_param_def_with_set(&mut self, params: &ParamDefWithSet) {
        for name in params.collect_param_names() {
            self.add_local_name(&name);
        }
    }

    fn collect_param_def_with_type_deps(&mut self, params: &ParamDefWithType) {
        for group in params.groups.iter() {
            if let ParamType::Obj(obj) = &group.param_type {
                self.collect_obj(obj);
            }
        }
    }

    fn collect_param_def_with_set_deps(&mut self, params: &ParamDefWithSet) {
        for group in params.groups.iter() {
            self.collect_obj(&group.param_type);
        }
    }

    fn collect_fn_set_clause(&mut self, clause: &FnSetClause) {
        self.collect_param_def_with_set_deps(&clause.params_def_with_set);
        self.add_param_def_with_set(&clause.params_def_with_set);
        for fact in clause.dom_facts.iter() {
            self.collect_or_and_chain_atomic_fact(fact);
        }
        self.collect_obj(&clause.ret_set);
    }

    fn collect_fn_set_body(&mut self, body: &FnSetBody) {
        self.collect_param_def_with_set_deps(&body.params_def_with_set);
        self.add_param_def_with_set(&body.params_def_with_set);
        for fact in body.dom_facts.iter() {
            self.collect_or_and_chain_atomic_fact(fact);
        }
        self.collect_obj(&body.ret_set);
    }

    fn collect_anonymous_fn(&mut self, anonymous_fn: &AnonymousFn) {
        let old = self.local_names.clone();
        self.collect_fn_set_body(&anonymous_fn.body);
        self.collect_obj(&anonymous_fn.equal_to);
        self.local_names = old;
    }

    fn collect_have_fn_by_induc_case(&mut self, case: &HaveFnByInducCase) {
        self.collect_and_chain_atomic_fact(&case.case_fact);
        match &case.body {
            HaveFnByInducCaseBody::EqualTo(obj) => self.collect_obj(obj),
            HaveFnByInducCaseBody::NestedCases(cases) => {
                for nested in cases.iter() {
                    self.collect_have_fn_by_induc_case(nested);
                }
            }
        }
    }

    fn collect_fact(&mut self, fact: &Fact) {
        match fact {
            Fact::AtomicFact(a) => self.collect_atomic_fact(a),
            Fact::ExistFact(e) => self.collect_exist_fact(e),
            Fact::OrFact(o) => self.collect_or_fact(o),
            Fact::AndFact(a) => self.collect_and_fact(a),
            Fact::ChainFact(c) => self.collect_chain_fact(c),
            Fact::ForallFact(f) => self.collect_forall_fact(f),
            Fact::ForallFactWithIff(f) => {
                self.collect_forall_fact(&f.forall_fact);
                for fact in f.iff_facts.iter() {
                    self.collect_exist_or_and_chain_atomic_fact(fact);
                }
            }
            Fact::NotForall(f) => self.collect_forall_fact(&f.forall_fact),
        }
    }

    fn collect_forall_fact(&mut self, fact: &ForallFact) {
        let old = self.local_names.clone();
        self.collect_param_def_with_type_deps(&fact.params_def_with_type);
        self.add_param_def_with_type(&fact.params_def_with_type);
        for dom_fact in fact.dom_facts.iter() {
            self.collect_fact(dom_fact);
        }
        for then_fact in fact.then_facts.iter() {
            self.collect_exist_or_and_chain_atomic_fact(then_fact);
        }
        self.local_names = old;
    }

    fn collect_exist_fact(&mut self, fact: &ExistFactEnum) {
        let body = fact.body();
        let old = self.local_names.clone();
        self.collect_param_def_with_type_deps(&body.params_def_with_type);
        self.add_param_def_with_type(&body.params_def_with_type);
        for body_fact in body.facts.iter() {
            self.collect_exist_body_fact(body_fact);
        }
        self.local_names = old;
    }

    fn collect_exist_body_fact(&mut self, fact: &ExistBodyFact) {
        match fact {
            ExistBodyFact::AtomicFact(a) => self.collect_atomic_fact(a),
            ExistBodyFact::AndFact(a) => self.collect_and_fact(a),
            ExistBodyFact::ChainFact(c) => self.collect_chain_fact(c),
            ExistBodyFact::OrFact(o) => self.collect_or_fact(o),
            ExistBodyFact::InlineForall(f) => self.collect_forall_fact(f),
        }
    }

    fn collect_or_and_chain_atomic_fact(&mut self, fact: &OrAndChainAtomicFact) {
        match fact {
            OrAndChainAtomicFact::AtomicFact(a) => self.collect_atomic_fact(a),
            OrAndChainAtomicFact::AndFact(a) => self.collect_and_fact(a),
            OrAndChainAtomicFact::ChainFact(c) => self.collect_chain_fact(c),
            OrAndChainAtomicFact::OrFact(o) => self.collect_or_fact(o),
        }
    }

    fn collect_exist_or_and_chain_atomic_fact(&mut self, fact: &ExistOrAndChainAtomicFact) {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(a) => self.collect_atomic_fact(a),
            ExistOrAndChainAtomicFact::AndFact(a) => self.collect_and_fact(a),
            ExistOrAndChainAtomicFact::ChainFact(c) => self.collect_chain_fact(c),
            ExistOrAndChainAtomicFact::OrFact(o) => self.collect_or_fact(o),
            ExistOrAndChainAtomicFact::ExistFact(e) => self.collect_exist_fact(e),
        }
    }

    fn collect_and_chain_atomic_fact(&mut self, fact: &AndChainAtomicFact) {
        match fact {
            AndChainAtomicFact::AtomicFact(a) => self.collect_atomic_fact(a),
            AndChainAtomicFact::AndFact(a) => self.collect_and_fact(a),
            AndChainAtomicFact::ChainFact(c) => self.collect_chain_fact(c),
        }
    }

    fn collect_and_fact(&mut self, fact: &AndFact) {
        for atomic in fact.facts.iter() {
            self.collect_atomic_fact(atomic);
        }
    }

    fn collect_or_fact(&mut self, fact: &OrFact) {
        for branch in fact.facts.iter() {
            self.collect_and_chain_atomic_fact(branch);
        }
    }

    fn collect_chain_fact(&mut self, fact: &ChainFact) {
        for prop_name in fact.prop_names.iter() {
            let name = prop_name.to_string();
            if !is_builtin_predicate(&name) {
                self.deps.push_prop(name);
            }
        }
        for obj in fact.objs.iter() {
            self.collect_obj(obj);
        }
    }

    fn collect_atomic_fact(&mut self, fact: &AtomicFact) {
        match fact {
            AtomicFact::NormalAtomicFact(f) => {
                self.deps.push_prop(f.predicate.to_string());
                for obj in f.body.iter() {
                    self.collect_obj(obj);
                }
            }
            AtomicFact::NotNormalAtomicFact(f) => {
                self.deps.push_prop(f.predicate.to_string());
                for obj in f.body.iter() {
                    self.collect_obj(obj);
                }
            }
            _ => {
                for obj in fact.args_ref() {
                    self.collect_obj(obj);
                }
            }
        }
    }

    fn collect_obj(&mut self, obj: &Obj) {
        match obj {
            Obj::Atom(_) | Obj::Number(_) | Obj::StandardSet(_) => {}
            Obj::FnObj(fn_obj) => {
                self.collect_fn_head(&fn_obj.head);
                for group in fn_obj.body.iter() {
                    for arg in group.iter() {
                        self.collect_obj(arg);
                    }
                }
            }
            Obj::Add(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Sub(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Mul(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Div(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Mod(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Pow(x) => self.collect_two_objs(&x.base, &x.exponent),
            Obj::Log(x) => self.collect_two_objs(&x.base, &x.arg),
            Obj::Max(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Min(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Union(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Intersect(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::SetMinus(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::SetDiff(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Range(x) => self.collect_two_objs(&x.start, &x.end),
            Obj::ClosedRange(x) => self.collect_two_objs(&x.start, &x.end),
            Obj::IntervalObj(x) => self.collect_two_objs(x.start(), x.end()),
            Obj::MatrixAdd(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::MatrixSub(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::MatrixMul(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::MatrixScalarMul(x) => self.collect_two_objs(&x.scalar, &x.matrix),
            Obj::MatrixPow(x) => self.collect_two_objs(&x.base, &x.exponent),
            Obj::Proj(x) => self.collect_two_objs(&x.set, &x.dim),
            Obj::ObjAtIndex(x) => self.collect_two_objs(&x.obj, &x.index),
            Obj::FiniteSeqSet(x) => self.collect_two_objs(&x.set, &x.n),
            Obj::MatrixSet(x) => {
                self.collect_obj(&x.set);
                self.collect_obj(&x.row_len);
                self.collect_obj(&x.col_len);
            }
            Obj::Sum(x) => {
                self.collect_obj(&x.start);
                self.collect_obj(&x.end);
                self.collect_obj(&x.func);
            }
            Obj::SumOfFiniteSet(x) => {
                self.collect_obj(&x.set);
                self.collect_obj(&x.func);
            }
            Obj::Product(x) => {
                self.collect_obj(&x.start);
                self.collect_obj(&x.end);
                self.collect_obj(&x.func);
            }
            Obj::ProductOfFiniteSet(x) => {
                self.collect_obj(&x.set);
                self.collect_obj(&x.func);
            }
            Obj::Abs(x) => self.collect_obj(&x.arg),
            Obj::Sqrt(x) => self.collect_obj(&x.arg),
            Obj::Cup(x) => self.collect_obj(&x.left),
            Obj::Cap(x) => self.collect_obj(&x.left),
            Obj::PowerSet(x) => self.collect_obj(&x.set),
            Obj::Count(x) => self.collect_obj(&x.set),
            Obj::FnRange(x) => self.collect_obj(&x.function),
            Obj::FnRangeOn(x) => {
                self.collect_obj(&x.function);
                self.collect_obj(&x.set);
            }
            Obj::Replacement(x) => {
                self.deps.push_prop(x.prop_name.to_string());
                self.collect_obj(&x.source_set);
            }
            Obj::TupleDim(x) => self.collect_obj(&x.arg),
            Obj::CartDim(x) => self.collect_obj(&x.set),
            Obj::OneSideInfinityIntervalObj(x) => self.collect_obj(x.start()),
            Obj::SeqSet(x) => self.collect_obj(&x.set),
            Obj::ListSet(x) => {
                for obj in x.list.iter() {
                    self.collect_obj(obj);
                }
            }
            Obj::GeneralCart(x) => {
                self.collect_obj(&x.index_set);
                self.collect_obj(&x.family_set);
                self.collect_obj(&x.family_fn);
            }
            Obj::Cart(x) => {
                for obj in x.args.iter() {
                    self.collect_obj(obj);
                }
            }
            Obj::Tuple(x) => {
                for obj in x.args.iter() {
                    self.collect_obj(obj);
                }
            }
            Obj::FiniteSeqListObj(x) => {
                for obj in x.objs.iter() {
                    self.collect_obj(obj);
                }
            }
            Obj::MatrixListObj(x) => {
                for row in x.rows.iter() {
                    for obj in row.iter() {
                        self.collect_obj(obj);
                    }
                }
            }
            Obj::SetBuilder(x) => {
                self.collect_obj(&x.param_set);
                let old = self.local_names.clone();
                self.add_local_name(&x.param);
                for fact in x.facts.iter() {
                    self.collect_exist_body_fact(fact);
                }
                self.local_names = old;
            }
            Obj::FnSet(x) => {
                let old = self.local_names.clone();
                self.collect_fn_set_body(&x.body);
                self.local_names = old;
            }
            Obj::AnonymousFn(x) => self.collect_anonymous_fn(x),
            Obj::StructObj(x) => {
                for param in x.params.iter() {
                    self.collect_obj(param);
                }
            }
            Obj::ObjAsStructInstanceWithFieldAccess(x) => {
                for param in x.struct_obj.params.iter() {
                    self.collect_obj(param);
                }
                self.collect_obj(&x.obj);
            }
            Obj::InstantiatedTemplateObj(x) => {
                for arg in x.args.iter() {
                    self.collect_obj(arg);
                }
            }
        }
    }

    fn collect_fn_head(&mut self, head: &FnObjHead) {
        match head {
            FnObjHead::Identifier(identifier) => {
                if !self.local_names.contains(&identifier.name)
                    && !is_builtin_identifier_name(&identifier.name)
                {
                    self.deps.push_fn(identifier.name.clone());
                }
            }
            FnObjHead::IdentifierWithMod(identifier) => {
                self.deps.push_fn(format!(
                    "{}{}{}",
                    identifier.mod_name, MOD_SIGN, identifier.name
                ));
            }
            FnObjHead::AnonymousFnLiteral(a) => self.collect_anonymous_fn(a),
            FnObjHead::FiniteSeqListObj(list) => {
                for obj in list.objs.iter() {
                    self.collect_obj(obj);
                }
            }
            FnObjHead::ObjAtIndex(obj_at_index) => {
                self.collect_obj(&obj_at_index.obj);
                self.collect_obj(&obj_at_index.index);
            }
            FnObjHead::ObjAsStructInstanceWithFieldAccess(field_access) => {
                for param in field_access.struct_obj.params.iter() {
                    self.collect_obj(param);
                }
                self.collect_obj(&field_access.obj);
            }
            FnObjHead::InstantiatedTemplateObj(template_obj) => {
                for arg in template_obj.args.iter() {
                    self.collect_obj(arg);
                }
            }
            FnObjHead::Forall(_)
            | FnObjHead::DefHeader(_)
            | FnObjHead::Exist(_)
            | FnObjHead::SetBuilder(_)
            | FnObjHead::FnSet(_)
            | FnObjHead::Induc(_)
            | FnObjHead::DefAlgo(_)
            | FnObjHead::TupleIndex(_)
            | FnObjHead::CartIndex(_) => {}
        }
    }

    fn collect_two_objs(&mut self, left: &Obj, right: &Obj) {
        self.collect_obj(left);
        self.collect_obj(right);
    }
}

fn by_thm_names_in_stmts(stmts: &[Stmt]) -> Vec<String> {
    let mut out = Vec::new();
    for stmt in stmts.iter() {
        collect_by_thm_names_in_stmt(stmt, &mut out);
    }
    out
}

fn collect_by_thm_names_in_stmt(stmt: &Stmt, out: &mut Vec<String>) {
    match stmt {
        Stmt::By(ByStmt::ByThmStmt(s)) => out.push(s.name.to_string()),
        Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(s)) => {
            for stmt in s.proof.iter() {
                collect_by_thm_names_in_stmt(stmt, out);
            }
        }
        Stmt::ProofBlock(ProofBlockStmt::SketchStmt(s)) => {
            for stmt in s.proof.iter() {
                collect_by_thm_names_in_stmt(stmt, out);
            }
        }
        Stmt::ProofBlock(ProofBlockStmt::TryStmt(s)) => {
            for stmt in s.proof.iter() {
                collect_by_thm_names_in_stmt(stmt, out);
            }
        }
        Stmt::Witness(WitnessStmt::WitnessExistFact(s)) => {
            for stmt in s.proof.iter() {
                collect_by_thm_names_in_stmt(stmt, out);
            }
        }
        Stmt::Witness(WitnessStmt::WitnessNonemptySet(s)) => {
            for stmt in s.proof.iter() {
                collect_by_thm_names_in_stmt(stmt, out);
            }
        }
        Stmt::DefThmStmt(s) => {
            for stmt in s.prove_process.iter() {
                collect_by_thm_names_in_stmt(stmt, out);
            }
        }
        Stmt::DefObjStmt(DefObjStmt::HaveFnByForallExistUniqueStmt(s)) => {
            for stmt in s.prove_process.iter() {
                collect_by_thm_names_in_stmt(stmt, out);
            }
        }
        _ => {}
    }
}

fn prop_id(name: &str) -> String {
    format!("prop:{}", name)
}

fn fn_id(name: &str) -> String {
    format!("fn:{}", name)
}

fn fact_id(kind: &str, name: &str) -> String {
    format!("fact:{}:{}", kind, name)
}

fn line_json_value(line_file: &LineFile) -> JsonValue {
    if is_default_line_file(line_file) {
        JsonValue::Null
    } else {
        JsonValue::Number(line_file.0)
    }
}

fn line_label(line_file: &LineFile) -> String {
    if is_default_line_file(line_file) {
        "unknown".to_string()
    } else {
        line_file.0.to_string()
    }
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

fn mermaid_node_shape(node: &GraphNode) -> String {
    let label = mermaid_label(&node.label);
    match node.kind.as_str() {
        "prop" => format!("([\"{}\"])", label),
        "fn" => format!("{{\"{}\"}}", label),
        "fact" => format!("[/\"{}\"/]", label),
        _ => format!("[\"{}\"]", label),
    }
}

fn mermaid_label(label: &str) -> String {
    label.replace('"', "'")
}

#[cfg(test)]
mod tests {
    use super::run_graph_for_code;

    fn graph_output(source: &'static str) -> String {
        std::thread::Builder::new()
            .name("graph_output_large_stack".to_string())
            .stack_size(64 * 1024 * 1024)
            .spawn(move || run_graph_for_code(source, "graph_test", true).1)
            .expect("spawn graph output test")
            .join()
            .expect("graph output test panicked")
    }

    #[test]
    fn prop_definition_records_direct_prop_and_fn_dependencies() {
        let output = graph_output(
            "abstract_prop p(x)\nhave fn d(x R) R = x\nprop q(x R):\n    $p(x)\n    d(x) = x\n",
        );

        assert!(output.contains(r#""id": "prop:p""#));
        assert!(output.contains(r#""id": "fn:d""#));
        assert!(output.contains(r#""id": "prop:q""#));
        assert!(output.contains(r#""from": "prop:p""#));
        assert!(output.contains(r#""to": "prop:q""#));
        assert!(output.contains(r#""kind": "uses_prop""#));
        assert!(output.contains(r#""from": "fn:d""#));
        assert!(output.contains(r#""kind": "uses_fn""#));
    }

    #[test]
    fn graph_output_includes_summary_and_usage_counts() {
        let output =
            graph_output("abstract_prop p(x)\nprop q(x R):\n    $p(x)\nprop r(x R):\n    $p(x)\n");

        assert!(output.contains(r#""summary""#));
        assert!(output.contains(r#""usage""#));
        assert!(output.contains(r#""defined_props": 3"#));
        assert!(output.contains(r#""edges": 2"#));
        assert!(output.contains(r#""id": "prop:p""#));
        assert!(output.contains(r#""used_by_count": 2"#));
        assert!(output.contains(r#""count": 1"#));
    }

    #[test]
    fn function_domain_records_prop_dependency() {
        let output = graph_output("abstract_prop p(x)\nhave fn f(x R: $p(x)) R = x\n");

        assert!(output.contains(r#""from": "prop:p""#));
        assert!(output.contains(r#""to": "fn:f""#));
        assert!(output.contains(r#""kind": "uses_prop""#));
    }

    #[test]
    fn anonymous_function_inside_prop_records_inner_dependencies() {
        let output = graph_output(
            "abstract_prop p(x)\nhave fn a(x R) R = x\nprop f():\n    fn(x R: $p(x)) R {a(x)} = fn(x R: $p(x)) R {a(x)}\n",
        );

        assert!(output.contains(r#""from": "prop:p""#));
        assert!(output.contains(r#""to": "prop:f""#));
        assert!(output.contains(r#""kind": "uses_prop""#));
        assert!(output.contains(r#""from": "fn:a""#));
        assert!(output.contains(r#""to": "prop:f""#));
        assert!(output.contains(r#""kind": "uses_fn""#));
    }

    #[test]
    fn anonymous_function_returned_by_fn_records_inner_dependencies() {
        let output = graph_output(
            "abstract_prop p(x)\nhave fn a(x R) R = x\nhave fn make(x R: $p(x)) fn(z R) R = fn(y R) R {a(y)}\n",
        );

        assert!(output.contains(r#""from": "prop:p""#));
        assert!(output.contains(r#""to": "fn:make""#));
        assert!(output.contains(r#""kind": "uses_prop""#));
        assert!(output.contains(r#""from": "fn:a""#));
        assert!(output.contains(r#""to": "fn:make""#));
        assert!(output.contains(r#""kind": "uses_fn""#));
    }

    #[test]
    fn theorem_statement_records_vocabulary_dependencies() {
        let output = graph_output(
            "abstract_prop p(x)\nthm p_fact:\n    prove:\n        forall x R:\n            $p(x)\n            =>:\n                x = x\n        x = x\n",
        );

        assert!(output.contains(r#""id": "fact:thm:p_fact""#));
        assert!(output.contains(r#""from": "prop:p""#));
        assert!(output.contains(r#""to": "fact:thm:p_fact""#));
    }

    #[test]
    fn theorem_proof_records_theorem_citation_usage() {
        let output = graph_output(
            "thm graph_base:\n    ? forall x R:\n        x = x\n    x = x\nthm graph_use_base:\n    prove:\n        forall x R:\n            x = x\n    by thm graph_base(x)\n    x = x\n",
        );

        assert!(output.contains(r#""from": "fact:thm:graph_base""#));
        assert!(output.contains(r#""to": "fact:thm:graph_use_base""#));
        assert!(output.contains(r#""kind": "justified_by""#));
        assert!(output.contains(r#""used_by_count": 1"#));
    }

    #[test]
    fn theorem_backed_function_records_justification_fact() {
        let output = graph_output(
            "thm self_eq:\n    ? forall x R:\n        x = x\n    x = x\nhave fn identity by exist!:\n    ? forall x R:\n        exist! y R st {y = x}\n    trust exist! y R st {y = x}\n    by thm self_eq(x)\n    exist! y R st {y = x}\n",
        );

        assert!(output.contains(r#""from": "fact:thm:self_eq""#));
        assert!(output.contains(r#""to": "fn:identity""#));
        assert!(output.contains(r#""kind": "justified_by""#));
    }
}
