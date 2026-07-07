use crate::common::json_value::json_string_literal;
use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;

const MAIN_DOT_LIT: &str = "main.lit";

#[derive(Clone)]
struct DependencyNode {
    id: String,
    kind: String,
    text: String,
    source: LineFile,
    scope: String,
}

#[derive(Clone)]
struct DependencyEdge {
    from: String,
    to: String,
    kind: String,
    detail: String,
}

struct DependencyGraph {
    ok: bool,
    nodes: Vec<DependencyNode>,
    edges: Vec<DependencyEdge>,
    error: Option<DependencyGraphError>,
}

struct DependencyGraphError {
    error_type: String,
    message: String,
    source: LineFile,
}

struct GraphBuilder<'a> {
    runtime: &'a Runtime,
    nodes: Vec<DependencyNode>,
    edges: Vec<DependencyEdge>,
    node_ids: HashSet<String>,
    edge_keys: HashSet<String>,
    fact_nodes: HashMap<String, String>,
    definition_nodes: HashMap<String, String>,
    theorem_nodes: HashMap<String, String>,
    builtin_rule_nodes: HashMap<String, String>,
    external_nodes: HashMap<String, String>,
    next_fact_id: usize,
    next_definition_id: usize,
    next_theorem_id: usize,
    next_builtin_rule_id: usize,
    next_external_id: usize,
}

pub fn dependency_graph_json_for_results(
    runtime: &Runtime,
    stmt_results: &[StmtResult],
    runtime_error: &Option<RuntimeError>,
) -> String {
    let graph = GraphBuilder::build(runtime, stmt_results, runtime_error);
    render_json_value(&graph_to_json(runtime, &graph), 0)
}

pub fn dependency_graph_dot_for_results(
    runtime: &Runtime,
    stmt_results: &[StmtResult],
    runtime_error: &Option<RuntimeError>,
) -> String {
    let graph = GraphBuilder::build(runtime, stmt_results, runtime_error);
    graph_to_dot(&graph)
}

pub fn run_dependency_graph_json_for_code(
    code: &str,
    label: &str,
    detail_output: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_dependency_graph_on_source(
        "code",
        label,
        remove_windows_carriage_return(code).as_str(),
        detail_output,
        strict_mode,
        GraphOutputFormat::Json,
    )
}

pub fn run_dependency_graph_dot_for_code(
    code: &str,
    label: &str,
    detail_output: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_dependency_graph_on_source(
        "code",
        label,
        remove_windows_carriage_return(code).as_str(),
        detail_output,
        strict_mode,
        GraphOutputFormat::Dot,
    )
}

pub fn run_dependency_graph_json_for_file(
    file_path: &str,
    detail_output: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_dependency_graph_for_file(
        file_path,
        detail_output,
        strict_mode,
        GraphOutputFormat::Json,
    )
}

pub fn run_dependency_graph_dot_for_file(
    file_path: &str,
    detail_output: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_dependency_graph_for_file(
        file_path,
        detail_output,
        strict_mode,
        GraphOutputFormat::Dot,
    )
}

pub fn run_dependency_graph_json_for_repo(
    repo_path: &str,
    detail_output: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_dependency_graph_for_repo(
        repo_path,
        detail_output,
        strict_mode,
        GraphOutputFormat::Json,
    )
}

pub fn run_dependency_graph_dot_for_repo(
    repo_path: &str,
    detail_output: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_dependency_graph_for_repo(
        repo_path,
        detail_output,
        strict_mode,
        GraphOutputFormat::Dot,
    )
}

#[derive(Clone, Copy)]
enum GraphOutputFormat {
    Json,
    Dot,
}

impl<'a> GraphBuilder<'a> {
    fn build(
        runtime: &'a Runtime,
        stmt_results: &[StmtResult],
        runtime_error: &Option<RuntimeError>,
    ) -> DependencyGraph {
        let mut builder = GraphBuilder::new(runtime);
        for (index, result) in stmt_results.iter().enumerate() {
            builder.visit_stmt_result(&(index + 1).to_string(), result, None);
        }
        let error = runtime_error.as_ref().map(runtime_error_to_graph_error);
        if let Some(error) = &error {
            let error_id = "error:1".to_string();
            builder.add_node(
                error_id,
                "error",
                format!("{}: {}", error.error_type, error.message),
                error.source.clone(),
                "",
            );
        }
        DependencyGraph {
            ok: runtime_error.is_none(),
            nodes: builder.nodes,
            edges: builder.edges,
            error,
        }
    }

    fn new(runtime: &'a Runtime) -> Self {
        GraphBuilder {
            runtime,
            nodes: Vec::new(),
            edges: Vec::new(),
            node_ids: HashSet::new(),
            edge_keys: HashSet::new(),
            fact_nodes: HashMap::new(),
            definition_nodes: HashMap::new(),
            theorem_nodes: HashMap::new(),
            builtin_rule_nodes: HashMap::new(),
            external_nodes: HashMap::new(),
            next_fact_id: 1,
            next_definition_id: 1,
            next_theorem_id: 1,
            next_builtin_rule_id: 1,
            next_external_id: 1,
        }
    }

    fn visit_stmt_result(&mut self, path: &str, result: &StmtResult, parent_stmt_id: Option<&str>) {
        if let Some(success) = result.factual_success() {
            self.visit_factual_success(path, success, parent_stmt_id);
            return;
        }
        if let Some(success) = result.non_factual_success() {
            self.visit_non_factual_success(path, success, parent_stmt_id);
            return;
        }
        self.visit_unknown_result(path, result, parent_stmt_id);
    }

    fn visit_factual_success(
        &mut self,
        path: &str,
        success: &FactualStmtSuccess,
        parent_stmt_id: Option<&str>,
    ) {
        let stmt: Stmt = success.stmt.clone().into_stmt();
        let stmt_id = self.add_statement_node(path, &stmt);
        if let Some(parent_id) = parent_stmt_id {
            self.add_edge(&stmt_id, parent_id, "inside_proof", "");
        }

        let fact_id = self.fact_node(&success.stmt);
        self.add_edge(&stmt_id, &fact_id, "states", "");
        self.add_verified_by_edges(&success.verified_by, &fact_id);
        self.add_store_edges(&stmt_id, &success.infers);
    }

    fn visit_non_factual_success(
        &mut self,
        path: &str,
        success: &NonFactualStmtSuccess,
        parent_stmt_id: Option<&str>,
    ) {
        let stmt_id = self.add_statement_node(path, &success.stmt);
        if let Some(parent_id) = parent_stmt_id {
            self.add_edge(&stmt_id, parent_id, "inside_proof", "");
        }

        self.add_definition_edges_for_statement(&stmt_id, &success.stmt);
        self.add_non_factual_verification_edges(&stmt_id, success);

        for (index, inside_result) in success.inside_results.iter().enumerate() {
            let child_path = format!("{}.{}", path, index + 1);
            self.visit_stmt_result(&child_path, inside_result, Some(&stmt_id));
        }

        self.add_store_edges(&stmt_id, &success.infers);
    }

    fn visit_unknown_result(
        &mut self,
        path: &str,
        result: &StmtResult,
        parent_stmt_id: Option<&str>,
    ) {
        let line_file = result.line_file();
        let text = if let Some(unknown) = result.as_fact_unknown() {
            format!("unknown: {}", unknown.goal())
        } else if let Some(unknown) = result.as_unknown() {
            let detail = unknown.detail_for_display();
            if detail.is_empty() {
                "unknown statement".to_string()
            } else {
                format!("unknown: {}", detail)
            }
        } else {
            "unknown statement".to_string()
        };
        let stmt_id = format!("stmt:{}", path);
        self.add_node(stmt_id.clone(), "statement", text, line_file, path);
        if let Some(parent_id) = parent_stmt_id {
            self.add_edge(&stmt_id, parent_id, "inside_proof", "");
        }
    }

    fn add_statement_node(&mut self, path: &str, stmt: &Stmt) -> String {
        let id = format!("stmt:{}", path);
        self.add_node(
            id.clone(),
            "statement",
            stmt.to_string(),
            stmt.line_file(),
            path,
        );
        id
    }

    fn add_definition_edges_for_statement(&mut self, stmt_id: &str, stmt: &Stmt) {
        match stmt {
            Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(definition)) => {
                let def_id = self.definition_node(
                    "prop",
                    &definition.name,
                    &definition.to_string(),
                    definition.line_file.clone(),
                );
                self.add_edge(stmt_id, &def_id, "defines", "");
                for prop_name in prop_refs_in_facts(&definition.iff_facts) {
                    if prop_name == definition.name {
                        continue;
                    }
                    let dep_id = self.definition_ref_node("prop", &prop_name);
                    self.add_edge(&dep_id, &def_id, "uses_definition", "");
                }
            }
            Stmt::DefPredicateStmt(DefPredicateStmt::DefAbstractPropStmt(definition)) => {
                let def_id = self.definition_node(
                    "abstract_prop",
                    &definition.name,
                    &definition.to_string(),
                    definition.line_file.clone(),
                );
                self.add_edge(stmt_id, &def_id, "defines", "");
            }
            Stmt::DefThmStmt(definition) => {
                for name in &definition.names {
                    let theorem_id = self.theorem_node(
                        name,
                        Some(definition.clone()),
                        definition.line_file.clone(),
                    );
                    self.add_edge(stmt_id, &theorem_id, "defines", "");
                }
            }
            _ => {}
        }
    }

    fn add_non_factual_verification_edges(
        &mut self,
        stmt_id: &str,
        success: &NonFactualStmtSuccess,
    ) {
        if let Some(verification) = success.claim_verification.as_ref() {
            match verification {
                ClaimVerificationResult::Forall(v) => {
                    let fact_id = self.fact_node(&Fact::ForallFact(v.forall_fact.clone()));
                    self.add_edge(stmt_id, &fact_id, "proves", "claim forall");
                }
                ClaimVerificationResult::Fact(v) => {
                    let fact_id = self.fact_node(&v.fact);
                    self.add_edge(stmt_id, &fact_id, "proves", "claim");
                }
            }
        }
        let Some(verification) = success.by_verification.as_ref() else {
            return;
        };
        match verification {
            ByVerificationResult::Theorem(v) => {
                let theorem = self.runtime.get_thm_definition_by_name(&v.theorem);
                let theorem_line = theorem
                    .as_ref()
                    .map(|thm| thm.line_file.clone())
                    .unwrap_or_else(default_line_file);
                let theorem_id = self.theorem_node(&v.theorem, theorem, theorem_line);
                self.add_edge(&theorem_id, stmt_id, "uses_theorem", "");
                for domain_fact in &v.domain_facts {
                    let requirement_id = self.external_node(
                        "fact",
                        domain_fact,
                        success.stmt.line_file(),
                        "theorem domain fact",
                    );
                    self.add_edge(&requirement_id, stmt_id, "requires", "");
                }
            }
            ByVerificationResult::PropRegistration(v) => {
                let fact_id = self.fact_node(&Fact::ForallFact(v.forall_fact.clone()));
                self.add_edge(stmt_id, &fact_id, "registers", v.registration_type.as_str());
            }
            ByVerificationResult::Contra(v) => {
                let assumption_id = self.fact_node(&v.reverse_assumption);
                self.add_edge(
                    &assumption_id,
                    stmt_id,
                    "local_assumption",
                    "reverse assumption",
                );
                let goal_id = self.fact_node(&v.to_prove);
                self.add_edge(stmt_id, &goal_id, "proves", "by contradiction");
            }
            _ => {}
        }
    }

    fn add_store_edges(&mut self, stmt_id: &str, infers: &InferResult) {
        for output in infers.store_fact_outputs() {
            let stored_fact = &output.itself_and_why_itself_is_stored.0;
            let reason = &output.itself_and_why_itself_is_stored.1;
            let stored_id = self.fact_node(stored_fact);
            self.add_edge(stmt_id, &stored_id, "stores", reason);
            for inferred_fact in &output.inferred_facts {
                let inferred_id = self.fact_node(inferred_fact);
                self.add_edge(&stored_id, &inferred_id, "infers", reason);
            }
        }
    }

    fn add_verified_by_edges(&mut self, verified_by: &VerifiedByResult, target_fact_id: &str) {
        match verified_by {
            VerifiedByResult::BuiltinRule(rule) => {
                let rule_id = self.builtin_rule_node(&rule.msg);
                self.add_edge(&rule_id, target_fact_id, "verifies", "");
                for subgoal in &rule.subgoals {
                    self.add_subgoal_edge(subgoal, target_fact_id);
                }
            }
            VerifiedByResult::Fact(citation) => {
                let citation_id = self.citation_node(citation.cite_what.as_ref());
                self.add_edge(
                    &citation_id,
                    target_fact_id,
                    "verifies",
                    citation.detail.as_deref().unwrap_or(""),
                );
            }
            VerifiedByResult::KnownForallInstantiation(instantiation) => {
                let cite_id = self.citation_node(instantiation.cite_what.as_ref());
                self.add_edge(&cite_id, target_fact_id, "verifies", "known forall");
                for requirement in &instantiation.requirements {
                    let requirement_id = self.fact_node(&requirement.stmt);
                    self.add_edge(&requirement_id, target_fact_id, "requires", "");
                    self.add_subgoal_edge(requirement.result.as_ref(), &requirement_id);
                }
            }
            VerifiedByResult::VerifiedBys(steps) => {
                for step in &steps.cite_what {
                    self.add_verified_bys_enum_edges(step, target_fact_id);
                }
            }
            VerifiedByResult::ForallProof(proof) => {
                for proved in &proof.proves {
                    let proved_fact = proved.stmt.clone().to_fact();
                    let proved_id = self.fact_node(&proved_fact);
                    self.add_edge(&proved_id, target_fact_id, "forall_conclusion", "");
                    self.add_subgoal_edge(proved.result.as_ref(), &proved_id);
                }
            }
        }
    }

    fn add_verified_bys_enum_edges(&mut self, step: &VerifiedBysEnum, target_fact_id: &str) {
        match step {
            VerifiedBysEnum::ByBuiltinRule(rule) => {
                let rule_id = self.builtin_rule_node(&rule.msg);
                self.add_edge(&rule_id, target_fact_id, "verifies", "");
                let verify_id = self.fact_node(&rule.verify_what);
                self.add_edge(&verify_id, target_fact_id, "step", "");
                for subgoal in &rule.subgoals {
                    self.add_subgoal_edge(subgoal, &verify_id);
                }
            }
            VerifiedBysEnum::ByFact(citation) => {
                let citation_id = self.citation_node(citation.cite_what.as_ref());
                self.add_edge(
                    &citation_id,
                    target_fact_id,
                    "verifies",
                    citation.detail.as_deref().unwrap_or(""),
                );
                let verify_id = self.fact_node(&citation.verify_what);
                self.add_edge(&verify_id, target_fact_id, "step", "");
            }
            VerifiedBysEnum::ByKnownForall(known_forall) => {
                let citation_id = self.citation_node(known_forall.result.cite_what.as_ref());
                self.add_edge(&citation_id, target_fact_id, "verifies", "known forall");
                let verify_id = self.fact_node(&known_forall.verify_what);
                self.add_edge(&verify_id, target_fact_id, "step", "");
                for requirement in &known_forall.result.requirements {
                    let requirement_id = self.fact_node(&requirement.stmt);
                    self.add_edge(&requirement_id, &verify_id, "requires", "");
                    self.add_subgoal_edge(requirement.result.as_ref(), &requirement_id);
                }
            }
        }
    }

    fn add_subgoal_edge(&mut self, subgoal: &StmtResult, target_fact_id: &str) {
        if let Some(success) = subgoal.factual_success() {
            let subgoal_id = self.fact_node(&success.stmt);
            self.add_edge(&subgoal_id, target_fact_id, "subgoal", "");
            self.add_verified_by_edges(&success.verified_by, &subgoal_id);
        } else if let Some(success) = subgoal.non_factual_success() {
            let external_id = self.external_node(
                "statement",
                &success.stmt.to_string(),
                success.stmt.line_file(),
                "subgoal statement",
            );
            self.add_edge(&external_id, target_fact_id, "subgoal", "");
        }
    }

    fn citation_node(&mut self, stmt: &Stmt) -> String {
        match stmt {
            Stmt::Fact(fact) => self.fact_node(fact),
            Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(definition)) => self
                .definition_node(
                    "prop",
                    &definition.name,
                    &definition.to_string(),
                    definition.line_file.clone(),
                ),
            Stmt::DefPredicateStmt(DefPredicateStmt::DefAbstractPropStmt(definition)) => self
                .definition_node(
                    "abstract_prop",
                    &definition.name,
                    &definition.to_string(),
                    definition.line_file.clone(),
                ),
            Stmt::DefThmStmt(definition) => {
                let name = definition
                    .names
                    .first()
                    .cloned()
                    .unwrap_or_else(|| "anonymous theorem".to_string());
                self.theorem_node(
                    &name,
                    Some(definition.clone()),
                    definition.line_file.clone(),
                )
            }
            _ => self.external_node("statement", &stmt.to_string(), stmt.line_file(), "citation"),
        }
    }

    fn fact_node(&mut self, fact: &Fact) -> String {
        let key = fact_key(fact);
        if let Some(id) = self.fact_nodes.get(&key) {
            return id.clone();
        }
        let id = format!("fact:{}", self.next_fact_id);
        self.next_fact_id += 1;
        self.add_node(id.clone(), "fact", fact.to_string(), fact.line_file(), "");
        self.fact_nodes.insert(key, id.clone());
        id
    }

    fn definition_ref_node(&mut self, definition_kind: &str, name: &str) -> String {
        let key = format!("{}:{}", definition_kind, name);
        if let Some(id) = self.definition_nodes.get(&key) {
            return id.clone();
        }
        let id = format!("definition:{}", self.next_definition_id);
        self.next_definition_id += 1;
        self.add_node(
            id.clone(),
            "definition",
            format!("{} {}", definition_kind, name),
            default_line_file(),
            "",
        );
        self.definition_nodes.insert(key, id.clone());
        id
    }

    fn definition_node(
        &mut self,
        definition_kind: &str,
        name: &str,
        text: &str,
        source: LineFile,
    ) -> String {
        let key = format!("{}:{}", definition_kind, name);
        if let Some(id) = self.definition_nodes.get(&key) {
            return id.clone();
        }
        let id = format!("definition:{}", self.next_definition_id);
        self.next_definition_id += 1;
        self.add_node(id.clone(), "definition", text.to_string(), source, "");
        self.definition_nodes.insert(key, id.clone());
        id
    }

    fn theorem_node(
        &mut self,
        name: &str,
        definition: Option<DefThmStmt>,
        source: LineFile,
    ) -> String {
        let key = name.to_string();
        if let Some(id) = self.theorem_nodes.get(&key) {
            return id.clone();
        }
        let id = format!("theorem:{}", self.next_theorem_id);
        self.next_theorem_id += 1;
        let text = definition
            .map(|definition| definition.to_string())
            .unwrap_or_else(|| format!("theorem {}", name));
        self.add_node(id.clone(), "theorem", text, source, "");
        self.theorem_nodes.insert(key, id.clone());
        id
    }

    fn builtin_rule_node(&mut self, rule: &str) -> String {
        if let Some(id) = self.builtin_rule_nodes.get(rule) {
            return id.clone();
        }
        let id = format!("builtin_rule:{}", self.next_builtin_rule_id);
        self.next_builtin_rule_id += 1;
        self.add_node(
            id.clone(),
            "builtin_rule",
            rule.to_string(),
            default_line_file(),
            "",
        );
        self.builtin_rule_nodes.insert(rule.to_string(), id.clone());
        id
    }

    fn external_node(&mut self, kind: &str, text: &str, source: LineFile, detail: &str) -> String {
        let key = format!("{}:{}:{}:{}:{}", kind, source.1, source.0, text, detail);
        if let Some(id) = self.external_nodes.get(&key) {
            return id.clone();
        }
        let id = format!("external:{}", self.next_external_id);
        self.next_external_id += 1;
        self.add_node(id.clone(), kind, text.to_string(), source, "");
        self.external_nodes.insert(key, id.clone());
        id
    }

    fn add_node(
        &mut self,
        id: String,
        kind: impl Into<String>,
        text: impl Into<String>,
        source: LineFile,
        scope: impl Into<String>,
    ) {
        if !self.node_ids.insert(id.clone()) {
            return;
        }
        self.nodes.push(DependencyNode {
            id,
            kind: kind.into(),
            text: text.into(),
            source,
            scope: scope.into(),
        });
    }

    fn add_edge(
        &mut self,
        from: &str,
        to: &str,
        kind: impl Into<String>,
        detail: impl Into<String>,
    ) {
        if from == to {
            return;
        }
        let kind = kind.into();
        let detail = detail.into();
        let key = format!("{}->{}:{}:{}", from, to, kind, detail);
        if !self.edge_keys.insert(key) {
            return;
        }
        self.edges.push(DependencyEdge {
            from: from.to_string(),
            to: to.to_string(),
            kind,
            detail,
        });
    }
}

fn run_dependency_graph_for_file(
    file_path: &str,
    detail_output: bool,
    strict_mode: bool,
    format: GraphOutputFormat,
) -> (bool, String) {
    let resolved_path = match crate::runner::resolve_litex_file_path(file_path) {
        Ok(path) => path,
        Err(message) => return target_error_graph(message, format),
    };
    let source_code = match fs::read_to_string(resolved_path.as_str()) {
        Ok(content) => content,
        Err(error) => return target_error_graph(format!("could not read file: {}", error), format),
    };
    run_dependency_graph_on_source(
        "file",
        resolved_path.as_str(),
        source_code.as_str(),
        detail_output,
        strict_mode,
        format,
    )
}

fn run_dependency_graph_for_repo(
    repo_path: &str,
    detail_output: bool,
    strict_mode: bool,
    format: GraphOutputFormat,
) -> (bool, String) {
    let joined = Path::new(repo_path).join(MAIN_DOT_LIT);
    let Some(joined_string) = joined.to_str() else {
        return target_error_graph("repo path is not valid UTF-8".to_string(), format);
    };
    run_dependency_graph_for_file(joined_string, detail_output, strict_mode, format)
}

fn run_dependency_graph_on_source(
    _target_kind: &str,
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
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let ok = runtime_error.is_none();
    let output = match format {
        GraphOutputFormat::Json => {
            dependency_graph_json_for_results(&runtime, &stmt_results, &runtime_error)
        }
        GraphOutputFormat::Dot => {
            dependency_graph_dot_for_results(&runtime, &stmt_results, &runtime_error)
        }
    };
    (ok, strip_free_param_numeric_tags_in_display(&output))
}

fn target_error_graph(message: String, format: GraphOutputFormat) -> (bool, String) {
    let error = DependencyGraphError {
        error_type: "TargetError".to_string(),
        message,
        source: default_line_file(),
    };
    let graph = DependencyGraph {
        ok: false,
        nodes: vec![DependencyNode {
            id: "error:1".to_string(),
            kind: "error".to_string(),
            text: format!("{}: {}", error.error_type, error.message),
            source: default_line_file(),
            scope: String::new(),
        }],
        edges: vec![],
        error: Some(error),
    };
    let output = match format {
        GraphOutputFormat::Json => {
            let runtime = Runtime::new();
            render_json_value(&graph_to_json(&runtime, &graph), 0)
        }
        GraphOutputFormat::Dot => graph_to_dot(&graph),
    };
    (false, output)
}

fn graph_to_json(runtime: &Runtime, graph: &DependencyGraph) -> JsonValue {
    let nodes = graph
        .nodes
        .iter()
        .map(|node| node_to_json(runtime, node))
        .collect::<Vec<_>>();
    let edges = graph.edges.iter().map(edge_to_json).collect::<Vec<_>>();
    let error = graph
        .error
        .as_ref()
        .map(|error| error_to_json(runtime, error))
        .unwrap_or(JsonValue::Null);
    JsonValue::Object(vec![
        (
            "result".to_string(),
            JsonValue::JsonString(if graph.ok { "success" } else { "error" }.to_string()),
        ),
        ("ok".to_string(), JsonValue::Bool(graph.ok)),
        ("nodes".to_string(), JsonValue::Array(nodes)),
        ("edges".to_string(), JsonValue::Array(edges)),
        ("error".to_string(), error),
    ])
}

fn node_to_json(runtime: &Runtime, node: &DependencyNode) -> JsonValue {
    let mut fields = vec![
        ("id".to_string(), JsonValue::JsonString(node.id.clone())),
        ("kind".to_string(), JsonValue::JsonString(node.kind.clone())),
        ("text".to_string(), JsonValue::JsonString(node.text.clone())),
        (
            "source".to_string(),
            source_json_value(runtime, &node.source),
        ),
    ];
    if !node.scope.is_empty() {
        fields.push((
            "scope".to_string(),
            JsonValue::JsonString(node.scope.clone()),
        ));
    }
    JsonValue::Object(fields)
}

fn edge_to_json(edge: &DependencyEdge) -> JsonValue {
    let mut fields = vec![
        ("from".to_string(), JsonValue::JsonString(edge.from.clone())),
        ("to".to_string(), JsonValue::JsonString(edge.to.clone())),
        ("kind".to_string(), JsonValue::JsonString(edge.kind.clone())),
    ];
    if !edge.detail.is_empty() {
        fields.push((
            "detail".to_string(),
            JsonValue::JsonString(edge.detail.clone()),
        ));
    }
    JsonValue::Object(fields)
}

fn error_to_json(runtime: &Runtime, error: &DependencyGraphError) -> JsonValue {
    JsonValue::Object(vec![
        (
            "error_type".to_string(),
            JsonValue::JsonString(error.error_type.clone()),
        ),
        (
            "message".to_string(),
            JsonValue::JsonString(error.message.clone()),
        ),
        (
            "source".to_string(),
            source_json_value(runtime, &error.source),
        ),
    ])
}

fn graph_to_dot(graph: &DependencyGraph) -> String {
    let mut out = String::new();
    out.push_str("digraph litex_dependency_graph {\n");
    out.push_str("  rankdir=LR;\n");
    out.push_str("  node [shape=box, style=rounded];\n");
    for node in &graph.nodes {
        let label = format!("{}\\n{}", node.kind, compact_dot_label(&node.text));
        out.push_str(&format!(
            "  {} [label={}];\n",
            dot_id(&node.id),
            dot_string(&label)
        ));
    }
    for edge in &graph.edges {
        let label = if edge.detail.is_empty() {
            edge.kind.clone()
        } else {
            format!("{}: {}", edge.kind, edge.detail)
        };
        out.push_str(&format!(
            "  {} -> {} [label={}];\n",
            dot_id(&edge.from),
            dot_id(&edge.to),
            dot_string(&label)
        ));
    }
    out.push_str("}\n");
    out
}

fn source_json_value(runtime: &Runtime, line_file: &LineFile) -> JsonValue {
    let mut fields = vec![("line".to_string(), line_json_value(line_file))];
    if is_default_line_file(line_file) {
        return JsonValue::Object(fields);
    }
    let path = line_file.1.as_ref();
    if path == BUILTIN_CODE_PATH {
        fields.push((
            "source_kind".to_string(),
            JsonValue::JsonString("builtin".to_string()),
        ));
        fields.push((
            "source".to_string(),
            JsonValue::JsonString(BUILTIN_CODE_PATH.to_string()),
        ));
        return JsonValue::Object(fields);
    }
    let module_manager = runtime.module_manager.borrow();
    if path == module_manager.entry_path_rc.as_ref() {
        fields.push((
            "source_kind".to_string(),
            JsonValue::JsonString("entry".to_string()),
        ));
        fields.push((
            "source".to_string(),
            JsonValue::JsonString("entry".to_string()),
        ));
        if runtime.detail_output {
            fields.push(("path".to_string(), JsonValue::JsonString(path.to_string())));
        }
        return JsonValue::Object(fields);
    }
    for (module_name, imported_module) in &module_manager.imported_modules {
        if path.starts_with(imported_module.absolute_path.as_str()) {
            let source_kind = if imported_module.is_std {
                "std"
            } else {
                "module"
            };
            let source = if imported_module.is_std {
                format!("std/{}", module_name)
            } else {
                module_name.clone()
            };
            fields.push((
                "source_kind".to_string(),
                JsonValue::JsonString(source_kind.to_string()),
            ));
            fields.push(("source".to_string(), JsonValue::JsonString(source)));
            if runtime.detail_output {
                fields.push(("path".to_string(), JsonValue::JsonString(path.to_string())));
            }
            return JsonValue::Object(fields);
        }
    }
    fields.push((
        "source_kind".to_string(),
        JsonValue::JsonString("run_file".to_string()),
    ));
    fields.push((
        "source".to_string(),
        JsonValue::JsonString("external_file".to_string()),
    ));
    if runtime.detail_output {
        fields.push(("path".to_string(), JsonValue::JsonString(path.to_string())));
    }
    JsonValue::Object(fields)
}

fn line_json_value(line_file: &LineFile) -> JsonValue {
    if is_default_line_file(line_file) {
        JsonValue::Null
    } else {
        JsonValue::Number(line_file.0)
    }
}

fn runtime_error_to_graph_error(error: &RuntimeError) -> DependencyGraphError {
    DependencyGraphError {
        error_type: error.display_label().to_string(),
        message: runtime_error_message(error),
        source: error.line_file(),
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

fn fact_key(fact: &Fact) -> String {
    let line_file = fact.line_file();
    format!("{}:{}:{}", line_file.1, line_file.0, fact)
}

fn prop_refs_in_facts(facts: &[Fact]) -> Vec<String> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    for fact in facts {
        collect_prop_refs_in_fact(fact, &mut seen, &mut out);
    }
    out
}

fn collect_prop_refs_in_fact(fact: &Fact, seen: &mut HashSet<String>, out: &mut Vec<String>) {
    match fact {
        Fact::AtomicFact(atomic) => collect_prop_refs_in_atomic(atomic, seen, out),
        Fact::ExistFact(exist) => collect_prop_refs_in_exist(exist, seen, out),
        Fact::OrFact(or_fact) => {
            for branch in &or_fact.facts {
                collect_prop_refs_in_exist_or_and_chain_atomic(&branch.clone().into(), seen, out);
            }
        }
        Fact::AndFact(and_fact) => {
            for atomic in &and_fact.facts {
                collect_prop_refs_in_atomic(atomic, seen, out);
            }
        }
        Fact::ChainFact(chain_fact) => {
            for prop_name in &chain_fact.prop_names {
                push_prop_name(prop_name.to_string(), seen, out);
            }
        }
        Fact::ForallFact(forall_fact) => {
            for dom_fact in &forall_fact.dom_facts {
                collect_prop_refs_in_fact(dom_fact, seen, out);
            }
            for then_fact in &forall_fact.then_facts {
                collect_prop_refs_in_exist_or_and_chain_atomic(then_fact, seen, out);
            }
        }
        Fact::ForallFactWithIff(forall_fact_with_iff) => {
            collect_prop_refs_in_fact(
                &Fact::ForallFact(forall_fact_with_iff.forall_fact.clone()),
                seen,
                out,
            );
            for iff_fact in &forall_fact_with_iff.iff_facts {
                collect_prop_refs_in_exist_or_and_chain_atomic(iff_fact, seen, out);
            }
        }
        Fact::NotForall(not_forall) => {
            collect_prop_refs_in_fact(&Fact::ForallFact(not_forall.forall_fact.clone()), seen, out)
        }
    }
}

fn collect_prop_refs_in_exist(
    exist: &ExistFactEnum,
    seen: &mut HashSet<String>,
    out: &mut Vec<String>,
) {
    let body = match exist {
        ExistFactEnum::ExistFact(body)
        | ExistFactEnum::ExistUniqueFact(body)
        | ExistFactEnum::NotExistFact(body) => body,
    };
    for fact in &body.facts {
        match fact {
            ExistBodyFact::AtomicFact(atomic) => collect_prop_refs_in_atomic(atomic, seen, out),
            ExistBodyFact::AndFact(and_fact) => {
                for atomic in &and_fact.facts {
                    collect_prop_refs_in_atomic(atomic, seen, out);
                }
            }
            ExistBodyFact::ChainFact(chain_fact) => {
                for prop_name in &chain_fact.prop_names {
                    push_prop_name(prop_name.to_string(), seen, out);
                }
            }
            ExistBodyFact::OrFact(or_fact) => {
                for branch in &or_fact.facts {
                    collect_prop_refs_in_exist_or_and_chain_atomic(
                        &branch.clone().into(),
                        seen,
                        out,
                    );
                }
            }
            ExistBodyFact::InlineForall(forall_fact) => {
                collect_prop_refs_in_fact(&Fact::ForallFact(forall_fact.clone()), seen, out)
            }
        }
    }
}

fn collect_prop_refs_in_exist_or_and_chain_atomic(
    fact: &ExistOrAndChainAtomicFact,
    seen: &mut HashSet<String>,
    out: &mut Vec<String>,
) {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(atomic) => {
            collect_prop_refs_in_atomic(atomic, seen, out)
        }
        ExistOrAndChainAtomicFact::AndFact(and_fact) => {
            for atomic in &and_fact.facts {
                collect_prop_refs_in_atomic(atomic, seen, out);
            }
        }
        ExistOrAndChainAtomicFact::ChainFact(chain_fact) => {
            for prop_name in &chain_fact.prop_names {
                push_prop_name(prop_name.to_string(), seen, out);
            }
        }
        ExistOrAndChainAtomicFact::OrFact(or_fact) => {
            for branch in &or_fact.facts {
                collect_prop_refs_in_exist_or_and_chain_atomic(&branch.clone().into(), seen, out);
            }
        }
        ExistOrAndChainAtomicFact::ExistFact(exist_fact) => {
            collect_prop_refs_in_exist(exist_fact, seen, out)
        }
    }
}

fn collect_prop_refs_in_atomic(
    atomic: &AtomicFact,
    seen: &mut HashSet<String>,
    out: &mut Vec<String>,
) {
    match atomic {
        AtomicFact::NormalAtomicFact(fact) => push_prop_name(fact.predicate.to_string(), seen, out),
        AtomicFact::NotNormalAtomicFact(fact) => {
            push_prop_name(fact.predicate.to_string(), seen, out)
        }
        _ => {}
    }
}

fn push_prop_name(name: String, seen: &mut HashSet<String>, out: &mut Vec<String>) {
    if seen.insert(name.clone()) {
        out.push(name);
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
