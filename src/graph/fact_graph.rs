use crate::prelude::*;
use std::collections::{HashMap, HashSet};

const FACT_GRAPH_NAME: &str = "litex-fact-graph";
const FACT_GRAPH_VERSION: &str = "0.1";

#[derive(Clone)]
struct FactGraphNode {
    id: String,
    kind: String,
    label: String,
    fact_kind: Option<String>,
    line_file: Option<LineFile>,
    statement: Option<String>,
    reason: Option<String>,
}

struct FactGraphEdge {
    from: String,
    to: String,
    kind: String,
    count: usize,
}

struct FactGraphBuilder {
    nodes: Vec<FactGraphNode>,
    node_index: HashMap<String, usize>,
    edges: Vec<FactGraphEdge>,
    edge_index: HashMap<String, usize>,
    trust_node_by_line: HashMap<String, String>,
    theorem_node_by_line: HashMap<String, String>,
    claim_node_by_line: HashMap<String, String>,
}

pub fn run_fact_graph_for_code(code: &str, label: &str, hide_file_paths: bool) -> (bool, String) {
    run_fact_graph_for_code_with_language(code, label, hide_file_paths, OutputLanguage::English)
}

pub fn run_fact_graph_for_code_with_language(
    code: &str,
    label: &str,
    hide_file_paths: bool,
    _output_language: OutputLanguage,
) -> (bool, String) {
    run_fact_graph_on_source("code", label, code, hide_file_paths, false)
}

pub fn run_fact_graph_for_code_strict(
    code: &str,
    label: &str,
    hide_file_paths: bool,
) -> (bool, String) {
    run_fact_graph_for_code_strict_with_language(
        code,
        label,
        hide_file_paths,
        OutputLanguage::English,
    )
}

pub fn run_fact_graph_for_code_strict_with_language(
    code: &str,
    label: &str,
    hide_file_paths: bool,
    _output_language: OutputLanguage,
) -> (bool, String) {
    run_fact_graph_on_source("code", label, code, hide_file_paths, true)
}

pub fn run_fact_graph_for_file(file_path: &str, hide_file_paths: bool) -> (bool, String) {
    run_fact_graph_for_file_with_strict(file_path, hide_file_paths, false)
}

pub fn run_fact_graph_for_file_with_strict(
    file_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_fact_graph_for_file_with_strict_and_language(
        file_path,
        hide_file_paths,
        strict_mode,
        OutputLanguage::English,
    )
}

pub fn run_fact_graph_for_file_with_strict_and_language(
    file_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
) -> (bool, String) {
    run_fact_graph_for_file_with_strict_language_and_isolation(
        file_path,
        hide_file_paths,
        strict_mode,
        output_language,
        false,
    )
}

pub fn run_fact_graph_for_file_with_strict_language_and_isolation(
    file_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
    _output_language: OutputLanguage,
    force_isolated: bool,
) -> (bool, String) {
    let resolved_path = match resolve_litex_file_path(file_path) {
        Ok(path) => path,
        Err(message) => {
            return fact_graph_target_error_output("file", file_path, hide_file_paths, message);
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
    render_fact_graph_result(
        "file",
        resolved_path.as_str(),
        hide_file_paths,
        runtime,
        stmt_results,
        runtime_error,
    )
}

pub fn run_fact_graph_for_repo(repo_path: &str, hide_file_paths: bool) -> (bool, String) {
    run_fact_graph_for_repo_with_strict(repo_path, hide_file_paths, false)
}

pub fn run_fact_graph_for_repo_with_strict(
    repo_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_fact_graph_for_repo_with_strict_and_language(
        repo_path,
        hide_file_paths,
        strict_mode,
        OutputLanguage::English,
    )
}

pub fn run_fact_graph_for_repo_with_strict_and_language(
    repo_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
    _output_language: OutputLanguage,
) -> (bool, String) {
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.detail_output = !hide_file_paths;
    runtime.strict_mode = strict_mode;
    match discover_repository(&mut runtime, repo_path) {
        Ok(_) => {}
        Err(error) => {
            return render_fact_graph_result(
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
        RepositoryFileTarget::Module(entry_module_id),
    );
    render_fact_graph_result(
        "repo",
        repo_path,
        hide_file_paths,
        runtime,
        stmt_results,
        runtime_error,
    )
}

fn run_fact_graph_on_source(
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
    render_fact_graph_result(
        target_kind,
        target_label,
        hide_file_paths,
        runtime,
        stmt_results,
        runtime_error,
    )
}

fn render_fact_graph_result(
    target_kind: &str,
    target_label: &str,
    hide_file_paths: bool,
    runtime: Runtime,
    stmt_results: Vec<StmtResult>,
    runtime_error: Option<RuntimeError>,
) -> (bool, String) {
    render_fact_graph_from_stmt_results(
        target_kind,
        target_label,
        hide_file_paths,
        &runtime,
        stmt_results.as_slice(),
        runtime_error.as_ref(),
    )
}

/// Render only the proof-facing dependency graph from already executed statements.
///
/// The graph omits `prop`, function, and object-definition nodes. Its edges are
/// taken from the verifier's actual citation and `forall`-requirement evidence.
pub fn render_fact_graph_from_stmt_results(
    target_kind: &str,
    target_label: &str,
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
            fact_graph_target_json_value(target_kind, target_label, hide_file_paths),
        ),
    ];
    if let Some(error) = runtime_error {
        fields.push((
            "error".to_string(),
            JsonValue::JsonString(display_runtime_error_json(runtime, error, true)),
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

fn fact_graph_target_error_output(
    target_kind: &str,
    target_label: &str,
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
            fact_graph_target_json_value(target_kind, target_label, hide_file_paths),
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

fn fact_graph_target_json_value(
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

impl FactGraphBuilder {
    fn new() -> Self {
        Self {
            nodes: vec![],
            node_index: HashMap::new(),
            edges: vec![],
            edge_index: HashMap::new(),
            trust_node_by_line: HashMap::new(),
            theorem_node_by_line: HashMap::new(),
            claim_node_by_line: HashMap::new(),
        }
    }

    fn from_stmt_results(stmt_results: &[StmtResult]) -> Self {
        let mut builder = Self::new();
        for result in stmt_results {
            builder.collect_result_nodes(result);
        }
        for result in stmt_results {
            builder.collect_result_edges(result);
        }
        builder
    }

    fn collect_result_nodes(&mut self, result: &StmtResult) {
        if let Some(success) = result.factual_success() {
            self.add_fact_node(&success.stmt, "fact", None);
            self.add_infer_nodes(&success.infers);
            self.collect_verified_by_nodes(&success.verified_by);
            return;
        }

        let Some(success) = result.non_factual_success() else {
            return;
        };
        match &success.stmt {
            Stmt::DefThmStmt(stmt) => self.add_theorem_nodes(stmt, &success.stmt),
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(stmt)) => {
                self.add_claim_nodes(stmt, &success.stmt)
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(_))
            | Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(_)) => {
                self.add_trust_nodes(&success.infers)
            }
            _ => {}
        }
        if let Some(verification) = success.theorem_verification.as_ref() {
            self.add_assumption_nodes(&verification.assumption_infers);
        }
        if let Some(ClaimVerificationResult::Forall(verification)) =
            success.claim_verification.as_ref()
        {
            self.add_assumption_nodes(&verification.assumption_infers);
        }
        for inside in &success.inside_results {
            self.collect_result_nodes(inside);
        }
    }

    fn collect_verified_by_nodes(&mut self, verified_by: &VerifiedByResult) {
        match verified_by {
            VerifiedByResult::BuiltinRule(result) => {
                for subgoal in &result.subgoals {
                    self.collect_result_nodes(subgoal);
                }
            }
            VerifiedByResult::Fact(result) => {
                self.add_cited_stmt_node(result.cite_what.as_ref());
            }
            VerifiedByResult::KnownForallInstantiation(result) => {
                self.add_cited_stmt_node(result.cite_what.as_ref());
                for requirement in &result.requirements {
                    self.add_requirement_source_nodes(requirement.result.as_ref());
                }
            }
            VerifiedByResult::VerifiedBys(result) => {
                for item in &result.cite_what {
                    self.collect_verified_bys_item_nodes(item);
                }
            }
            VerifiedByResult::ForallProof(result) => {
                self.add_assumption_nodes(&result.assumption_infers);
                for proved in &result.proves {
                    self.collect_result_nodes(proved.result.as_ref());
                }
            }
        }
    }

    fn collect_verified_bys_item_nodes(&mut self, item: &VerifiedBysEnum) {
        match item {
            VerifiedBysEnum::ByBuiltinRule(result) => {
                for subgoal in &result.subgoals {
                    self.collect_result_nodes(subgoal);
                }
            }
            VerifiedBysEnum::ByFact(result) => {
                self.add_cited_stmt_node(result.cite_what.as_ref());
            }
            VerifiedBysEnum::ByKnownForall(result) => {
                self.add_cited_stmt_node(result.result.cite_what.as_ref());
                for requirement in &result.result.requirements {
                    self.add_requirement_source_nodes(requirement.result.as_ref());
                }
            }
        }
    }

    fn add_infer_nodes(&mut self, infers: &InferResult) {
        for output in infers.store_fact_outputs() {
            let (fact, reason) = &output.itself_and_why_itself_is_stored;
            self.add_fact_node(fact, fact_kind_from_store_reason(reason), Some(reason));
            for inferred in &output.inferred_facts {
                self.add_fact_node(inferred, "inferred", Some(reason));
            }
        }
    }

    fn add_assumption_nodes(&mut self, infers: &InferResult) {
        for output in infers.store_fact_outputs() {
            if output.itself_and_why_itself_is_stored.1 == ParamDefWithType::store_reason() {
                continue;
            }
            self.add_fact_node(
                &output.itself_and_why_itself_is_stored.0,
                "assumption",
                Some(&output.itself_and_why_itself_is_stored.1),
            );
        }
    }

    fn add_trust_nodes(&mut self, infers: &InferResult) {
        for output in infers.store_fact_outputs() {
            let fact = &output.itself_and_why_itself_is_stored.0;
            let node_id = self.add_fact_node(
                fact,
                "trust",
                Some(&output.itself_and_why_itself_is_stored.1),
            );
            self.trust_node_by_line
                .insert(line_key(&fact.line_file()), node_id);
        }
    }

    fn add_requirement_source_nodes(&mut self, result: &StmtResult) {
        let _ = self.dependency_source_ids_from_result(result);
    }

    fn add_theorem_nodes(&mut self, stmt: &DefThmStmt, full_stmt: &Stmt) {
        let interface_fact: Fact = stmt.forall_fact.clone().into();
        let interface_line = line_key(&interface_fact.line_file());
        for name in &stmt.names {
            let theorem_id = theorem_id(name);
            self.ensure_node(
                theorem_id.clone(),
                "fact",
                name.to_string(),
                Some(&stmt.line_file),
                Some(&full_stmt.to_string()),
                Some("thm"),
                None,
            );
            self.theorem_node_by_line
                .insert(interface_line.clone(), theorem_id);
        }
    }

    fn add_claim_nodes(&mut self, stmt: &ClaimStmt, full_stmt: &Stmt) {
        let claim_id = claim_id(&stmt.line_file);
        self.ensure_node(
            claim_id.clone(),
            "fact",
            format!("claim@{}", line_label(&stmt.line_file)),
            Some(&stmt.line_file),
            Some(&full_stmt.to_string()),
            Some("claim"),
            None,
        );
        self.claim_node_by_line
            .insert(line_key(&stmt.fact.line_file()), claim_id);
    }

    fn add_cited_stmt_node(&mut self, stmt: &Stmt) -> Option<String> {
        match stmt {
            Stmt::Fact(fact) => {
                let line = line_key(&fact.line_file());
                if let Some(node_id) = self.theorem_node_by_line.get(&line) {
                    return Some(node_id.clone());
                }
                if let Some(node_id) = self.claim_node_by_line.get(&line) {
                    return Some(node_id.clone());
                }
                if let Some(node_id) = self.trust_node_by_line.get(&line) {
                    return Some(node_id.clone());
                }
                let node_id = fact_node_id(fact);
                self.node_index.contains_key(&node_id).then_some(node_id)
            }
            Stmt::DefThmStmt(def_thm) => {
                let name = def_thm.names.first()?;
                let node_id = theorem_id(name);
                self.ensure_node(
                    node_id.clone(),
                    "fact",
                    name.to_string(),
                    Some(&def_thm.line_file),
                    Some(&stmt.to_string()),
                    Some("thm"),
                    None,
                );
                Some(node_id)
            }
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(claim)) => {
                self.add_claim_nodes(claim, stmt);
                Some(claim_id(&claim.line_file))
            }
            _ => None,
        }
    }

    fn collect_result_edges(&mut self, result: &StmtResult) {
        if let Some(success) = result.factual_success() {
            let target_id = self.add_fact_node(&success.stmt, "fact", None);
            self.add_infer_edges(&success.infers);
            self.collect_verified_by_edges(&target_id, &success.verified_by);
            return;
        }

        let Some(success) = result.non_factual_success() else {
            return;
        };
        for inside in &success.inside_results {
            self.collect_result_edges(inside);
        }
        let Some(last_fact_id) = self.last_factual_result_node_id(&success.inside_results) else {
            return;
        };
        match &success.stmt {
            Stmt::DefThmStmt(stmt) => {
                for name in &stmt.names {
                    self.add_edge(&last_fact_id, &theorem_id(name), "proves");
                }
            }
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(stmt)) => {
                self.add_edge(&last_fact_id, &claim_id(&stmt.line_file), "proves");
            }
            _ => {}
        }
    }

    fn collect_verified_by_edges(&mut self, target_id: &str, verified_by: &VerifiedByResult) {
        match verified_by {
            VerifiedByResult::BuiltinRule(result) => {
                self.add_subgoal_edges(target_id, &result.subgoals);
            }
            VerifiedByResult::Fact(result) => {
                self.add_cited_stmt_edges(target_id, result.cite_what.as_ref());
            }
            VerifiedByResult::KnownForallInstantiation(result) => {
                self.add_known_forall_edges(target_id, result);
            }
            VerifiedByResult::VerifiedBys(result) => {
                for item in &result.cite_what {
                    self.add_verified_bys_item_edges(target_id, item);
                }
            }
            VerifiedByResult::ForallProof(result) => {
                for proved in &result.proves {
                    self.collect_result_edges(proved.result.as_ref());
                    if let Some(source_id) = self.primary_result_node_id(proved.result.as_ref()) {
                        self.add_edge(&source_id, target_id, "proves");
                    }
                }
            }
        }
    }

    fn add_verified_bys_item_edges(&mut self, target_id: &str, item: &VerifiedBysEnum) {
        match item {
            VerifiedBysEnum::ByBuiltinRule(result) => {
                self.add_subgoal_edges(target_id, &result.subgoals);
            }
            VerifiedBysEnum::ByFact(result) => {
                self.add_cited_stmt_edges(target_id, result.cite_what.as_ref());
            }
            VerifiedBysEnum::ByKnownForall(result) => {
                self.add_known_forall_edges(target_id, &result.result);
            }
        }
    }

    fn add_cited_stmt_edges(&mut self, target_id: &str, cited_stmt: &Stmt) {
        if let Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(definition)) = cited_stmt {
            self.add_definition_unfolding_edges(target_id, &definition.iff_facts);
            return;
        }
        if let Some(source_id) = self.add_cited_stmt_node(cited_stmt) {
            for source_id in self.main_chain_source_ids(&source_id) {
                self.add_edge(&source_id, target_id, "cites");
            }
        }
    }

    fn add_definition_unfolding_edges(&mut self, target_id: &str, requirements: &[Fact]) {
        for requirement in requirements {
            if let Some(source_id) = self.latest_matching_fact_node_id(target_id, requirement) {
                self.add_edge(&source_id, target_id, "unfolds");
            }
        }
    }

    fn latest_matching_fact_node_id(&self, target_id: &str, fact: &Fact) -> Option<String> {
        let target_index = self.node_index.get(target_id).copied()?;
        let target_text = canonical_fact_text(fact);
        self.nodes
            .iter()
            .take(target_index)
            .enumerate()
            .rev()
            .find_map(|(_, node)| {
                if node.kind != "fact" {
                    return None;
                }
                if node.fact_kind.as_deref() == Some("inferred") {
                    return None;
                }
                let statement = node.statement.as_ref()?;
                (canonical_fact_text_from_text(statement) == target_text).then_some(node.id.clone())
            })
    }

    fn add_known_forall_edges(&mut self, target_id: &str, result: &KnownForallInstantiationResult) {
        if let Some(source_id) = self.add_cited_stmt_node(result.cite_what.as_ref()) {
            self.add_edge(&source_id, target_id, "instantiates");
        }
        for requirement in &result.requirements {
            for source_id in self.dependency_source_ids_from_result(requirement.result.as_ref()) {
                for source_id in self.main_chain_source_ids(&source_id) {
                    self.add_edge(&source_id, target_id, "requires");
                }
            }
        }
    }

    fn add_subgoal_edges(&mut self, target_id: &str, subgoals: &[StmtResult]) {
        for subgoal in subgoals {
            self.collect_result_edges(subgoal);
            if let Some(source_id) = self.primary_result_node_id(subgoal) {
                for source_id in self.main_chain_source_ids(&source_id) {
                    self.add_edge(&source_id, target_id, "subgoal");
                }
            }
        }
    }

    fn dependency_source_ids_from_result(&mut self, result: &StmtResult) -> Vec<String> {
        if let Some(success) = result.factual_success() {
            let direct_id = fact_node_id(&success.stmt);
            if self.node_index.contains_key(&direct_id) {
                return vec![direct_id];
            }
            return self.dependency_source_ids_from_verified_by(&success.verified_by);
        }
        let Some(success) = result.non_factual_success() else {
            return vec![];
        };
        match &success.stmt {
            Stmt::DefThmStmt(stmt) => stmt
                .names
                .first()
                .map(|name| vec![theorem_id(name)])
                .unwrap_or_default(),
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(stmt)) => {
                vec![claim_id(&stmt.line_file)]
            }
            _ => vec![],
        }
    }

    fn dependency_source_ids_from_verified_by(
        &mut self,
        verified_by: &VerifiedByResult,
    ) -> Vec<String> {
        match verified_by {
            VerifiedByResult::BuiltinRule(result) => {
                self.dependency_source_ids_from_results(&result.subgoals)
            }
            VerifiedByResult::Fact(result) => self
                .add_cited_stmt_node(result.cite_what.as_ref())
                .into_iter()
                .collect(),
            VerifiedByResult::KnownForallInstantiation(result) => self
                .add_cited_stmt_node(result.cite_what.as_ref())
                .into_iter()
                .collect(),
            VerifiedByResult::VerifiedBys(result) => {
                let mut ids = vec![];
                for item in &result.cite_what {
                    let mut item_ids = match item {
                        VerifiedBysEnum::ByBuiltinRule(item) => {
                            self.dependency_source_ids_from_results(&item.subgoals)
                        }
                        VerifiedBysEnum::ByFact(item) => self
                            .add_cited_stmt_node(item.cite_what.as_ref())
                            .into_iter()
                            .collect(),
                        VerifiedBysEnum::ByKnownForall(item) => self
                            .add_cited_stmt_node(item.result.cite_what.as_ref())
                            .into_iter()
                            .collect(),
                    };
                    ids.append(&mut item_ids);
                }
                ids.sort();
                ids.dedup();
                ids
            }
            VerifiedByResult::ForallProof(result) => result
                .proves
                .iter()
                .flat_map(|proved| self.dependency_source_ids_from_result(proved.result.as_ref()))
                .collect(),
        }
    }

    fn dependency_source_ids_from_results(&mut self, results: &[StmtResult]) -> Vec<String> {
        let mut ids = vec![];
        for result in results {
            ids.extend(self.dependency_source_ids_from_result(result));
        }
        ids.sort();
        ids.dedup();
        ids
    }

    fn main_chain_source_ids(&self, source_id: &str) -> Vec<String> {
        let Some(index) = self.node_index.get(source_id).copied() else {
            return vec![];
        };
        let node = &self.nodes[index];
        if node.fact_kind.as_deref() != Some("inferred") {
            return vec![source_id.to_string()];
        }
        let mut parents = self
            .edges
            .iter()
            .filter(|edge| edge.to == source_id && edge.kind == "infers")
            .flat_map(|edge| self.main_chain_source_ids(&edge.from))
            .collect::<Vec<_>>();
        parents.sort();
        parents.dedup();
        parents
    }

    fn add_infer_edges(&mut self, infers: &InferResult) {
        for output in infers.store_fact_outputs() {
            let primary = &output.itself_and_why_itself_is_stored.0;
            let source_id = fact_node_id(primary);
            if !self.node_index.contains_key(&source_id) {
                continue;
            }
            for inferred in &output.inferred_facts {
                let target_id = self.add_fact_node(inferred, "inferred", None);
                self.add_edge(&source_id, &target_id, "infers");
            }
        }
    }

    fn primary_result_node_id(&mut self, result: &StmtResult) -> Option<String> {
        if let Some(success) = result.factual_success() {
            return Some(self.add_fact_node(&success.stmt, "fact", None));
        }
        let success = result.non_factual_success()?;
        match &success.stmt {
            Stmt::DefThmStmt(stmt) => stmt.names.first().map(|name| theorem_id(name)),
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(stmt)) => Some(claim_id(&stmt.line_file)),
            _ => None,
        }
    }

    fn last_factual_result_node_id(&mut self, results: &[StmtResult]) -> Option<String> {
        for result in results.iter().rev() {
            if let Some(success) = result.factual_success() {
                return Some(self.add_fact_node(&success.stmt, "fact", None));
            }
            if let Some(success) = result.non_factual_success() {
                if let Some(node_id) = self.last_factual_result_node_id(&success.inside_results) {
                    return Some(node_id);
                }
            }
        }
        None
    }

    fn add_fact_node(&mut self, fact: &Fact, fact_kind: &str, reason: Option<&String>) -> String {
        let node_id = fact_node_id(fact);
        let label = format!(
            "{} · {}",
            line_label(&fact.line_file()),
            compact_text(&fact.to_string())
        );
        self.ensure_node(
            node_id.clone(),
            "fact",
            label,
            Some(&fact.line_file()),
            Some(&fact.to_string()),
            Some(fact_kind),
            reason,
        );
        node_id
    }

    fn ensure_node(
        &mut self,
        id: String,
        kind: &str,
        label: String,
        line_file: Option<&LineFile>,
        statement: Option<&String>,
        fact_kind: Option<&str>,
        reason: Option<&String>,
    ) {
        if let Some(index) = self.node_index.get(&id).copied() {
            let node = &mut self.nodes[index];
            if node.statement.is_none() {
                node.statement = statement.cloned();
            }
            if node.line_file.is_none() {
                node.line_file = line_file.cloned();
            }
            if node.reason.is_none() {
                node.reason = reason.cloned();
            }
            if let Some(fact_kind) = fact_kind {
                if node.fact_kind.as_deref() == Some("reference") || node.fact_kind.is_none() {
                    node.fact_kind = Some(fact_kind.to_string());
                }
            }
            return;
        }
        self.node_index.insert(id.clone(), self.nodes.len());
        self.nodes.push(FactGraphNode {
            id,
            kind: kind.to_string(),
            label,
            fact_kind: fact_kind.map(|kind| kind.to_string()),
            line_file: line_file.cloned(),
            statement: statement.cloned(),
            reason: reason.cloned(),
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
        self.edges.push(FactGraphEdge {
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
        JsonValue::Array(self.edges.iter().map(FactGraphEdge::json_value).collect())
    }

    fn summary_json(&self) -> JsonValue {
        let facts = self
            .nodes
            .iter()
            .filter(|node| {
                node.kind == "fact"
                    && node.fact_kind.as_deref() != Some("thm")
                    && node.fact_kind.as_deref() != Some("claim")
            })
            .count();
        let theorems = self
            .nodes
            .iter()
            .filter(|node| node.fact_kind.as_deref() == Some("thm"))
            .count();
        let claims = self
            .nodes
            .iter()
            .filter(|node| node.fact_kind.as_deref() == Some("claim"))
            .count();
        let trust_facts = self
            .nodes
            .iter()
            .filter(|node| node.fact_kind.as_deref() == Some("trust"))
            .count();
        let longest_chain = self.longest_chain();
        JsonValue::Object(vec![
            ("nodes".to_string(), JsonValue::Number(self.nodes.len())),
            ("edges".to_string(), JsonValue::Number(self.edges.len())),
            ("facts".to_string(), JsonValue::Number(facts)),
            ("theorems".to_string(), JsonValue::Number(theorems)),
            ("claims".to_string(), JsonValue::Number(claims)),
            ("trust_facts".to_string(), JsonValue::Number(trust_facts)),
            (
                "longest_chain_nodes".to_string(),
                JsonValue::Number(longest_chain.len()),
            ),
        ])
    }

    fn empty_summary_json() -> JsonValue {
        JsonValue::Object(vec![
            ("nodes".to_string(), JsonValue::Number(0)),
            ("edges".to_string(), JsonValue::Number(0)),
            ("facts".to_string(), JsonValue::Number(0)),
            ("theorems".to_string(), JsonValue::Number(0)),
            ("claims".to_string(), JsonValue::Number(0)),
            ("trust_facts".to_string(), JsonValue::Number(0)),
            ("longest_chain_nodes".to_string(), JsonValue::Number(0)),
        ])
    }

    fn longest_chain_json(&self) -> JsonValue {
        let node_ids = self.longest_chain();
        JsonValue::Object(vec![
            ("node_count".to_string(), JsonValue::Number(node_ids.len())),
            (
                "selection".to_string(),
                JsonValue::JsonString(
                    "facts, claims, and theorems; inferred facts are compressed into edges"
                        .to_string(),
                ),
            ),
            (
                "node_ids".to_string(),
                JsonValue::Array(node_ids.into_iter().map(JsonValue::JsonString).collect()),
            ),
        ])
    }

    fn empty_longest_chain_json() -> JsonValue {
        JsonValue::Object(vec![
            ("node_count".to_string(), JsonValue::Number(0)),
            (
                "selection".to_string(),
                JsonValue::JsonString(
                    "facts, claims, and theorems; inferred facts are compressed into edges"
                        .to_string(),
                ),
            ),
            ("node_ids".to_string(), JsonValue::Array(vec![])),
        ])
    }

    fn longest_chain(&self) -> Vec<String> {
        let mut outgoing: HashMap<String, Vec<String>> = HashMap::new();
        for edge in &self.edges {
            let Some(from_index) = self.node_index.get(&edge.from).copied() else {
                continue;
            };
            let Some(to_index) = self.node_index.get(&edge.to).copied() else {
                continue;
            };
            if !fact_graph_node_belongs_to_main_chain(&self.nodes[from_index])
                || !fact_graph_node_belongs_to_main_chain(&self.nodes[to_index])
            {
                continue;
            }
            outgoing
                .entry(edge.from.clone())
                .or_default()
                .push(edge.to.clone());
        }
        let mut memo = HashMap::new();
        let mut visiting = HashSet::new();
        let mut longest = vec![];
        for node in &self.nodes {
            if !fact_graph_node_belongs_to_main_chain(node) {
                continue;
            }
            let candidate =
                longest_chain_from(node.id.as_str(), &outgoing, &mut memo, &mut visiting);
            if candidate.len() > longest.len() {
                longest = candidate;
            }
        }
        longest
    }

    fn mermaid(&self) -> String {
        let mut lines = vec!["flowchart LR".to_string()];
        for node in &self.nodes {
            lines.push(format!(
                "    {}{}",
                mermaid_id(&node.id),
                mermaid_node_shape(node)
            ));
        }
        for edge in &self.edges {
            let label = if edge.count > 1 {
                format!("{} x{}", edge.kind, edge.count)
            } else {
                edge.kind.clone()
            };
            lines.push(format!(
                "    {} -->|{}| {}",
                mermaid_id(&edge.from),
                label,
                mermaid_id(&edge.to)
            ));
        }
        lines.join("\n")
    }
}

impl FactGraphNode {
    fn json_value(&self, include_source: bool) -> JsonValue {
        let mut fields = vec![
            ("id".to_string(), JsonValue::JsonString(self.id.clone())),
            ("kind".to_string(), JsonValue::JsonString(self.kind.clone())),
            (
                "label".to_string(),
                JsonValue::JsonString(self.label.clone()),
            ),
            ("defined".to_string(), JsonValue::Bool(true)),
        ];
        if let Some(fact_kind) = &self.fact_kind {
            fields.push((
                "fact_kind".to_string(),
                JsonValue::JsonString(fact_kind.clone()),
            ));
        }
        if let Some(line_file) = &self.line_file {
            fields.push(("line".to_string(), fact_graph_line_json_value(line_file)));
            if include_source && !is_default_line_file(line_file) {
                fields.push((
                    "source".to_string(),
                    JsonValue::JsonString(line_file.1.as_ref().to_string()),
                ));
            }
        }
        if let Some(statement) = &self.statement {
            fields.push((
                "statement".to_string(),
                JsonValue::JsonString(strip_free_param_numeric_tags_in_display(statement)),
            ));
        }
        if let Some(reason) = &self.reason {
            fields.push((
                "store_reason".to_string(),
                JsonValue::JsonString(reason.clone()),
            ));
        }
        JsonValue::Object(fields)
    }
}

impl FactGraphEdge {
    fn json_value(&self) -> JsonValue {
        JsonValue::Object(vec![
            ("from".to_string(), JsonValue::JsonString(self.from.clone())),
            ("to".to_string(), JsonValue::JsonString(self.to.clone())),
            ("kind".to_string(), JsonValue::JsonString(self.kind.clone())),
            ("count".to_string(), JsonValue::Number(self.count)),
        ])
    }
}

fn longest_chain_from(
    node_id: &str,
    outgoing: &HashMap<String, Vec<String>>,
    memo: &mut HashMap<String, Vec<String>>,
    visiting: &mut HashSet<String>,
) -> Vec<String> {
    if let Some(chain) = memo.get(node_id) {
        return chain.clone();
    }
    if !visiting.insert(node_id.to_string()) {
        return vec![];
    }
    let mut best_tail = vec![];
    if let Some(next_nodes) = outgoing.get(node_id) {
        for next in next_nodes {
            let candidate = longest_chain_from(next, outgoing, memo, visiting);
            if candidate.len() > best_tail.len() {
                best_tail = candidate;
            }
        }
    }
    visiting.remove(node_id);
    let mut chain = vec![node_id.to_string()];
    chain.append(&mut best_tail);
    memo.insert(node_id.to_string(), chain.clone());
    chain
}

fn fact_kind_from_store_reason(reason: &str) -> &'static str {
    if reason == TrustStmt::store_reason() || reason == TrustHaveStmt::store_reason() {
        "trust"
    } else if reason == ClaimStmt::store_reason() {
        "claim_result"
    } else {
        "fact"
    }
}

fn fact_node_id(fact: &Fact) -> String {
    format!("fact:{}:{}", line_key(&fact.line_file()), fact)
}

fn theorem_id(name: &str) -> String {
    format!("thm:{}", name)
}

fn claim_id(line_file: &LineFile) -> String {
    format!("claim:{}", line_key(line_file))
}

fn line_key(line_file: &LineFile) -> String {
    if is_default_line_file(line_file) {
        "unknown".to_string()
    } else {
        format!("{}:{}", line_file.1.as_ref(), line_file.0)
    }
}

fn line_label(line_file: &LineFile) -> String {
    if is_default_line_file(line_file) {
        "?".to_string()
    } else {
        line_file.0.to_string()
    }
}

fn compact_text(text: &str) -> String {
    let compact = text.split_whitespace().collect::<Vec<_>>().join(" ");
    let visible = compact.chars().take(112).collect::<String>();
    if visible.len() < compact.len() {
        format!("{}…", visible)
    } else {
        visible
    }
}

fn canonical_fact_text(fact: &Fact) -> String {
    canonical_fact_text_from_text(&fact.to_string())
}

fn canonical_fact_text_from_text(text: &str) -> String {
    strip_free_param_numeric_tags_in_display(text)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn fact_graph_node_belongs_to_main_chain(node: &FactGraphNode) -> bool {
    node.fact_kind.as_deref() != Some("inferred")
}

fn fact_graph_line_json_value(line_file: &LineFile) -> JsonValue {
    if is_default_line_file(line_file) {
        JsonValue::Null
    } else {
        JsonValue::Number(line_file.0)
    }
}

fn mermaid_id(id: &str) -> String {
    let mut output = "n_".to_string();
    for character in id.chars() {
        if character.is_ascii_alphanumeric() {
            output.push(character);
        } else {
            output.push('_');
        }
    }
    output
}

fn mermaid_node_shape(node: &FactGraphNode) -> String {
    let label = node.label.replace('"', "'");
    match node.fact_kind.as_deref() {
        Some("thm") => format!("[[\"{}\"]]", label),
        Some("claim") => format!("([\"{}\"])", label),
        _ => format!("[/\"{}\"/]", label),
    }
}

#[cfg(test)]
mod tests {
    use super::run_fact_graph_for_code;

    fn fact_graph_output(source: &'static str) -> String {
        std::thread::Builder::new()
            .name("fact_graph_output_large_stack".to_string())
            .stack_size(64 * 1024 * 1024)
            .spawn(move || run_fact_graph_for_code(source, "fact_graph_test", true).1)
            .expect("spawn fact graph output test")
            .join()
            .expect("fact graph output test panicked")
    }

    #[test]
    fn fact_graph_uses_runtime_fact_evidence_without_definition_nodes() {
        let output = fact_graph_output(
            "abstract_prop p(x)\nabstract_prop q(x)\ntrust forall x R:\n    $p(x)\n    =>:\n        $q(x)\nthm fact_graph_chain:\n    ? forall x R:\n        $p(x)\n        =>:\n            $q(x)\n    $q(x)\nclaim:\n    ? forall x R:\n        $p(x)\n        =>:\n            $q(x)\n    $q(x)\n",
        );

        assert!(output.contains(r#""graph": "litex-fact-graph""#));
        assert!(output.contains(r#""fact_kind": "thm""#));
        assert!(output.contains(r#""fact_kind": "claim""#));
        assert!(output.contains(r#""fact_kind": "trust""#));
        assert!(output.contains(r#""kind": "requires""#));
        assert!(output.contains(r#""longest_chain""#));
        assert!(!output.contains(r#""kind": "prop""#));
        assert!(!output.contains(r#""kind": "fn""#));
    }

    #[test]
    fn fact_graph_flattens_definition_dependencies_into_fact_edges() {
        let output = fact_graph_output(
            "abstract_prop p(x)\nabstract_prop q(x)\nprop packed(x R):\n    $p(x)\n    $q(x)\nthm packed_from_facts:\n    ? forall x R:\n        $p(x)\n        $q(x)\n        =>:\n            $packed(x)\n    $packed(x)\n",
        );

        assert!(output.contains(r#""kind": "unfolds""#));
        assert!(output.contains(r#""selection": "facts, claims, and theorems; inferred facts are compressed into edges""#));
        assert!(!output.contains(r#""kind": "prop""#));
    }
}
