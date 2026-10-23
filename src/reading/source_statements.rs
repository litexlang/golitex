//! Match retained proof-body results to the exact original body AST.
//!
//! This is a reading index, not an execution environment. Bodies come from
//! typed statement fields and are paired only with their owning result's
//! ordered proof_steps. Synthetic derivations remain inline and explicitly
//! lack a source mapping rather than borrowing a nearby line.

use super::*;
use crate::ast::stmt::{ByStmt, DefinitionStmt, ProofBlockStmt, ReleaseAndExpandStmt, WitnessStmt};

#[derive(Default)]
pub(super) struct SourceStatements {
    nodes: BTreeMap<usize, Stmt>,
    spans: BTreeMap<usize, (usize, usize)>,
    current: Option<usize>,
    gaps: BTreeSet<String>,
    scopes: Vec<String>,
    node_scopes: BTreeMap<usize, Vec<String>>,
    named_bindings: BTreeMap<(String, String), String>,
    declarations: BTreeSet<String>,
}

impl Capture {
    pub fn prepare_source_statements(&mut self, block: &TokenBlock) {
        self.source_statements.spans.clear();
        self.source_statements.current = None;
        self.source_statements.gaps.clear();
        self.source_statements.scopes = vec![format!("file:{}", self.current_source)];
        collect_spans(block, &mut self.source_statements.spans);
    }

    pub fn begin_ast_statement(
        &mut self,
        statement: &Stmt,
        runtime: &Runtime,
    ) -> Option<(String, usize)> {
        if !self.capturing_ast {
            return None;
        }
        let saved = (self.current_statement.clone(), self.current_line);
        let line = crate::json_output::reading_statement_source_line(statement)
            .map(|source| source.line)
            .unwrap_or(self.current_line);
        let index = self.statements.len();
        let id = format!("statement{index}");
        let (start, end) = self
            .source_statements
            .spans
            .get(&line)
            .copied()
            .unwrap_or_default();
        self.statements.push(object(vec![
            ("id", text(&id)),
            ("source_statement_id", text(&id)),
            ("source_id", text(&self.current_source)),
            (
                "parent_statement_id",
                if saved.0.is_empty() {
                    JsonValue::Null
                } else {
                    text(&saved.0)
                },
            ),
            ("line", JsonValue::Number(line as f64)),
            ("start_byte", JsonValue::Number(start as f64)),
            ("end_byte", JsonValue::Number(end as f64)),
            ("text", text(&statement.reading_text())),
            ("source_text", text(&statement.readable_string())),
            (
                "mathematics",
                super::mathematical_meaning::statement_math(statement, runtime, self.language),
            ),
            ("origin", text(statement_origin(statement))),
            ("status", text("not_exported")),
            ("produced_fact_ids", JsonValue::Array(Vec::new())),
            ("cited_fact_ids", JsonValue::Array(Vec::new())),
            ("declaration_dependencies", JsonValue::Array(Vec::new())),
            ("evidence", object(vec![("kind", text("unavailable"))])),
            (
                "coverage",
                object(vec![
                    ("evidence", text("unavailable")),
                    ("source_mapping", text("unavailable")),
                    ("occurrences", text("pending")),
                ]),
            ),
        ]));
        self.source_statements
            .nodes
            .insert(index, statement.clone());
        self.source_statements
            .node_scopes
            .insert(index, self.source_statements.scopes.clone());
        self.current_statement = id;
        self.current_line = line;
        Some(saved)
    }

    pub fn end_ast_statement(&mut self, saved: Option<(String, usize)>, syntax: &JsonValue) {
        if let Some((statement, line)) = saved {
            // Reuse the typed AST projection, stopping before facts, objects
            // or the bodies of definitions. This describes source syntax,
            // independently of whether its execution produced evidence.
            let mut node = syntax;
            let mut path = Vec::new();
            while matches!(
                field_text(node, "type").as_str(),
                "Stmt"
                    | "DefinitionStmt"
                    | "DefineObjStmt"
                    | "TrustBoundaryStmt"
                    | "ReleaseAndExpandStmt"
                    | "ByStmt"
                    | "RegisterStmt"
                    | "WitnessStmt"
                    | "ProofBlockStmt"
                    | "CommandStmt"
            ) {
                path.push(field_text(node, "variant"));
                let Some(child) = node
                    .as_object()
                    .ok()
                    .and_then(|fields| fields.get("fields"))
                    .and_then(|fields| fields.as_object().ok())
                    .and_then(|fields| fields.get("0"))
                else {
                    break;
                };
                node = child;
            }
            if let Some(JsonValue::Object(fields)) = self
                .current_statement
                .strip_prefix("statement")
                .and_then(|id| id.parse::<usize>().ok())
                .and_then(|index| self.statements.get_mut(index))
            {
                fields.insert("statement_kind".into(), text(&path.join(".")));
            }
            self.current_statement = statement;
            self.current_line = line;
        }
    }

    pub fn ast_body(&mut self, field: &str, body: &[Stmt], runtime: &Runtime) -> JsonValue {
        // Plain predicate/theorem names have no IdentifierId. Their source
        // namespace is the parser's explicit body scope. This index is used
        // only for concept navigation; it cannot create facts or proof edges.
        if self.capturing_ast {
            self.source_statements.scopes.push(format!(
                "{}:{}:{field}",
                self.current_source, self.current_statement
            ));
        }
        let result = JsonValue::Array(
            body.iter()
                .map(|statement| capture_ast__stmt__Stmt(statement, self, runtime))
                .collect(),
        );
        if self.capturing_ast {
            self.source_statements.scopes.pop();
        }
        result
    }

    pub fn named_source_key(&self, name: &str) -> String {
        self.source_statements
            .scopes
            .iter()
            .rev()
            .find_map(|scope| {
                self.source_statements
                    .named_bindings
                    .get(&(scope.clone(), name.into()))
                    .cloned()
            })
            .unwrap_or_else(|| format!("named:{}:{name}", self.current_path))
    }

    pub fn register_named_binding(&mut self, name: &str) {
        let Some(scope) = self.source_statements.scopes.last() else {
            return;
        };
        let key = if self.source_statements.scopes.len() == 1 {
            format!("named:{}:{name}", self.current_path)
        } else {
            format!("named:{}:{scope}:{name}", self.current_path)
        };
        self.source_statements
            .named_bindings
            .insert((scope.clone(), name.into()), key);
    }

    pub fn enter_location(&mut self, line: &SourceLine) -> (String, usize, Vec<String>) {
        let saved = (
            self.current_path.clone(),
            self.current_line,
            self.source_statements.scopes.clone(),
        );
        self.current_path = self.logical_path(&line.origin.display_path());
        self.current_line = line.line;
        if let Some((index, _)) = self.source_statements.nodes.iter().find(|(_, statement)| {
            crate::json_output::reading_statement_source_line(statement)
                .is_some_and(|source| source == line)
        }) {
            if let Some(scopes) = self.source_statements.node_scopes.get(index) {
                self.source_statements.scopes = scopes.clone();
            }
        }
        saved
    }

    pub fn leave_location(&mut self, saved: (String, usize, Vec<String>)) {
        self.current_path = saved.0;
        self.current_line = saved.1;
        self.source_statements.scopes = saved.2;
    }

    pub fn declaration_reference(&mut self, line: &SourceLine, kind: &str) -> JsonValue {
        let source = self
            .source_statements
            .nodes
            .iter()
            .find(|(_, statement)| {
                crate::json_output::reading_statement_source_line(statement)
                    .is_some_and(|location| location == line)
            })
            .map(|(index, _)| format!("statement{index}"));
        if !self.capturing_ast && self.source_snapshot_depth == 0 {
            if let Some(id) = &source {
                if id != &self.current_statement {
                    self.source_statements.declarations.insert(id.clone());
                }
            }
        }
        object(vec![
            ("kind", text("declaration_reference")),
            ("declaration_kind", text(kind)),
            ("source_id", text(&self.source_id(&line.origin))),
            ("line", JsonValue::Number(line.line as f64)),
            (
                "statement_id",
                source.map(|id| text(&id)).unwrap_or(JsonValue::Null),
            ),
        ])
    }

    /// A typed signature proof certifies this declaration lookup. Ordinary
    /// occurrences alone must never create a mathematical dependency edge.
    pub fn signature_declaration(
        &mut self,
        predicate: &AtomicName,
        runtime: &Runtime,
    ) -> JsonValue {
        let reference = self.atomic_name(predicate, runtime);
        let id = field_text(&reference, "symbol_id");
        let definition = self
            .symbols
            .get(&id)
            .map(|symbol| field_text(symbol, "definition_statement_id"))
            .unwrap_or_default();
        let line = self
            .statements
            .iter()
            .find(|statement| field_text(statement, "id") == definition)
            .and_then(|statement| {
                field_text(statement, "source_statement_id")
                    .strip_prefix("statement")
                    .and_then(|index| index.parse::<usize>().ok())
            })
            .and_then(|index| self.source_statements.nodes.get(&index))
            .and_then(crate::json_output::reading_statement_source_line)
            .cloned();
        match line {
            Some(line) => self.declaration_reference(&line, "predicate_signature"),
            None => self.unavailable("predicate_declaration"),
        }
    }

    pub fn capture_source_result(
        &mut self,
        source_index: usize,
        result: &ExecStmtResult,
        runtime: &Runtime,
    ) -> JsonValue {
        let source_id = field_text(&self.statements[source_index], "id");
        let record_index = if field_text(&self.statements[source_index], "status") == "not_exported"
        {
            source_index
        } else {
            // Enumeration/induction can execute one source body in several
            // actual local contexts. Keep those executions separate.
            let index = self.statements.len();
            let mut instance = self.statements[source_index].clone();
            if let JsonValue::Object(fields) = &mut instance {
                fields.insert("id".into(), text(&format!("{source_id}@{index}")));
            }
            self.statements.push(instance);
            index
        };
        let id = field_text(&self.statements[record_index], "id");
        let previous_statement = std::mem::replace(&mut self.current_statement, id.clone());
        let previous_node = self.source_statements.current.replace(source_index);
        let previous_source_scopes = std::mem::replace(
            &mut self.source_statements.scopes,
            self.source_statements
                .node_scopes
                .get(&source_index)
                .cloned()
                .unwrap_or_default(),
        );
        let previous_root = std::mem::replace(&mut self.root_scope, self.current_scope.clone());
        let previous_line = self.current_line;
        self.current_line = number_field(&self.statements[source_index], "line");
        let previous_branch = self.proof_branch.take();
        let previous_part = std::mem::take(&mut self.proof_part);
        let previous_citations = std::mem::take(&mut self.citations);
        let previous_stores = std::mem::take(&mut self.stores);
        let previous_missing = std::mem::take(&mut self.missing);
        let previous_gaps = std::mem::take(&mut self.source_statements.gaps);
        let previous_declarations = std::mem::take(&mut self.source_statements.declarations);
        let previous_rules = std::mem::take(&mut self.statement_rules);
        let previous_wd = std::mem::take(&mut self.wd_uses);

        let evidence = capture_execute__exec_stmt_result__ExecStmtResult(result, self, runtime);
        let stores = if result.is_failed() {
            Vec::new()
        } else {
            self.stores.iter().cloned().collect()
        };
        let citations = self
            .citations
            .difference(&self.stores)
            .cloned()
            .collect::<Vec<_>>();
        if let JsonValue::Object(fields) = &mut self.statements[record_index] {
            fields.insert("scope_id".into(), text(&self.root_scope));
            fields.insert(
                "status".into(),
                text(if result.is_failed() {
                    "rejected"
                } else {
                    "accepted"
                }),
            );
            fields.insert("produced_fact_ids".into(), strings(&stores));
            fields.insert("cited_fact_ids".into(), strings(&citations));
            fields.insert(
                "declaration_dependencies".into(),
                strings(
                    &self
                        .source_statements
                        .declarations
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>(),
                ),
            );
            fields.insert(
                "parent_statement_id".into(),
                if previous_statement.is_empty() {
                    JsonValue::Null
                } else {
                    text(&previous_statement)
                },
            );
            fields.insert("evidence".into(), evidence);
            fields.insert(
                "well_definedness_ids".into(),
                strings(&self.wd_uses.iter().cloned().collect::<Vec<_>>()),
            );
            fields.insert(
                "rule_ids".into(),
                strings(&self.statement_rules.iter().cloned().collect::<Vec<_>>()),
            );
            fields.insert(
                "coverage".into(),
                object(vec![
                    (
                        "evidence",
                        text(if self.missing.is_empty() {
                            "complete"
                        } else {
                            "partial"
                        }),
                    ),
                    (
                        "source_mapping",
                        text(if self.source_statements.gaps.is_empty() {
                            "complete"
                        } else {
                            "partial"
                        }),
                    ),
                    (
                        "missing_source_mappings",
                        strings(
                            &self
                                .source_statements
                                .gaps
                                .iter()
                                .cloned()
                                .collect::<Vec<_>>(),
                        ),
                    ),
                    ("occurrences", text("pending")),
                    (
                        "missing_types",
                        strings(&self.missing.iter().cloned().collect::<Vec<_>>()),
                    ),
                ]),
            );
        }
        self.citations.extend(previous_citations);
        self.stores = previous_stores;
        self.missing.extend(previous_missing);
        self.source_statements.gaps.extend(previous_gaps);
        self.source_statements
            .declarations
            .extend(previous_declarations);
        self.statement_rules.extend(previous_rules);
        self.wd_uses.extend(previous_wd);
        self.current_statement = previous_statement;
        self.source_statements.current = previous_node;
        self.source_statements.scopes = previous_source_scopes;
        self.root_scope = previous_root;
        self.current_line = previous_line;
        self.proof_branch = previous_branch;
        self.proof_part = previous_part;
        object(vec![
            ("kind", text("statement_reference")),
            ("statement_id", text(&id)),
        ])
    }

    pub fn proof_steps(
        &mut self,
        owner: &str,
        steps: &[ExecStmtResult],
        runtime: &Runtime,
    ) -> JsonValue {
        let body = self
            .source_statements
            .current
            .and_then(|index| self.source_statements.nodes.get(&index))
            .and_then(|statement| {
                statement.reading_proof_body(owner, self.proof_branch, &self.proof_part)
            })
            .map(<[Stmt]>::to_vec);
        if let Some(body) = body.filter(|body| body.len() == steps.len()) {
            let mut output = Vec::with_capacity(steps.len());
            for (statement, result) in body.iter().zip(steps) {
                let source = self
                    .source_statements
                    .nodes
                    .iter()
                    .find(|(_, source)| *source == statement)
                    .map(|(index, _)| *index);
                if let Some(index) = source {
                    output.push(self.capture_source_result(index, result, runtime));
                } else {
                    self.source_statements.gaps.insert(owner.into());
                    output.push(capture_execute__exec_stmt_result__ExecStmtResult(
                        result, self, runtime,
                    ));
                }
            }
            JsonValue::Array(output)
        } else {
            if !steps.is_empty() {
                self.source_statements.gaps.insert(owner.into());
            }
            JsonValue::Array(
                steps
                    .iter()
                    .map(|result| {
                        capture_execute__exec_stmt_result__ExecStmtResult(result, self, runtime)
                    })
                    .collect(),
            )
        }
    }

    pub fn finish_source_statements(&mut self, first: usize, mapped: bool) {
        let mut unmapped = false;
        for record in self.statements.iter_mut().skip(first) {
            if let JsonValue::Object(fields) = record {
                if fields.get("status").and_then(|value| value.as_str().ok())
                    == Some("not_exported")
                {
                    unmapped = true;
                }
                if let Some(JsonValue::Object(mut coverage)) = fields.get("coverage").cloned() {
                    coverage.insert(
                        "occurrences".into(),
                        text(if mapped { "complete" } else { "partial" }),
                    );
                    fields.insert("coverage".into(), JsonValue::Object(coverage));
                }
            }
        }
        if unmapped {
            if let JsonValue::Object(fields) = &mut self.statements[first] {
                if let Some(JsonValue::Object(mut coverage)) = fields.get("coverage").cloned() {
                    coverage.insert("source_mapping".into(), text("partial"));
                    fields.insert("coverage".into(), JsonValue::Object(coverage));
                }
            }
        }
    }

    pub fn annotate_trust_origins(&mut self) -> JsonValue {
        let mut origins = BTreeMap::new();
        let mut edges = BTreeMap::<String, BTreeSet<String>>::new();
        for statement in &self.statements {
            let id = field_text(statement, "id");
            let origin = field_text(statement, "origin");
            if field_text(statement, "status") == "accepted" && origin != "checked" {
                origins.insert(id.clone(), origin);
            }
            let mut dependencies = string_list(statement, "declaration_dependencies");
            for fact_id in string_list(statement, "cited_fact_ids") {
                if let Some(fact) = self.facts.get(&fact_id) {
                    let producer = field_text(fact, "producer_statement_id");
                    if !producer.is_empty() && producer != id {
                        dependencies.insert(producer);
                    }
                }
            }
            edges.insert(id, dependencies);
        }
        // Iterative postorder avoids call-stack growth on a long textbook.
        let mut resolved = BTreeMap::<String, BTreeSet<String>>::new();
        for start in edges.keys() {
            let mut active = BTreeSet::new();
            let mut stack = vec![(start.clone(), false)];
            while let Some((id, closing)) = stack.pop() {
                if resolved.contains_key(&id) {
                    continue;
                }
                if closing {
                    let mut dependencies = BTreeSet::new();
                    if origins.contains_key(&id) {
                        dependencies.insert(id.clone());
                    }
                    for target in edges.get(&id).into_iter().flatten() {
                        if let Some(found) = resolved.get(target) {
                            dependencies.extend(found.iter().cloned());
                        }
                    }
                    resolved.insert(id.clone(), dependencies);
                    active.remove(&id);
                } else if active.insert(id.clone()) {
                    stack.push((id.clone(), true));
                    for target in edges.get(&id).into_iter().flatten().rev() {
                        if !active.contains(target) && !resolved.contains_key(target) {
                            stack.push((target.clone(), false));
                        }
                    }
                }
            }
        }
        for statement in &mut self.statements {
            let id = field_text(statement, "id");
            if let JsonValue::Object(fields) = statement {
                fields.insert(
                    "trust_dependencies".into(),
                    strings(
                        &resolved
                            .get(&id)
                            .cloned()
                            .unwrap_or_default()
                            .into_iter()
                            .collect::<Vec<_>>(),
                    ),
                );
            }
        }
        object(vec![
            (
                "user_assumptions",
                strings(
                    &origins
                        .iter()
                        .filter(|(_, origin)| origin.as_str() == "user_trust")
                        .map(|(id, _)| id.clone())
                        .collect::<Vec<_>>(),
                ),
            ),
            (
                "axioms",
                strings(
                    &origins
                        .iter()
                        .filter(|(_, origin)| origin.as_str() != "user_trust")
                        .map(|(id, _)| id.clone())
                        .collect::<Vec<_>>(),
                ),
            ),
        ])
    }
}

fn string_list(value: &JsonValue, key: &str) -> BTreeSet<String> {
    value
        .as_object()
        .ok()
        .and_then(|fields| fields.get(key))
        .and_then(|value| value.as_array().ok())
        .into_iter()
        .flatten()
        .filter_map(|value| value.as_str().ok().map(str::to_owned))
        .collect()
}

fn number_field(value: &JsonValue, key: &str) -> usize {
    value
        .as_object()
        .ok()
        .and_then(|fields| fields.get(key))
        .and_then(|value| value.as_u64().ok())
        .unwrap_or_default() as usize
}

fn collect_spans(block: &TokenBlock, output: &mut BTreeMap<usize, (usize, usize)>) {
    let mut tokens = BTreeMap::new();
    collect_tokens(block, &mut tokens);
    let start = tokens
        .values()
        .flatten()
        .map(|(_, start, _)| *start)
        .min()
        .unwrap_or_default();
    let end = tokens
        .values()
        .flatten()
        .map(|(_, _, end)| *end)
        .max()
        .unwrap_or(start);
    output.insert(block.line, (start, end));
    for child in &block.body {
        collect_spans(child, output);
    }
}

fn statement_origin(statement: &Stmt) -> &str {
    match statement {
        Stmt::Trust(_) => "user_trust",
        Stmt::Definition(DefinitionStmt::AxiomStmt(_)) => "axiom",
        Stmt::ReleaseAndExpand(
            ReleaseAndExpandStmt::ReleaseZornLemmaStmt(_)
            | ReleaseAndExpandStmt::ReleaseAxiomOfChoiceStmt(_)
            | ReleaseAndExpandStmt::ReleaseRegularityAxiomStmt(_),
        ) => "axiom_release",
        _ => "checked",
    }
}

// These are the bodies the corresponding execution owners pass to
// run_proof_body_stmts. No source spelling or localized output is matched.
impl Stmt {
    fn reading_text(&self) -> String {
        match self {
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(value)) => value.fact.readable_string(),
            Stmt::Definition(DefinitionStmt::DefThmStmt(value)) => value.fact.readable_string(),
            Stmt::Definition(DefinitionStmt::DefStrategyStmt(value)) => {
                Fact::ForallFact(value.forall_fact.clone()).readable_string()
            }
            Stmt::By(ByStmt::ByContraStmt(value)) => value.to_prove.readable_string(),
            Stmt::By(ByStmt::ByCasesStmt(value)) => value
                .then_facts
                .iter()
                .map(Fact::readable_string)
                .collect::<Vec<_>>()
                .join("\n"),
            Stmt::By(ByStmt::ByEnumerateFiniteSetStmt(value)) => {
                Fact::ForallFact(value.forall_fact.clone()).readable_string()
            }
            Stmt::By(ByStmt::ByForStmt(value)) => {
                Fact::ForallFact(value.forall_fact.clone()).readable_string()
            }
            _ => self.readable_string(),
        }
    }

    fn reading_proof_body(
        &self,
        owner: &str,
        branch: Option<usize>,
        part: &str,
    ) -> Option<&[Stmt]> {
        match self {
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(value))
                if owner.starts_with("ExecClaim") =>
            {
                Some(&value.proof)
            }
            Stmt::ProofBlock(ProofBlockStmt::SketchStmt(value))
                if owner == "ExecSketchStmtSuccess" =>
            {
                Some(&value.proof)
            }
            Stmt::Definition(DefinitionStmt::DefThmStmt(value))
                if owner.starts_with("ExecDefThm") =>
            {
                Some(&value.prove_process)
            }
            Stmt::Definition(DefinitionStmt::DefStrategyStmt(value))
                if owner == "ExecDefStrategyStmtSuccess" =>
            {
                Some(&value.prove_process)
            }
            Stmt::Witness(WitnessStmt::WitnessExistFact(value))
                if owner == "ExecWitnessExistFactStmtSuccessResult" =>
            {
                Some(&value.proof)
            }
            Stmt::Witness(WitnessStmt::WitnessAtomicFact(value))
                if owner == "ExecWitnessAtomicFactStmtSuccessResult" =>
            {
                Some(&value.proof)
            }
            Stmt::Witness(WitnessStmt::WitnessNonemptySet(value))
                if owner == "ExecWitnessNonemptySetStmtSuccessResult" =>
            {
                Some(&value.proof)
            }
            Stmt::By(ByStmt::ByContraStmt(value)) if owner == "ExecByContraStmtSuccess" => {
                Some(&value.proof)
            }
            Stmt::By(ByStmt::ByExtensionStmt(value)) if owner == "ExecByExtensionStmtSuccess" => {
                Some(&value.proof)
            }
            Stmt::By(ByStmt::ByFnExtensionStmt(value))
                if owner == "ExecByFnExtensionStmtSuccess" =>
            {
                Some(&value.proof)
            }
            Stmt::By(ByStmt::ByCasesStmt(value)) if owner == "ByCasesBranchSuccess" => {
                branch.and_then(|index| value.proofs.get(index).map(Vec::as_slice))
            }
            Stmt::By(ByStmt::ByEnumerateFiniteSetStmt(value))
                if owner == "EnumerateAssignmentOutcome" =>
            {
                Some(&value.proof)
            }
            Stmt::By(ByStmt::ByForStmt(value)) if owner == "EnumerateAssignmentOutcome" => {
                Some(&value.proof)
            }
            Stmt::By(ByStmt::ByInducStmt(value)) if owner == "ByInducCaseSuccess" => match part {
                "base" => Some(value.base_proof.as_deref().unwrap_or(&value.proof)),
                "step" => Some(value.step_proof.as_deref().unwrap_or(&value.proof)),
                _ => None,
            },
            Stmt::By(ByStmt::ByStrongInducStmt(value)) if owner == "ByInducCaseSuccess" => {
                match part {
                    "base" => Some(value.base_proof.as_deref().unwrap_or(&value.proof)),
                    "step" => Some(value.step_proof.as_deref().unwrap_or(&value.proof)),
                    _ => None,
                }
            }
            Stmt::ReleaseAndExpand(ReleaseAndExpandStmt::ReleaseZornLemmaStmt(value))
                if owner == "ExecReleaseZornLemmaStmtSuccess" =>
            {
                Some(&value.proof)
            }
            Stmt::ReleaseAndExpand(ReleaseAndExpandStmt::ReleaseAxiomOfChoiceStmt(value))
                if owner == "ExecReleaseAxiomOfChoiceStmtSuccess" =>
            {
                Some(&value.proof)
            }
            _ => None,
        }
    }
}
