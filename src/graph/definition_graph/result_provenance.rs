//! Result provenance, proof sources, citations, and direct trust.

use super::*;

impl DefinitionGraphBuilder {
    pub(super) fn add_result_provenance(&mut self, stmt_results: &[StmtResult]) {
        for result in stmt_results {
            self.add_one_result_provenance(result);
        }
    }

    pub(super) fn add_one_result_provenance(&mut self, result: &StmtResult) {
        let Some(success) = result.non_factual_success() else {
            return;
        };
        let source_stmt = success.statement();
        match &source_stmt {
            Stmt::Definition(DefinitionStmt::DefThmStmt(statement)) => {
                let previous_canonical_name = self.active_canonical_name.clone();
                self.active_canonical_name = self
                    .canonical_name_by_source
                    .get(statement.line_file.1.as_ref())
                    .cloned();
                let sources = self.proof_source_ids_from_success_children(success);
                let direct_trust = success_children_contain_direct_trust(success);
                let name = self.normalized_dependency_name(&statement.name);
                let target_id = definition_id("theorem", name.as_str());
                if self.node_is_defined(&target_id) {
                    for source_id in sources.iter() {
                        self.add_edge(source_id, &target_id, "proof");
                    }
                    if direct_trust {
                        self.set_node_knowledge_status(&target_id, "trust", Some("direct"));
                    }
                }
                self.active_canonical_name = previous_canonical_name;
            }
            Stmt::Definition(DefinitionStmt::HaveFnByForallExistUniqueStmt(statement)) => {
                self.add_selection_certificate(statement, success);
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

    pub(super) fn add_selection_certificate(
        &mut self,
        statement: &HaveFnByForallExistUniqueStmt,
        success: &SuccessStmtResult,
    ) {
        let function_id = definition_id("fn", statement.fn_name());
        if !self.node_is_defined(&function_id) {
            return;
        }
        let certificate_id = selection_certificate_id(statement.fn_name(), &statement.line_file);
        self.ensure_node(
            certificate_id.clone(),
            "certificate",
            "selection_certificate",
            format!("{} exist!", statement.fn_name()).as_str(),
            true,
            Some(&statement.line_file),
            Some(&statement.forall.to_string()),
        );
        self.set_node_source_if_default(
            &function_id,
            &statement.line_file,
            statement.to_string().as_str(),
        );
        self.set_node_semantic_role(&function_id, "canonical_selection");
        self.set_node_litex_form(&function_id, "have_fn_by_exist_unique");

        let previous_canonical_name = self.active_canonical_name.clone();
        self.active_canonical_name = self
            .canonical_name_by_source
            .get(statement.line_file.1.as_ref())
            .cloned();
        let mut signature = DepCollector::new();
        signature.collect_param_def_with_type_deps(&statement.forall.typed_parameters);
        signature.add_param_def_with_type(&statement.forall.typed_parameters);
        for fact in statement.forall.then_facts.iter() {
            signature.collect_exist_or_and_chain_atomic_fact(fact);
        }
        self.add_dependency_edges(&certificate_id, signature, "signature");

        let mut well_definedness = DepCollector::new();
        well_definedness.add_param_def_with_type(&statement.forall.typed_parameters);
        for fact in statement.forall.dom_facts.iter() {
            well_definedness.collect_fact(fact);
        }
        self.add_dependency_edges(&certificate_id, well_definedness, "well_definedness");

        for source_id in self.proof_source_ids_from_success_children(success) {
            self.add_edge(&source_id, &certificate_id, "proof");
        }
        let direct_trust = success_children_contain_direct_trust(success);
        if direct_trust {
            self.set_node_knowledge_status(&certificate_id, "trust", Some("direct"));
            self.set_node_knowledge_status(&function_id, "trust", Some("direct"));
        }
        self.add_edge(&certificate_id, &function_id, "selection");
        self.active_canonical_name = previous_canonical_name;
    }

    pub(super) fn proof_source_ids_from_success_children(
        &mut self,
        success: &SuccessStmtResult,
    ) -> Vec<String> {
        let mut source_ids = Vec::new();
        success.visit_child_results(&mut |child| {
            self.collect_proof_source_ids_from_result(child, &mut source_ids)
        });
        success.visit_success_child_results(&mut |child| {
            self.collect_proof_source_ids_from_success(child, &mut source_ids)
        });
        source_ids.sort();
        source_ids.dedup();
        source_ids
    }

    pub(super) fn collect_proof_source_ids_from_verify_result(
        &mut self,
        result: &VerifyFactResult,
        source_ids: &mut Vec<String>,
    ) {
        if let Some(verified) = result.verified() {
            self.collect_verified_by_source_ids(verified.proof(), source_ids);
        }
    }

    pub(super) fn collect_proof_source_ids_from_result(
        &mut self,
        result: &StmtResult,
        source_ids: &mut Vec<String>,
    ) {
        let StmtResult::Success(success) = result else {
            return;
        };
        self.collect_proof_source_ids_from_success(success, source_ids);
    }

    pub(super) fn collect_proof_source_ids_from_success(
        &mut self,
        success: &SuccessStmtResult,
        source_ids: &mut Vec<String>,
    ) {
        if let Some(success) = success.fact() {
            if let Some(proof) = success.proof() {
                self.collect_verified_by_source_ids(proof, source_ids);
            }
            return;
        }
        if let SuccessStmtResult::By(SuccessByStmtResult::ByThmStmt(result)) = success {
            if let Some(verification) = result.verification.as_ref() {
                let StmtResult::Success(SuccessStmtResult::ReleaseThmStmt(application)) =
                    verification.temporary_application.as_ref()
                else {
                    return;
                };
                let Some(application_verification) = application.verification.as_ref() else {
                    return;
                };
                let theorem_name =
                    self.normalized_dependency_name(application_verification.theorem.as_str());
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
        }
        if let SuccessStmtResult::ReleaseThmStmt(result) = success {
            if let Some(verification) = result.verification.as_ref() {
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
        }
        match &success.statement() {
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
            Stmt::Definition(DefinitionStmt::AxiomStmt(statement)) => {
                let name = self.normalized_dependency_name(&statement.name);
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
            _ => {}
        }
        success.visit_child_results(&mut |child| {
            self.collect_proof_source_ids_from_result(child, source_ids)
        });
        success.visit_fact_verification_children(&mut |child| {
            self.collect_proof_source_ids_from_verify_result(child, source_ids)
        });
        success.visit_success_child_results(&mut |child| {
            self.collect_proof_source_ids_from_success(child, source_ids)
        });
    }

    pub(super) fn collect_verified_by_source_ids(
        &mut self,
        verified_by: &SuccessFactProofResult,
        source_ids: &mut Vec<String>,
    ) {
        match verified_by {
            SuccessFactProofResult::BuiltinRule(result)
            | SuccessFactProofResult::BuiltinStrategy(result) => {
                for subgoal in result.subgoals.iter() {
                    self.collect_proof_source_ids_from_verify_result(subgoal, source_ids);
                }
            }
            SuccessFactProofResult::StoredFactCitation(result) => self
                .collect_cited_stmt_source_ids(&result.source_fact.clone().into_stmt(), source_ids),
            SuccessFactProofResult::KnownForallInstantiation(result) => {
                self.collect_cited_stmt_source_ids(
                    &result.source_fact.clone().into_stmt(),
                    source_ids,
                );
                for requirement in result.requirements.iter() {
                    self.collect_proof_source_ids_from_verify_result(
                        requirement.result.as_ref(),
                        source_ids,
                    );
                }
            }
            SuccessFactProofResult::DefinitionReduction(result) => {
                self.collect_cited_stmt_source_ids(&result.definition.clone().into(), source_ids);
                for check in result.verification.clause_checks.iter() {
                    self.collect_proof_source_ids_from_verify_result(check, source_ids);
                }
            }
            SuccessFactProofResult::CheckedFunctionDefinitionReduction(result) => {
                self.collect_cited_stmt_source_ids(
                    &result.verification.defining_equality.clone().into_stmt(),
                    source_ids,
                );
                self.collect_proof_source_ids_from_verify_result(
                    &result.verification.reduced_equality,
                    source_ids,
                );
            }
            SuccessFactProofResult::DiagnosticOnly(_) => {}
            SuccessFactProofResult::CombinedProofs(result) => {
                if let Some(primary) = result.primary.as_ref() {
                    self.collect_verified_by_source_ids(primary.proof(), source_ids);
                }
                for step in result.steps.iter() {
                    self.collect_proof_source_ids_from_verify_result(step, source_ids);
                }
            }
            SuccessFactProofResult::ForallProof(result) => {
                for proved in result.proves.iter() {
                    self.collect_proof_source_ids_from_verify_result(
                        proved.result.as_ref(),
                        source_ids,
                    );
                }
            }
            SuccessFactProofResult::Transform(result) => {
                self.collect_verified_by_source_ids(result.source.proof(), source_ids);
            }
            SuccessFactProofResult::Reuse(result) => {
                self.collect_verified_by_source_ids(result.source.proof(), source_ids);
            }
        }
    }

    pub(super) fn collect_cited_stmt_source_ids(
        &mut self,
        statement: &Stmt,
        source_ids: &mut Vec<String>,
    ) {
        match statement {
            Stmt::Definition(DefinitionStmt::DefThmStmt(statement)) => {
                let name = self.normalized_dependency_name(&statement.name);
                let source_id = definition_id("theorem", name.as_str());
                self.ensure_node(
                    source_id.clone(),
                    "theorem",
                    "theorem",
                    name.as_str(),
                    false,
                    Some(&statement.line_file),
                    Some(&statement.to_string()),
                );
                source_ids.push(source_id);
            }
            Stmt::Definition(DefinitionStmt::AxiomStmt(statement)) => {
                let name = self.normalized_dependency_name(&statement.name);
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
            Stmt::Definition(DefinitionStmt::DefPropStmt(statement)) => {
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
            Stmt::Definition(DefinitionStmt::DefAbstractPropStmt(statement)) => {
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

    pub(super) fn ensure_direct_trust_source(
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
}
