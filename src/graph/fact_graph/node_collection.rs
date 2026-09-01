//! Fact, theorem, claim, axiom, and citation node collection.

use super::*;

impl FactGraphBuilder {
    pub(super) fn new() -> Self {
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

    pub(super) fn from_stmt_results(stmt_results: &[StmtResult]) -> Self {
        let mut builder = Self::new();
        for result in stmt_results {
            builder.collect_result_nodes(result);
        }
        for result in stmt_results {
            builder.collect_result_edges(result);
        }
        builder
    }

    pub(super) fn collect_result_nodes(&mut self, result: &StmtResult) {
        if let StmtResult::Success(success) = result {
            self.collect_success_nodes(success);
        }
    }

    pub(super) fn collect_success_nodes(&mut self, success: &SuccessStmtResult) {
        if let Some(success) = success.fact() {
            self.add_fact_node(&success.fact(), "fact", None);
            self.add_infer_nodes(&success.infers);
            self.collect_verified_by_nodes(success.proof());
            return;
        }

        let source_stmt = success.statement();
        match &source_stmt {
            Stmt::Definition(DefinitionStmt::DefThmStmt(stmt)) => {
                self.add_theorem_nodes(stmt, &source_stmt)
            }
            Stmt::Definition(DefinitionStmt::AxiomStmt(stmt)) => {
                self.add_axiom_nodes(stmt, &source_stmt)
            }
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(stmt)) => {
                self.add_claim_nodes(stmt, &source_stmt);
                if let SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ClaimStmt(
                    result,
                )) = success
                {
                    self.add_infer_nodes(&result.environment_effects);
                }
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(_))
            | Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(_)) => {
                if let Some(common) = success.common() {
                    self.add_trust_nodes(&common.infers)
                }
            }
            Stmt::By(ByStmt::ByDefStmt(_)) | Stmt::By(ByStmt::ByStructDefStmt(_)) => {
                if let Some(common) = success.common() {
                    self.add_infer_nodes(&common.infers)
                }
            }
            _ => {}
        }
        if let SuccessStmtResult::Definition(SuccessDefinitionStmtResult::DefThmStmt(result)) =
            success
        {
            if let Some(verification) = result.verification.as_ref() {
                self.add_assumption_nodes(&verification.proof_scope.assumption_infers);
            }
        }
        let checked_goal_block = match success {
            SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ClaimStmt(result)) => {
                self.add_assumption_nodes(&result.domain.assumption_infers);
                None
            }
            SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ExampleStmt(result)) => {
                result.verification.as_ref()
            }
            _ => None,
        };
        if let Some(verification) = checked_goal_block {
            self.add_assumption_nodes(&verification.domain.assumption_infers);
        }
        success.visit_child_results(&mut |child| self.collect_result_nodes(child));
        success.visit_success_child_results(&mut |child| self.collect_success_nodes(child));
    }

    pub(super) fn collect_verified_by_nodes(&mut self, verified_by: &SuccessFactProofResult) {
        match verified_by {
            SuccessFactProofResult::BuiltinRule(result)
            | SuccessFactProofResult::BuiltinStrategy(result) => {
                for subgoal in &result.subgoals {
                    self.collect_result_nodes(subgoal);
                }
            }
            SuccessFactProofResult::StoredFactCitation(result) => {
                self.add_cited_stmt_node(&result.source_fact.clone().into_stmt());
            }
            SuccessFactProofResult::KnownForallInstantiation(result) => {
                self.add_cited_stmt_node(&result.source_fact.clone().into_stmt());
                for requirement in &result.requirements {
                    self.add_requirement_source_nodes(requirement.result.as_ref());
                }
            }
            SuccessFactProofResult::DefinitionReduction(result) => {
                self.add_cited_stmt_node(&result.definition.clone().into());
                for check in result.verification.clause_checks.iter() {
                    self.collect_result_nodes(check);
                }
            }
            SuccessFactProofResult::CheckedFunctionDefinitionReduction(result) => {
                self.add_cited_stmt_node(
                    &result.verification.defining_equality.clone().into_stmt(),
                );
            }
            SuccessFactProofResult::DiagnosticOnly(_) => {}
            SuccessFactProofResult::CombinedProofs(result) => {
                if let Some(primary) = result.primary.as_ref() {
                    self.collect_verified_by_nodes(primary.proof());
                }
                for step in result.steps.iter() {
                    self.collect_result_nodes(step);
                }
            }
            SuccessFactProofResult::ForallProof(result) => {
                self.add_assumption_nodes(&result.assumption_infers);
                for proved in &result.proves {
                    self.collect_result_nodes(proved.result.as_ref());
                }
            }
            SuccessFactProofResult::Transform(result) => {
                self.collect_verified_by_nodes(result.source.proof());
            }
            SuccessFactProofResult::Reuse(result) => {
                self.collect_verified_by_nodes(result.source.proof());
            }
        }
    }

    pub(super) fn add_infer_nodes(&mut self, infers: &SuccessInferResult) {
        for output in infers.store_fact_outputs() {
            let (fact, reason) = &output.itself_and_why_itself_is_stored;
            self.add_fact_node(fact, fact_kind_from_store_reason(reason), Some(reason));
            for inferred in &output.inferred_facts {
                self.add_fact_node(inferred, "inferred", Some(reason));
            }
        }
    }

    pub(super) fn add_assumption_nodes(&mut self, infers: &SuccessInferResult) {
        for output in infers.store_fact_outputs() {
            if output.itself_and_why_itself_is_stored.1 == TypedParameterList::store_reason() {
                continue;
            }
            self.add_fact_node(
                &output.itself_and_why_itself_is_stored.0,
                "assumption",
                Some(&output.itself_and_why_itself_is_stored.1),
            );
        }
    }

    pub(super) fn add_trust_nodes(&mut self, infers: &SuccessInferResult) {
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

    pub(super) fn add_requirement_source_nodes(&mut self, result: &StmtResult) {
        let _ = self.dependency_source_ids_from_result(result);
    }

    pub(super) fn add_theorem_nodes(&mut self, stmt: &DefThmStmt, full_stmt: &Stmt) {
        let interface_fact = stmt.fact.clone();
        let interface_line = line_key(&interface_fact.line_file());
        let theorem_id = theorem_id(&stmt.name);
        self.ensure_node(
            theorem_id.clone(),
            "fact",
            stmt.name.clone(),
            Some(&stmt.line_file),
            Some(&full_stmt.to_string()),
            Some("thm"),
            None,
        );
        self.theorem_node_by_line.insert(interface_line, theorem_id);
    }

    pub(super) fn add_axiom_nodes(&mut self, stmt: &AxiomStmt, full_stmt: &Stmt) {
        let interface_fact: Fact = stmt.forall_fact.clone().into();
        let interface_line = line_key(&interface_fact.line_file());
        let theorem_id = theorem_id(&stmt.name);
        self.ensure_node(
            theorem_id.clone(),
            "fact",
            stmt.name.clone(),
            Some(&stmt.line_file),
            Some(&full_stmt.to_string()),
            Some("axiom"),
            None,
        );
        self.theorem_node_by_line.insert(interface_line, theorem_id);
    }

    pub(super) fn add_claim_nodes(&mut self, stmt: &ClaimStmt, full_stmt: &Stmt) {
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

    pub(super) fn add_cited_stmt_node(&mut self, stmt: &Stmt) -> Option<String> {
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
            Stmt::Definition(DefinitionStmt::DefThmStmt(def_thm)) => {
                let name = &def_thm.name;
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
            Stmt::Definition(DefinitionStmt::AxiomStmt(axiom)) => {
                let name = &axiom.name;
                let node_id = theorem_id(name);
                self.ensure_node(
                    node_id.clone(),
                    "fact",
                    name.to_string(),
                    Some(&axiom.line_file),
                    Some(&stmt.to_string()),
                    Some("axiom"),
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
}
