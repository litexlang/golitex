//! Proof, citation, universal, subgoal, and inference edge collection.

use super::*;

impl FactGraphBuilder {
    pub(super) fn collect_result_edges(&mut self, result: &StmtResult) {
        if let StmtResult::Success(success) = result {
            self.collect_success_edges(success);
        }
    }

    pub(super) fn collect_success_edges(&mut self, success: &SuccessStmtResult) {
        if let Some(success) = success.fact() {
            let target_id = self.add_fact_node(&success.fact(), "fact", None);
            self.add_infer_edges(&success.infers);
            if let Some(proof) = success.proof() {
                self.collect_verified_by_edges(&target_id, proof);
            }
            return;
        }

        let source_stmt = success.statement();
        if let SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ClaimStmt(result)) =
            success
        {
            self.add_infer_edges(&result.environment_effects);
        }
        success.visit_child_results(&mut |child| self.collect_result_edges(child));
        success.visit_success_child_results(&mut |child| self.collect_success_edges(child));
        if let SuccessStmtResult::By(SuccessByStmtResult::ByDefStmt(result)) = success {
            let common = success
                .common()
                .expect("by-definition result carries common execution evidence");
            self.add_infer_edges(&common.infers);
            let target_fact: Fact = result.statement.fact.clone().into();
            let target_id = self.add_fact_node(&target_fact, "fact", None);
            if let Some(verification) = &result.verification {
                for clause_result in &verification.clause_checks {
                    for source_id in self.dependency_source_ids_from_verify_result(clause_result) {
                        for source_id in self.main_chain_source_ids(&source_id) {
                            self.add_edge(&source_id, &target_id, "unfolds");
                        }
                    }
                }
            }
            return;
        }
        if let SuccessStmtResult::By(SuccessByStmtResult::ByStructDefStmt(result)) = success {
            let common = success
                .common()
                .expect("by-struct-definition result carries common execution evidence");
            self.add_infer_edges(&common.infers);
            let membership: Fact = self
                .runtime
                .new_in_fact(
                    result.statement.obj.clone(),
                    result.struct_obj.clone().into(),
                    result.statement.line_file.clone(),
                )
                .into();
            let source_id = self.add_fact_node(&membership, "membership", None);
            for output in common.infers.store_fact_outputs() {
                let target_id = self.add_fact_node(
                    &output.itself_and_why_itself_is_stored.0,
                    "struct definition",
                    None,
                );
                self.add_edge(&source_id, &target_id, "unfolds");
            }
            return;
        }
        let mut last_fact_id = None;
        success.visit_child_results(&mut |child| {
            if let Some(node_id) = self.last_factual_result_node_id(std::slice::from_ref(child)) {
                last_fact_id = Some(node_id);
            }
        });
        success.visit_fact_verification_children(&mut |child| {
            self.collect_verify_result_edges(child);
            last_fact_id = Some(self.primary_verify_result_node_id(child));
        });
        success.visit_success_child_results(&mut |child| {
            if let Some(node_id) = self.last_factual_success_node_id(child) {
                last_fact_id = Some(node_id);
            }
        });
        let Some(last_fact_id) = last_fact_id else {
            return;
        };
        match &source_stmt {
            Stmt::Definition(DefinitionStmt::DefThmStmt(stmt)) => {
                self.add_edge(&last_fact_id, &theorem_id(&stmt.name), "proves");
            }
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(stmt)) => {
                self.add_edge(&last_fact_id, &claim_id(&stmt.line_file), "proves");
            }
            _ => {}
        }
    }

    pub(super) fn collect_verify_result_edges(&mut self, result: &VerifyFactResult) {
        let target_id = self.add_fact_node(&result.fact(), "verification", None);
        if let Some(verified) = result.verified() {
            self.collect_verified_by_edges(&target_id, verified.proof());
        }
    }

    pub(super) fn collect_verified_by_edges(
        &mut self,
        target_id: &str,
        verified_by: &SuccessFactProofResult,
    ) {
        match verified_by {
            SuccessFactProofResult::BuiltinRule(result)
            | SuccessFactProofResult::BuiltinStrategy(result) => {
                self.add_subgoal_edges(target_id, &result.subgoals);
            }
            SuccessFactProofResult::StoredFactCitation(result) => {
                self.add_cited_stmt_edges(target_id, &result.source_fact.clone().into_stmt())
            }
            SuccessFactProofResult::KnownForallInstantiation(result) => {
                self.add_known_forall_edges(target_id, result);
            }
            SuccessFactProofResult::DefinitionReduction(result) => {
                self.add_cited_stmt_edges(target_id, &result.definition.clone().into());
                for check in result.verification.clause_checks.iter() {
                    self.collect_verify_result_edges(check);
                }
            }
            SuccessFactProofResult::CheckedFunctionDefinitionReduction(result) => {
                self.add_cited_stmt_edges(
                    target_id,
                    &result.verification.defining_equality.clone().into_stmt(),
                );
                self.collect_verify_result_edges(&result.verification.reduced_equality);
                let source_id =
                    self.primary_verify_result_node_id(&result.verification.reduced_equality);
                self.add_edge(&source_id, target_id, "proves");
            }
            SuccessFactProofResult::DiagnosticOnly(_) => {}
            SuccessFactProofResult::CombinedProofs(result) => {
                if let Some(primary) = result.primary.as_ref() {
                    self.collect_verified_by_edges(target_id, primary.proof());
                }
                for step in result.steps.iter() {
                    self.collect_verify_result_edges(step);
                    let source_id = self.primary_verify_result_node_id(step);
                    self.add_edge(&source_id, target_id, "proves");
                }
            }
            SuccessFactProofResult::ForallProof(result) => {
                for proved in &result.proves {
                    self.collect_verify_result_edges(proved.result.as_ref());
                    self.add_infer_edges(&proved.store.infers);
                    let source_id = self.primary_verify_result_node_id(proved.result.as_ref());
                    self.add_edge(&source_id, target_id, "proves");
                }
            }
            SuccessFactProofResult::Transform(result) => {
                self.collect_verified_by_edges(target_id, result.source.proof());
            }
            SuccessFactProofResult::Reuse(result) => {
                self.collect_verified_by_edges(target_id, result.source.proof());
            }
        }
    }

    pub(super) fn add_cited_stmt_edges(&mut self, target_id: &str, cited_stmt: &Stmt) {
        if let Stmt::Definition(DefinitionStmt::DefPropStmt(definition)) = cited_stmt {
            self.add_definition_unfolding_edges(target_id, &definition.iff_facts);
            return;
        }
        if let Some(source_id) = self.add_cited_stmt_node(cited_stmt) {
            for source_id in self.main_chain_source_ids(&source_id) {
                self.add_edge(&source_id, target_id, "cites");
            }
        }
    }

    pub(super) fn add_definition_unfolding_edges(
        &mut self,
        target_id: &str,
        requirements: &[Fact],
    ) {
        for requirement in requirements {
            if let Some(source_id) = self.latest_matching_fact_node_id(target_id, requirement) {
                self.add_edge(&source_id, target_id, "unfolds");
            }
        }
    }

    pub(super) fn latest_matching_fact_node_id(
        &self,
        target_id: &str,
        fact: &Fact,
    ) -> Option<String> {
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

    pub(super) fn add_known_forall_edges(
        &mut self,
        target_id: &str,
        result: &SuccessInstantiateKnownForallResult,
    ) {
        if let Some(source_id) = self.add_cited_stmt_node(&result.source_fact.clone().into_stmt()) {
            self.add_edge(&source_id, target_id, "instantiates");
        }
        for requirement in &result.requirements {
            for source_id in
                self.dependency_source_ids_from_verify_result(requirement.result.as_ref())
            {
                for source_id in self.main_chain_source_ids(&source_id) {
                    self.add_edge(&source_id, target_id, "requires");
                }
            }
        }
    }

    pub(super) fn add_subgoal_edges(&mut self, target_id: &str, subgoals: &[VerifyFactResult]) {
        for subgoal in subgoals {
            self.collect_verify_result_edges(subgoal);
            let source_id = self.primary_verify_result_node_id(subgoal);
            for source_id in self.main_chain_source_ids(&source_id) {
                self.add_edge(&source_id, target_id, "subgoal");
            }
        }
    }

    pub(super) fn dependency_source_ids_from_verify_result(
        &mut self,
        result: &VerifyFactResult,
    ) -> Vec<String> {
        let direct_id = fact_node_id(&result.fact());
        if self.node_index.contains_key(&direct_id) {
            return vec![direct_id];
        }
        result
            .verified()
            .map(|verified| self.dependency_source_ids_from_verified_by(verified.proof()))
            .unwrap_or_default()
    }

    pub(super) fn dependency_source_ids_from_verified_by(
        &mut self,
        verified_by: &SuccessFactProofResult,
    ) -> Vec<String> {
        match verified_by {
            SuccessFactProofResult::BuiltinRule(result)
            | SuccessFactProofResult::BuiltinStrategy(result) => {
                self.dependency_source_ids_from_verify_results(&result.subgoals)
            }
            SuccessFactProofResult::StoredFactCitation(result) => self
                .add_cited_stmt_node(&result.source_fact.clone().into_stmt())
                .into_iter()
                .collect(),
            SuccessFactProofResult::KnownForallInstantiation(result) => self
                .add_cited_stmt_node(&result.source_fact.clone().into_stmt())
                .into_iter()
                .collect(),
            SuccessFactProofResult::DefinitionReduction(result) => {
                let mut ids = self
                    .add_cited_stmt_node(&result.definition.clone().into())
                    .into_iter()
                    .collect::<Vec<_>>();
                for check in result.verification.clause_checks.iter() {
                    ids.extend(self.dependency_source_ids_from_verify_result(check));
                }
                ids
            }
            SuccessFactProofResult::CheckedFunctionDefinitionReduction(result) => {
                let mut ids = self
                    .add_cited_stmt_node(&result.verification.defining_equality.clone().into_stmt())
                    .into_iter()
                    .collect::<Vec<_>>();
                ids.extend(self.dependency_source_ids_from_verify_result(
                    &result.verification.reduced_equality,
                ));
                ids.sort();
                ids.dedup();
                ids
            }
            SuccessFactProofResult::DiagnosticOnly(_) => Vec::new(),
            SuccessFactProofResult::CombinedProofs(result) => {
                let mut ids = vec![];
                if let Some(primary) = result.primary.as_ref() {
                    ids.extend(self.dependency_source_ids_from_verified_by(primary.proof()));
                }
                for step in result.steps.iter() {
                    ids.extend(self.dependency_source_ids_from_verify_result(step));
                }
                ids.sort();
                ids.dedup();
                ids
            }
            SuccessFactProofResult::ForallProof(result) => result
                .proves
                .iter()
                .flat_map(|proved| {
                    self.dependency_source_ids_from_verify_result(proved.result.as_ref())
                })
                .collect(),
            SuccessFactProofResult::Transform(result) => {
                self.dependency_source_ids_from_verified_by(result.source.proof())
            }
            SuccessFactProofResult::Reuse(result) => {
                self.dependency_source_ids_from_verified_by(result.source.proof())
            }
        }
    }

    pub(super) fn dependency_source_ids_from_verify_results(
        &mut self,
        results: &[VerifyFactResult],
    ) -> Vec<String> {
        let mut ids = vec![];
        for result in results {
            ids.extend(self.dependency_source_ids_from_verify_result(result));
        }
        ids.sort();
        ids.dedup();
        ids
    }

    pub(super) fn main_chain_source_ids(&self, source_id: &str) -> Vec<String> {
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
}
