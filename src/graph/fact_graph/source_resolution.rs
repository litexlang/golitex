//! Primary and last factual dependency source resolution.

use super::*;

impl FactGraphBuilder {
    pub(super) fn primary_verify_result_node_id(
        &mut self,
        result: &VerifyFactResult,
    ) -> String {
        self.add_fact_node(&result.fact(), "verification", None)
    }

    pub(super) fn add_infer_edges(&mut self, infers: &SuccessInferResult) {
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

    pub(super) fn primary_result_node_id(&mut self, result: &StmtResult) -> Option<String> {
        if let Some(success) = result.factual_success() {
            return Some(self.add_fact_node(&success.fact(), "fact", None));
        }
        let success = result.non_factual_success()?;
        match &success.statement() {
            Stmt::Definition(DefinitionStmt::DefThmStmt(stmt)) => Some(theorem_id(&stmt.name)),
            Stmt::Definition(DefinitionStmt::AxiomStmt(stmt)) => Some(theorem_id(&stmt.name)),
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(stmt)) => Some(claim_id(&stmt.line_file)),
            Stmt::By(ByStmt::ByDefStmt(stmt)) => {
                let fact: Fact = stmt.fact.clone().into();
                Some(self.add_fact_node(&fact, "fact", None))
            }
            _ => None,
        }
    }

    pub(super) fn last_factual_result_node_id(&mut self, results: &[StmtResult]) -> Option<String> {
        for result in results.iter().rev() {
            if let Some(success) = result.factual_success() {
                return Some(self.add_fact_node(&success.fact(), "fact", None));
            }
            if let Some(success) = result.non_factual_success() {
                if let Stmt::By(ByStmt::ByDefStmt(stmt)) = &success.statement() {
                    let fact: Fact = stmt.fact.clone().into();
                    return Some(self.add_fact_node(&fact, "fact", None));
                }
                let mut last_child_id = None;
                success.visit_child_results(&mut |child| {
                    if let Some(node_id) =
                        self.last_factual_result_node_id(std::slice::from_ref(child))
                    {
                        last_child_id = Some(node_id);
                    }
                });
                success.visit_success_child_results(&mut |child| {
                    if let Some(node_id) = self.last_factual_success_node_id(child) {
                        last_child_id = Some(node_id);
                    }
                });
                if last_child_id.is_some() {
                    return last_child_id;
                }
            }
        }
        None
    }
}
