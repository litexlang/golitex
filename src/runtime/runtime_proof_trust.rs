use crate::prelude::*;
use std::collections::HashSet;

impl Runtime {
    pub fn proof_trust_summary_from_stmt_results(
        &self,
        results: &[StmtResult],
    ) -> ProofTrustSummary {
        let mut summary = ProofTrustSummary::new();
        for result in results {
            self.collect_stmt_result_trust(result, &mut summary);
        }
        summary
    }

    pub fn proof_trust_summary_from_stmt(&self, stmt: &Stmt) -> ProofTrustSummary {
        let mut summary = ProofTrustSummary::new();
        self.collect_stmt_trust(stmt, &mut summary);
        summary
    }

    pub(crate) fn propagate_cli_trust_to_statement_effects(
        &mut self,
        result: &StmtResult,
        previous_symbol_ids: &HashSet<SymbolId>,
    ) -> Result<(), RuntimeError> {
        let Some(trace) = result.execution_trace() else {
            return Ok(());
        };
        if !trace.trust_summary.contains_kind("cli_trusted_prefix") {
            return Ok(());
        }
        let trust_summary = trace.trust_summary.clone();
        self.merge_trust_into_new_environment_symbols(previous_symbol_ids, &trust_summary);
        self.merge_trust_into_persistent_result_facts(result, &trust_summary)
    }

    fn collect_stmt_result_trust(&self, result: &StmtResult, summary: &mut ProofTrustSummary) {
        if let Some(success) = result.factual_success() {
            self.collect_stmt_trust(&success.stmt.clone().into(), summary);
            self.collect_infer_result_trust(&success.infers, summary);
            self.collect_verified_by_trust(&success.verified_by, summary);
        }
        if let Some(success) = result.non_factual_success() {
            self.collect_stmt_trust(&success.stmt, summary);
            self.collect_infer_result_trust(&success.infers, summary);
            if let Some(ByVerificationResult::Theorem(verification)) =
                success.by_verification.as_ref()
            {
                summary.merge(&self.get_thm_trust_summary_by_name(&verification.theorem));
            }
            for inside in success.inside_results.iter() {
                self.collect_stmt_result_trust(inside, summary);
            }
        }
    }

    fn collect_stmt_trust(&self, stmt: &Stmt, summary: &mut ProofTrustSummary) {
        self.collect_symbol_trust_from_stmt(stmt, summary);
        match stmt {
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(trust)) => {
                summary.add_dependency("trust", None, trust.line_file.clone());
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(trust_have)) => {
                summary.add_dependency("trust_have", None, trust_have.line_file.clone());
            }
            Stmt::DefThmStmt(def_thm) if def_thm.is_axiom() => {
                summary.add_dependency(
                    "axiom",
                    Some(def_thm.name.clone()),
                    def_thm.line_file.clone(),
                );
            }
            Stmt::Fact(fact) => {
                summary.merge(&self.trust_summary_for_cached_fact(&fact.to_string()));
            }
            _ => {}
        }
    }

    fn collect_symbol_trust_from_stmt(&self, stmt: &Stmt, summary: &mut ProofTrustSummary) {
        let statement = stmt.to_string();
        for environment in self.iter_environments_from_top() {
            for (_, definition) in environment.symbols.iter() {
                if definition.trust_summary().is_empty() {
                    continue;
                }
                let identity_prefix = format!("#{}#", definition.binding().id().value());
                if statement.contains(identity_prefix.as_str()) {
                    summary.merge(definition.trust_summary());
                }
            }
        }
    }

    fn collect_infer_result_trust(&self, infers: &InferResult, summary: &mut ProofTrustSummary) {
        for output in infers.store_fact_outputs() {
            let fact = &output.itself_and_why_itself_is_stored.0;
            let reason = &output.itself_and_why_itself_is_stored.1;
            summary.merge(&ProofTrustSummary::from_store_reason(
                reason,
                fact.line_file(),
            ));
            summary.merge(&self.trust_summary_for_cached_fact(&fact.to_string()));
        }
    }

    fn collect_verified_by_trust(
        &self,
        verified_by: &VerifiedByResult,
        summary: &mut ProofTrustSummary,
    ) {
        match verified_by {
            VerifiedByResult::BuiltinRule(result) => {
                for subgoal in result.subgoals.iter() {
                    self.collect_stmt_result_trust(subgoal, summary);
                }
            }
            VerifiedByResult::Fact(result) => {
                self.collect_stmt_trust(&result.cite_what, summary);
            }
            VerifiedByResult::KnownForallInstantiation(result) => {
                self.collect_stmt_trust(&result.cite_what, summary);
                for requirement in result.requirements.iter() {
                    self.collect_stmt_result_trust(&requirement.result, summary);
                }
            }
            VerifiedByResult::VerifiedBys(result) => {
                for item in result.cite_what.iter() {
                    self.collect_verified_bys_item_trust(item, summary);
                }
            }
            VerifiedByResult::ForallProof(result) => {
                self.collect_infer_result_trust(&result.assumption_infers, summary);
                for proved in result.proves.iter() {
                    self.collect_stmt_result_trust(&proved.result, summary);
                }
            }
        }
    }

    fn collect_verified_bys_item_trust(
        &self,
        item: &VerifiedBysEnum,
        summary: &mut ProofTrustSummary,
    ) {
        match item {
            VerifiedBysEnum::ByBuiltinRule(result) => {
                for subgoal in result.subgoals.iter() {
                    self.collect_stmt_result_trust(subgoal, summary);
                }
            }
            VerifiedBysEnum::ByFact(result) => {
                self.collect_stmt_trust(&result.cite_what, summary);
            }
            VerifiedBysEnum::ByKnownForall(result) => {
                self.collect_stmt_trust(&result.result.cite_what, summary);
                for requirement in result.result.requirements.iter() {
                    self.collect_stmt_result_trust(&requirement.result, summary);
                }
            }
        }
    }

    fn merge_trust_into_persistent_result_facts(
        &mut self,
        result: &StmtResult,
        trust_summary: &ProofTrustSummary,
    ) -> Result<(), RuntimeError> {
        if let Some(success) = result.factual_success() {
            self.store_fact_cache_keys_with_nested_obj_binders(
                &success.stmt,
                trust_summary.clone(),
            )?;
            self.merge_trust_into_infer_result_facts(&success.infers, trust_summary)?;
        }
        if let Some(success) = result.non_factual_success() {
            self.merge_trust_into_infer_result_facts(&success.infers, trust_summary)?;
            if matches!(&success.stmt, Stmt::ProofBlock(ProofBlockStmt::TryStmt(_))) {
                for inside in success.inside_results.iter() {
                    self.merge_trust_into_persistent_result_facts(inside, trust_summary)?;
                }
            }
        }
        Ok(())
    }

    fn merge_trust_into_infer_result_facts(
        &mut self,
        infer_result: &InferResult,
        trust_summary: &ProofTrustSummary,
    ) -> Result<(), RuntimeError> {
        for fact in infer_result.inferred_facts() {
            self.store_fact_cache_keys_with_nested_obj_binders(&fact, trust_summary.clone())?;
        }
        Ok(())
    }
}
