use crate::prelude::*;

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

    fn collect_stmt_result_trust(&self, result: &StmtResult, summary: &mut ProofTrustSummary) {
        if let Some(success) = result.factual_success() {
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
        match stmt {
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(trust)) => {
                summary.add_dependency("trust", None, trust.line_file.clone());
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(trust_have)) => {
                summary.add_dependency("trust_have", None, trust_have.line_file.clone());
            }
            Stmt::DefThmStmt(def_thm) if def_thm.is_axiom() => {
                let name = def_thm.names.first().cloned();
                summary.add_dependency("axiom", name, def_thm.line_file.clone());
            }
            Stmt::Fact(fact) => {
                summary.merge(&self.trust_summary_for_cached_fact(&fact.to_string()));
            }
            _ => {}
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
}
