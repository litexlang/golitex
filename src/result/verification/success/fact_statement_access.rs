//! Successful fact-statement proof access and constructors.

use super::proof_composition::merge_verified_by_with_steps;
use crate::prelude::*;
use std::rc::Rc;

impl SuccessFactStmtResult {
    pub fn new_with_verified_by_builtin_rules(
        stmt: Fact,
        infers: SuccessInferResult,
        verified_by: SuccessFactProofResult,
    ) -> Self {
        Self::new(stmt, infers, verified_by)
    }

    pub fn new_with_verified_by_builtin_strategy_evidence_recording_stmt(
        stmt: Fact,
        strategy_label: String,
        evidence: BuiltinRuleEvidence,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by = SuccessFactProofResult::BuiltinStrategy(SuccessBuiltinFactProofResult {
            msg: strategy_label,
            evidence: SuccessBuiltinFactProofEvidenceResult::Typed(evidence),
            subgoals: step_results,
        });
        Self::new_with_verified_by_builtin_rules(stmt, SuccessInferResult::new(), verified_by)
    }

    pub fn new_with_verified_by_builtin_rule_evidence_and_steps(
        stmt: Fact,
        infers: SuccessInferResult,
        builtin_rule_label: String,
        evidence: BuiltinRuleEvidence,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by = SuccessFactProofResult::builtin_rule_with_evidence(
            builtin_rule_label,
            evidence,
            step_results,
        );
        Self::new_with_verified_by_builtin_rules(stmt, infers, verified_by)
    }

    pub fn new_with_verified_by_builtin_rule_evidence_recording_stmt(
        stmt: Fact,
        builtin_rule_label: String,
        evidence: BuiltinRuleEvidence,
        step_results: Vec<StmtResult>,
    ) -> Self {
        Self::new_with_verified_by_builtin_rule_evidence_and_steps(
            stmt,
            SuccessInferResult::new(),
            builtin_rule_label,
            evidence,
            step_results,
        )
    }

    pub fn new_with_verified_by_known_fact_and_infer(
        stmt: Fact,
        infers: SuccessInferResult,
        verified_by: SuccessFactProofResult,
        step_results: Vec<StmtResult>,
    ) -> Self {
        let verified_by = merge_verified_by_with_steps(stmt.clone(), verified_by, step_results);
        Self::new(stmt, infers, verified_by)
    }

    pub fn new_with_verified_by_known_fact(
        stmt: Fact,
        verified_by: SuccessFactProofResult,
        step_results: Vec<StmtResult>,
    ) -> Self {
        Self::new_with_verified_by_known_fact_and_infer(
            stmt,
            SuccessInferResult::new(),
            verified_by,
            step_results,
        )
    }

    pub fn new_with_statement_proof_cache(
        stmt: Fact,
        infers: SuccessInferResult,
        source: Rc<SuccessVerifyFactResult>,
    ) -> Self {
        Self::new_with_verified_by_builtin_rules(
            stmt,
            infers,
            SuccessFactProofResult::Reuse(Box::new(SuccessReuseFactProofResult { source })),
        )
    }

    pub fn is_verified_by_builtin_rules_only(&self) -> bool {
        self.proof().tree_is_builtin_rules_only()
    }
}
