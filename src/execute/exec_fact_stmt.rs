use crate::prelude::*;
use std::result::Result;

impl Runtime {
    pub fn exec_fact(&mut self, fact: &Fact) -> Result<StmtResult, RuntimeError> {
        self.exec_fact_stmt_verify_well_definedness(fact)?;
        self.set_well_definedness_target_requirement_phase(
            WellDefinednessTargetRequirementPhase::Proof,
        );
        let result = self.exec_fact_stmt_verify_process(fact)?;
        self.set_well_definedness_target_requirement_phase(
            WellDefinednessTargetRequirementPhase::Store,
        );
        let infer_result = self.exec_fact_stmt_affect_environment(fact, &result)?;

        Ok(result.with_infers(infer_result))
    }

    /// Mathematical contract: a standalone fact is meaningful exactly when
    /// the central fact checker validates its predicate, arguments, binders,
    /// premises, and conclusions.
    fn exec_fact_stmt_verify_well_definedness(&mut self, fact: &Fact) -> Result<(), RuntimeError> {
        self.verify_fact_well_defined(fact, &UseContextVerifyState::new(0, false))
    }

    fn exec_fact_stmt_verify_process(&mut self, fact: &Fact) -> Result<StmtResult, RuntimeError> {
        self.verify_fact_return_err_if_not_true(fact, &UseContextVerifyState::new(0, false))
    }

    fn exec_fact_stmt_affect_environment(
        &mut self,
        fact: &Fact,
        result: &StmtResult,
    ) -> Result<InferResult, RuntimeError> {
        let verification_store_facts = result.infer_result();
        let mut infer_result = self
            .store_with_well_defined_verification_and_infer_with_default_verify_state(
                fact.clone(),
            )?;
        // Ordinary output suppresses the duplicate primary store record.  In
        // During compiler capture that record also owns the source-to-inferred-fact
        // edges (for example, concrete-prop definition projections), so keep
        // it as compiler evidence; IR construction still de-duplicates the
        // primary proposition itself.
        if verification_store_facts.contains_added_fact(fact) && !self.captures_well_definedness() {
            infer_result.remove_first_verified_statement_for_fact(fact);
        }

        Ok(infer_result)
    }

    pub(crate) fn exec_fact_stmt_affect_environment_only(
        &mut self,
        fact: &Fact,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.store_trusted_fact_and_infer_with_reason(
            fact.clone(),
            InferReason::VerifiedStatement,
        )?;

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                fact.clone(),
                infer_result,
                "trusted file load".to_string(),
                vec![],
            )
            .into(),
        )
    }
}
