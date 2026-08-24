use crate::error::RuntimeError;
use crate::fact::Fact;
use crate::infer::{InferReason, SuccessInferResult};
use crate::pipeline::record_pipeline_step;
use crate::result::{StmtResult, SuccessFactStmtResult, SuccessVerifyFactWellDefinedResult};
use crate::runtime::Runtime;
use crate::verify::ProofSearchState;
use std::result::Result;

impl Runtime {
    pub fn execute_submitted_fact(&mut self, fact: &Fact) -> Result<StmtResult, RuntimeError> {
        record_pipeline_step(
            "execute fact",
            "Runtime::execute_submitted_fact",
            "src/execute/submitted_fact_execution.rs",
        );
        let well_definedness = self.verify_fact_well_defined_for_execution(fact)?;
        let result = self.verify_fact_for_execution(fact)?;
        let infer_result = self.store_executed_fact_and_infer(fact, &result)?;

        Ok(result
            .with_fact_well_definedness(well_definedness)
            .with_infers(infer_result))
    }

    /// Mathematical contract: a standalone fact is meaningful exactly when
    /// the central fact checker validates its predicate, arguments, binders,
    /// premises, and conclusions.
    fn verify_fact_well_defined_for_execution(
        &mut self,
        fact: &Fact,
    ) -> Result<SuccessVerifyFactWellDefinedResult, RuntimeError> {
        record_pipeline_step(
            "well-definedness",
            "Runtime::verify_fact_well_defined_for_execution",
            "src/execute/submitted_fact_execution.rs",
        );
        self.verify_fact_well_defined_result(fact, &ProofSearchState::initial())
    }

    fn verify_fact_for_execution(&mut self, fact: &Fact) -> Result<StmtResult, RuntimeError> {
        record_pipeline_step(
            "verify",
            "Runtime::verify_fact_for_execution",
            "src/execute/submitted_fact_execution.rs",
        );
        self.verify_fact_or_error(fact, &ProofSearchState::initial())
    }

    fn store_executed_fact_and_infer(
        &mut self,
        fact: &Fact,
        result: &StmtResult,
    ) -> Result<SuccessInferResult, RuntimeError> {
        record_pipeline_step(
            "store and infer",
            "Runtime::store_executed_fact_and_infer",
            "src/execute/submitted_fact_execution.rs",
        );
        let verification_store_facts = result.infer_result();
        let mut infer_result =
            self.store_without_well_defined_verification_and_infer(fact.clone())?;
        if verification_store_facts.contains_added_fact(fact) {
            infer_result.remove_first_verified_statement_for_fact(fact);
        }

        Ok(infer_result)
    }

    pub fn execute_trusted_fact(&mut self, fact: &Fact) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.store_trusted_fact_and_infer_with_reason(
            fact.clone(),
            InferReason::VerifiedStatement,
        )?;

        Ok(
            SuccessFactStmtResult::new_with_verified_by_builtin_rules_label_and_steps(
                fact.clone(),
                infer_result,
                "trusted file load".to_string(),
                vec![],
            )
            .into(),
        )
    }
}
