use crate::prelude::*;

impl Runtime {
    pub fn verify_exist_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<InferResult, RuntimeError> {
        let stmt_for_fact_errors: Stmt = fact.clone().to_fact().into();
        self.verify_exist_or_and_chain_atomic_fact_well_defined(fact, verify_state)
            .map_err(|well_defined_error| {
                exec_stmt_error_with_stmt_and_cause(
                    stmt_for_fact_errors.clone(),
                    well_defined_error,
                )
            })?;
        self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
            fact.clone(),
        )
        .map_err(|store_fact_error| {
            exec_stmt_error_with_stmt_and_cause(stmt_for_fact_errors, store_fact_error)
        })
    }

    pub fn verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
        &mut self,
        fact: &OrAndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<InferResult, RuntimeError> {
        let stmt_for_fact_errors: Stmt = fact.clone().to_fact().into();
        self.verify_or_and_chain_atomic_fact_well_defined(fact, verify_state)
            .map_err(|well_defined_error| {
                exec_stmt_error_with_stmt_and_cause(
                    stmt_for_fact_errors.clone(),
                    well_defined_error,
                )
            })?;
        self.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(fact.clone())
            .map_err(|store_fact_error| {
                exec_stmt_error_with_stmt_and_cause(stmt_for_fact_errors, store_fact_error)
            })
    }

    pub fn verify_fact_well_defined_and_store_and_infer(
        &mut self,
        fact: Fact,
        verify_state: &VerifyState,
    ) -> Result<InferResult, RuntimeError> {
        self.verify_fact_well_defined_and_store_and_infer_with_reason(
            fact,
            verify_state,
            InferReason::VerifiedStatement,
        )
    }

    pub fn verify_fact_well_defined_and_store_and_infer_with_reason(
        &mut self,
        fact: Fact,
        verify_state: &VerifyState,
        reason: InferReason,
    ) -> Result<InferResult, RuntimeError> {
        let stmt_for_fact_errors: Stmt = fact.clone().into();
        self.verify_well_defined_and_store_and_infer_with_reason(fact, verify_state, reason)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt_for_fact_errors, e))
    }
}
