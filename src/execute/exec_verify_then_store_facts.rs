use crate::prelude::*;

impl Runtime {
    /// Mathematical contract: before assuming an existential/compound fact,
    /// verify every binder, object, and component fact, then store the checked
    /// fact and its sound consequences.
    pub fn verify_exist_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<InferResult, RuntimeError> {
        self.verify_exist_or_and_chain_atomic_fact_well_defined_and_store_and_infer_with_reason(
            fact,
            verify_state,
            InferReason::VerifiedStatement,
        )
    }

    /// Mathematical contract: identical to the compound-fact check above;
    /// `reason` changes provenance only, never the proof obligations.
    pub fn verify_exist_or_and_chain_atomic_fact_well_defined_and_store_and_infer_with_reason(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        verify_state: &UseContextVerifyState,
        reason: InferReason,
    ) -> Result<InferResult, RuntimeError> {
        let stmt_for_fact_errors: Stmt = fact.clone().to_fact().into();
        self.verify_exist_or_and_chain_atomic_fact_well_defined(fact, verify_state)
            .map_err(|well_defined_error| {
                exec_stmt_error_with_stmt_and_cause(
                    stmt_for_fact_errors.clone(),
                    well_defined_error,
                )
            })?;
        self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                fact.clone(),
                reason.store_reason(),
        )
        .map_err(|store_fact_error| {
            exec_stmt_error_with_stmt_and_cause(stmt_for_fact_errors, store_fact_error)
        })
    }

    /// Mathematical contract: before assuming an atomic/conjunctive/chain/or
    /// fact, verify all of its mathematical objects and subfacts, then store
    /// the checked fact and its consequences.
    pub fn verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
        &mut self,
        fact: &OrAndChainAtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<InferResult, RuntimeError> {
        self.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer_with_reason(
            fact,
            verify_state,
            InferReason::VerifiedStatement,
        )
    }

    /// Mathematical contract: identical to the restricted compound-fact check
    /// above; the supplied reason records provenance without weakening it.
    pub fn verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer_with_reason(
        &mut self,
        fact: &OrAndChainAtomicFact,
        verify_state: &UseContextVerifyState,
        reason: InferReason,
    ) -> Result<InferResult, RuntimeError> {
        let stmt_for_fact_errors: Stmt = fact.clone().to_fact().into();
        self.verify_or_and_chain_atomic_fact_well_defined(fact, verify_state)
            .map_err(|well_defined_error| {
                exec_stmt_error_with_stmt_and_cause(
                    stmt_for_fact_errors.clone(),
                    well_defined_error,
                )
            })?;
        self.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason(
            fact.clone(),
            reason.store_reason(),
        )
        .map_err(|store_fact_error| {
            exec_stmt_error_with_stmt_and_cause(stmt_for_fact_errors, store_fact_error)
        })
    }

    /// Mathematical contract: a fact may enter the environment only after the
    /// central fact checker establishes its complete well-definedness contract.
    pub fn verify_fact_well_defined_and_store_and_infer(
        &mut self,
        fact: Fact,
        verify_state: &UseContextVerifyState,
    ) -> Result<InferResult, RuntimeError> {
        self.verify_fact_well_defined_and_store_and_infer_with_reason(
            fact,
            verify_state,
            InferReason::VerifiedStatement,
        )
    }

    /// Mathematical contract: the provenance-bearing variant enforces the
    /// same fact well-definedness obligations before storage and inference.
    pub fn verify_fact_well_defined_and_store_and_infer_with_reason(
        &mut self,
        fact: Fact,
        verify_state: &UseContextVerifyState,
        reason: InferReason,
    ) -> Result<InferResult, RuntimeError> {
        let stmt_for_fact_errors: Stmt = fact.clone().into();
        self.verify_well_defined_and_store_and_infer_with_reason(fact, verify_state, reason)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt_for_fact_errors, e))
    }
}
