use crate::prelude::*;

impl Runtime {
    pub fn verify_exist_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        let stmt_for_fact_errors: Stmt = fact.clone().to_fact().into();
        self.verify_exist_or_and_chain_atomic_fact_well_defined(fact, verify_state)
            .map_err(|well_defined_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    stmt_for_fact_errors.clone(),
                    "".to_string(),
                    Some(well_defined_error),
                    vec![],
                )
            })?;
        self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
            fact.clone(),
        )
        .map_err(|store_fact_error| {
            RuntimeErrorStruct::exec_stmt_new_with_stmt(
                stmt_for_fact_errors,
                "".to_string(),
                Some(RuntimeError::ExecStmtError(store_fact_error)),
                vec![],
            )
        })
    }

    pub fn verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
        &mut self,
        fact: &OrAndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        let stmt_for_fact_errors: Stmt = fact.clone().to_fact().into();
        self.verify_or_and_chain_atomic_fact_well_defined(fact, verify_state)
            .map_err(|well_defined_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    stmt_for_fact_errors.clone(),
                    "".to_string(),
                    Some(well_defined_error),
                    vec![],
                )
            })?;
        self.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(fact.clone())
            .map_err(|store_fact_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    stmt_for_fact_errors,
                    "".to_string(),
                    Some(RuntimeError::ExecStmtError(store_fact_error)),
                    vec![],
                )
            })
    }

    pub fn verify_fact_well_defined_and_store_and_infer(
        &mut self,
        fact: Fact,
        verify_state: &VerifyState,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        let stmt_for_fact_errors: Stmt = fact.clone().into();
        self.verify_fact_well_defined(&fact, verify_state)
            .map_err(|well_defined_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    stmt_for_fact_errors.clone(),
                    "".to_string(),
                    Some(well_defined_error),
                    vec![],
                )
            })?;
        self.store_fact_without_well_defined_verified_and_infer(fact)
            .map_err(|store_fact_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    stmt_for_fact_errors,
                    "".to_string(),
                    Some(RuntimeError::ExecStmtError(store_fact_error)),
                    vec![],
                )
            })
    }
}
