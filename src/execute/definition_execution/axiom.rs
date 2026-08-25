use crate::prelude::*;

impl Runtime {
    pub fn exec_axiom_stmt(&mut self, stmt: &AxiomStmt) -> Result<StmtResult, RuntimeError> {
        if self.strict_mode_applies_to_current_module() {
            return Err(short_exec_error(
                stmt.clone().into(),
                AxiomStmt::strict_mode_rejection_message(),
                None,
                vec![],
            ));
        }

        let (well_definedness, _) = self
            .verify_forall_fact_well_defined_and_collect_certificate(
                &stmt.forall_fact,
                &ProofSearchState::initial(),
            )
            .map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    "axiom: forall fact is not well defined".to_string(),
                    Some(error),
                    vec![],
                )
            })?;

        let infer_result = self.exec_axiom_stmt_affect_environment(stmt)?;
        Ok(
            SuccessStmtResult::Definition(SuccessDefinitionStmtResult::AxiomStmt(Box::new(
                SuccessAxiomStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    well_definedness: Some(well_definedness),
                },
            )))
            .into(),
        )
    }

    pub fn exec_axiom_stmt_affect_environment(
        &mut self,
        stmt: &AxiomStmt,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_axiom(stmt)
            .map_err(|error| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), error))?;

        self.store_without_well_defined_verification_and_infer_with_reason(
            Fact::ForallFact(stmt.forall_fact.clone()),
            InferReason::Other(AxiomStmt::store_reason().to_string()),
        )
    }

    pub fn exec_axiom_stmt_affect_environment_only(
        &mut self,
        stmt: &AxiomStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.store_axiom(stmt)
            .map_err(|error| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), error))?;
        let infer_result = self.store_trusted_fact_and_infer_with_reason(
            Fact::ForallFact(stmt.forall_fact.clone()),
            InferReason::Other(AxiomStmt::store_reason().to_string()),
        )?;
        Ok(
            SuccessStmtResult::Definition(SuccessDefinitionStmtResult::AxiomStmt(Box::new(
                SuccessAxiomStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    well_definedness: None,
                },
            )))
            .into(),
        )
    }
}
