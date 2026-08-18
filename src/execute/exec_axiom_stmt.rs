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

        self.verify_forall_fact_well_defined_and_collect_certificate(
            &stmt.forall_fact,
            &UseContextVerifyState::new(0, false),
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
        Ok(VerifiedStmtIr::AxiomStmt {
            statement: stmt.clone(),
            common: VerifiedStmtCommonIr::new(infer_result, vec![]),
        }
        .into())
    }

    pub(crate) fn exec_axiom_stmt_affect_environment(
        &mut self,
        stmt: &AxiomStmt,
    ) -> Result<InferResult, RuntimeError> {
        self.store_axiom(stmt)
            .map_err(|error| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), error))?;

        self.store_without_well_defined_verification_and_infer_with_reason(
            Fact::ForallFact(stmt.forall_fact.clone()),
            InferReason::Other(AxiomStmt::store_reason().to_string()),
        )
    }

    pub(crate) fn exec_axiom_stmt_affect_environment_only(
        &mut self,
        stmt: &AxiomStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.store_axiom(stmt)
            .map_err(|error| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), error))?;
        let infer_result = self.store_trusted_fact_and_infer_with_reason(
            Fact::ForallFact(stmt.forall_fact.clone()),
            InferReason::Other(AxiomStmt::store_reason().to_string()),
        )?;
        Ok(VerifiedStmtIr::AxiomStmt {
            statement: stmt.clone(),
            common: VerifiedStmtCommonIr::new(infer_result, vec![]),
        }
        .into())
    }
}
