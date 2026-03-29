use super::exec_axiom_helpers::impossible_proof_error_message;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_contra_axiom_stmt(
        &mut self,
        stmt: &ByContraAxiomStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let to_prove_fact = Fact::AtomicFact(stmt.to_prove.clone());
        self.verify_fact_well_defined(&to_prove_fact, &VerifyState::new(0, false))
            .map_err(|verify_error| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByContraAxiomStmt(stmt.clone()),
                    format!("by_contra: failed to prove `{}`", to_prove_fact),
                    Some(verify_error.into()),
                    vec![],
                ))
            })?;

        let mut last_error: Option<RuntimeError> = None;
        let exec_proof_inside_results = {
            let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();

            self.push_env();

            let reverse_to_prove_fact = stmt.to_prove.make_reversed();
            self.store_atomic_fact_without_well_defined_verified_and_infer(&reverse_to_prove_fact)
                .map_err(|store_fact_error| {
                    RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                        Stmt::ByContraAxiomStmt(stmt.clone()),
                        format!("by_contra: failed to know reverse of `{}`", to_prove_fact),
                        Some(store_fact_error.into()),
                        vec![],
                    ))
                })?;

            for proof_stmt in stmt.proof.iter() {
                let exec_stmt_result = self.exec_stmt(proof_stmt);
                match exec_stmt_result {
                    Ok(result) => inside_results.push(result),
                    Err(statement_error) => {
                        last_error = Some(statement_error);
                        break;
                    }
                }
            }

            let verify_impossible_fact_result =
                self.verify_atomic_fact(&stmt.impossible_fact, &VerifyState::new(0, false))?;
            if verify_impossible_fact_result.is_unknown() {
                return Err(RuntimeError::ExecStmtError(
                    ExecStmtError::with_message_and_cause(
                        Stmt::ByContraAxiomStmt(stmt.clone()),
                        impossible_proof_error_message(&stmt.impossible_fact, None),
                        None,
                        inside_results,
                    ),
                ));
            }

            let verify_reversed_impossible_fact_result = self.verify_atomic_fact(
                &stmt.impossible_fact.make_reversed(),
                &VerifyState::new(0, false),
            )?;
            if verify_reversed_impossible_fact_result.is_unknown() {
                return Err(RuntimeError::ExecStmtError(
                    ExecStmtError::with_message_and_cause(
                        Stmt::ByContraAxiomStmt(stmt.clone()),
                        impossible_proof_error_message(&stmt.impossible_fact, None),
                        None,
                        vec![],
                    ),
                ));
            }

            self.pop_env();
            inside_results
        };

        if let Some(last_error) = last_error {
            return Err(RuntimeError::ExecStmtError(
                ExecStmtError::with_message_and_cause(
                    Stmt::ByContraAxiomStmt(stmt.clone()),
                    "by_contra: failed to execute proof".to_string(),
                    Some(last_error),
                    exec_proof_inside_results,
                ),
            ));
        }

        let infer_result = self
            .store_fact_without_well_defined_verified_and_infer(&to_prove_fact)
            .map_err(|store_fact_error| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByContraAxiomStmt(stmt.clone()),
                    format!("by_contra: failed to release `{}`", to_prove_fact),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })?;

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::ByContraAxiomStmt(stmt.clone()),
                infer_result,
                exec_proof_inside_results,
            ),
        ))
    }
}
