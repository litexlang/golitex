use crate::error::StmtError;
use crate::error::{ExecError, UnknownError};
use crate::fact::Fact;
use crate::verify::VerifyState;
use crate::stmt::claim_stmt::ClaimStmt;
use crate::result::NonErrStmtExecResult;
use crate::result::NonFactualStmtSuccess;
use super::Executor;

impl<'a> Executor<'a> {
    fn exec_claim_stmt_body(&mut self, stmt: &ClaimStmt) -> Result<NonErrStmtExecResult, StmtError> {
        for proof_stmt in stmt.proof.iter() {
            self.stmt(proof_stmt)?;
        }

        let verify_result = self.verify_fact(&stmt.fact, &VerifyState::new(0, false))?;
        if !verify_result.is_true() {
            return Err(StmtError::UnknownError(UnknownError::new(
                format!("claim failed: cannot prove `{}`", stmt.fact),
                stmt.line_file_index,
                None,
            )));
        }

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(
            stmt.to_string(),
            crate::infer::InferResult::new(),
            stmt.line_file_index,
        )))
    }

    pub fn exec_claim_stmt(&mut self, stmt: &ClaimStmt) -> Result<NonErrStmtExecResult, StmtError> {
        match &stmt.fact {
            Fact::ForallFactWithIff(_) => unreachable!("claim forall with iff is not supported"),
            Fact::ForallFact(forall_fact) => {
                self.verify_fact_well_defined(&stmt.fact, &VerifyState::new(0, false))
                    .map_err(|e| {
                        StmtError::ExecError(ExecError::new(
                            stmt.stmt_type_name(),
                            "claim: fact is not well defined".to_string(),
                            Some(e.into()),
                            stmt.line_file_index,
                        ))
                    })?;

                self.runtime_context.new_env();
                let body_result = self
                    .define_params_with_type(&forall_fact.params_def_with_type, false)
                    .map_err(|e| {
                        StmtError::ExecError(ExecError::new(
                            stmt.stmt_type_name(),
                            "claim: failed to define forall params".to_string(),
                            Some(e.into()),
                            stmt.line_file_index,
                        ))
                    })
                    .and_then(|_| self.exec_claim_stmt_body(stmt));
                self.runtime_context.delete_env();

                self.store_fact_without_well_defined_verified_and_infer(&stmt.fact)?;
                
                body_result
            }
            _ => {
                self.verify_fact_well_defined(&stmt.fact, &VerifyState::new(0, false))
                    .map_err(|e| {
                        StmtError::ExecError(ExecError::new(
                            stmt.stmt_type_name(),
                            "claim: fact is not well defined".to_string(),
                            Some(e.into()),
                            stmt.line_file_index,
                        ))
                    })?;

                self.runtime_context.new_env();
                let result =self.exec_claim_stmt_body(stmt);
                self.runtime_context.delete_env();

                self.store_fact_without_well_defined_verified_and_infer(&stmt.fact)?;

                result
            }
        }
    }
}
