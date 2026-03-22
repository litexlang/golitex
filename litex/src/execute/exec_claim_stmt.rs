use super::Executor;
use crate::error::StmtError;
use crate::error::{ExecStmtError, UnknownError};
use crate::fact::Fact;
use crate::result::NonErrStmtExecResult;
use crate::result::NonFactualStmtSuccess;
use crate::stmt::claim_stmt::ClaimStmt;
use crate::verify::VerifyState;

impl<'a> Executor<'a> {
    fn exec_claim_stmt_body_fact_except_forall_fact(
        &mut self,
        stmt: &ClaimStmt,
    ) -> Result<NonErrStmtExecResult, StmtError> {
        for proof_stmt in stmt.proof.iter() {
            self.exec_stmt(proof_stmt)?;
        }

        let verify_result = self.verify_fact(&stmt.fact, &VerifyState::new(0, false))?;
        if !verify_result.is_true() {
            return Err(StmtError::UnknownError(UnknownError::new(
                format!("claim failed: cannot prove `{}`", stmt.fact),
                stmt.line_file,
                None,
            )));
        }

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                stmt.to_string(),
                crate::infer::InferResult::new(),
                vec![],
                stmt.line_file,
            ),
        ))
    }

    fn exec_claim_stmt_body_fact_for_forall_fact(
        &mut self,
        stmt: &ClaimStmt,
    ) -> Result<NonErrStmtExecResult, StmtError> {
        // let body_result = self
        //             .define_params_with_type(&forall_fact.params_def_with_type, false)
        //             .map_err(|e| {
        //                 StmtError::ExecError(ExecStmtError::new(
        //                     stmt.stmt_type_name(),
        //                     "claim: failed to define forall params".to_string(),
        //                     Some(e.into()),
        //                     stmt.line_file,
        //                 ))
        //             })
        //             .and_then(|_| self.exec_claim_stmt_body_fact_except_forall_fact(stmt));

        return Err(StmtError::UnknownError(UnknownError::new(
            "not implemented".to_string(),
            stmt.line_file,
            None,
        )));
    }

    pub fn exec_claim_stmt(&mut self, stmt: &ClaimStmt) -> Result<NonErrStmtExecResult, StmtError> {
        match &stmt.fact {
            Fact::ForallFactWithIff(_) => unreachable!("claim forall with iff is not supported"),
            Fact::ForallFact(_) => {
                self.verify_fact_well_defined(&stmt.fact, &VerifyState::new(0, false))
                    .map_err(|e| {
                        StmtError::ExecError(ExecStmtError::new(
                            stmt.stmt_type_name(),
                            "claim: fact is not well defined".to_string(),
                            Some(e.into()),
                            stmt.line_file,
                        ))
                    })?;

                self.runtime_context.new_env();
                let body_result = self.exec_claim_stmt_body_fact_for_forall_fact(stmt);
                self.runtime_context.delete_env();

                if let Err(e) = body_result {
                    return Err(e);
                }

                self.store_fact_without_well_defined_verified_and_infer(&stmt.fact)?;

                body_result
            }
            _ => {
                self.verify_fact_well_defined(&stmt.fact, &VerifyState::new(0, false))
                    .map_err(|e| {
                        StmtError::ExecError(ExecStmtError::new(
                            stmt.stmt_type_name(),
                            "claim: fact is not well defined".to_string(),
                            Some(e.into()),
                            stmt.line_file,
                        ))
                    })?;

                self.runtime_context.new_env();
                let result = self.exec_claim_stmt_body_fact_except_forall_fact(stmt);
                self.runtime_context.delete_env();

                self.store_fact_without_well_defined_verified_and_infer(&stmt.fact)?;

                result
            }
        }
    }
}
