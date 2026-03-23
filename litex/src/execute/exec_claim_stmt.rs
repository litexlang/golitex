use super::Runtime;
use crate::error::StmtError;
use crate::error::{ExecStmtError, UnknownError};
use crate::fact::Fact;
use crate::fact::ForallFact;
use crate::result::NonErrStmtExecResult;
use crate::result::NonFactualStmtSuccess;
use crate::stmt::claim_stmt::ClaimStmt;
use crate::verify::VerifyState;

impl<'a> Runtime<'a> {
    fn exec_claim_stmt_body_fact_for_forall_fact(
        &mut self,
        stmt: &ClaimStmt,
        forall_fact: &ForallFact,
    ) -> Result<NonErrStmtExecResult, StmtError> {
        self.define_params_with_type(&forall_fact.params_def_with_type, false)
            .map_err(|e| {
                StmtError::ExecError(ExecStmtError::new(
                    stmt.stmt_type_name(),
                    "claim: failed to define forall params".to_string(),
                    Some(e.into()),
                    stmt.line_file,
                ))
            })?;

        for proof_stmt in stmt.proof.iter() {
            self.exec_stmt(proof_stmt)?;
        }

        for then_fact in forall_fact.then_facts.iter() {
            let result =
                self.verify_exist_or_and_chain_atomic_fact(then_fact, &VerifyState::new(0, false))?;
            if !result.is_true() {
                return Err(StmtError::UnknownError(UnknownError::new(
                    format!("claim failed: cannot prove `{}`", stmt.fact),
                    stmt.line_file,
                    None,
                )));
            }
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

    pub fn exec_claim_stmt(&mut self, stmt: &ClaimStmt) -> Result<NonErrStmtExecResult, StmtError> {
        match &stmt.fact {
            Fact::ForallFactWithIff(_) => unreachable!("claim forall with iff is not supported"),
            Fact::ForallFact(forall_fact) => {
                self.verify_fact_well_defined(&stmt.fact, &VerifyState::new(0, false))
                    .map_err(|e| {
                        StmtError::ExecError(ExecStmtError::new(
                            stmt.stmt_type_name(),
                            "claim: fact is not well defined".to_string(),
                            Some(e.into()),
                            stmt.line_file,
                        ))
                    })?;

                self.runtime_context.push_env();
                let body_result =
                    self.exec_claim_stmt_body_fact_for_forall_fact(stmt, &forall_fact);
                self.runtime_context.pop_env();

                if let Err(e) = body_result {
                    return Err(e);
                } else if let Ok(result) = body_result {
                    if !result.is_true() {
                        return Err(StmtError::UnknownError(UnknownError::new(
                            format!("claim failed: cannot prove `{}`", stmt.fact),
                            stmt.line_file,
                            None,
                        )));
                    }
                }

                self.store_fact_without_well_defined_verified_and_infer(&stmt.fact)?;

                Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
                    NonFactualStmtSuccess::new(
                        stmt.to_string(),
                        crate::infer::InferResult::new(),
                        vec![],
                        stmt.line_file,
                    ),
                ))
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

                self.runtime_context.push_env();
                let result = self.exec_claim_stmt_body_fact_except_forall_fact(stmt);
                self.runtime_context.pop_env();

                self.store_fact_without_well_defined_verified_and_infer(&stmt.fact)?;

                result
            }
        }
    }
}
