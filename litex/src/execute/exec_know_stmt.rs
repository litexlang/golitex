use super::Runtime;
use crate::error::ExecStmtError;
use crate::infer::InferResult;
use crate::result::NonErrStmtExecResult;
use crate::result::NonFactualStmtSuccess;
use crate::stmt::know_stmt::KnowStmt;
use crate::stmt::Stmt;
use crate::verify::VerifyState;

impl<'a> Runtime<'a> {
    pub fn exec_know_stmt(
        &mut self,
        know_stmt: &KnowStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        let mut infer_result = InferResult::new();
        for fact in know_stmt.facts.iter() {
            let fact_infer_result = self
                .verify_fact_well_defined_and_store_and_infer(fact, &VerifyState::new(0, false))
                .map_err(|e| {
                    ExecStmtError::new(
                        Stmt::KnowStmt(know_stmt.clone()),
                        Some(e.into()),
                        vec![],
                    )
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::KnowStmt(know_stmt.clone()),
                infer_result,
                vec![],
            ),
        ))
    }
}
