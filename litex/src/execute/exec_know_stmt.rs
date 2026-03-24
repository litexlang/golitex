use super::Runtime;
use crate::error::ExecStmtError;
use crate::infer::InferResult;
use crate::result::NonErrStmtExecResult;
use crate::result::NonFactualStmtSuccess;
use crate::stmt::know_stmt::KnowStmt;
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
                        know_stmt.stmt_type_name(),
                        know_stmt.to_string(),
                        Some(e.into()),
                        vec![],
                        know_stmt.line_file,
                    )
                })?;
            infer_result.append(fact_infer_result);
        }
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                know_stmt.to_string(),
                infer_result,
                vec![],
                know_stmt.line_file,
            ),
        ))
    }
}
