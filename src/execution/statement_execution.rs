use crate::error::RuntimeError;
use crate::result::{StatementExecutionPhase, StatementExecutionTrace, StmtResult};
use crate::runtime::{ExecutionMode, Runtime};
use crate::statement::Stmt;

impl Runtime {
    pub fn execute_statement(&mut self, stmt: &Stmt) -> Result<StmtResult, RuntimeError> {
        self.clear_statement_proof_state();
        let execution_mode = self.current_execution_mode();
        let result = match execution_mode {
            ExecutionMode::Trusted => self.execute_statement_without_verification(stmt),
            ExecutionMode::RequireVerification => self.execute_verified_statement(stmt),
        };
        let result = self.finish_statement_execution(result, execution_mode);
        self.clear_statement_proof_state();
        result
    }

    pub fn finish_statement_execution(
        &mut self,
        result: Result<StmtResult, RuntimeError>,
        execution_mode: ExecutionMode,
    ) -> Result<StmtResult, RuntimeError> {
        match result {
            Ok(mut result) => {
                self.attach_known_fact_ids_to_stmt_result(&mut result)?;
                let trace = match execution_mode {
                    ExecutionMode::Trusted => StatementExecutionTrace::trusted(),
                    ExecutionMode::RequireVerification => {
                        StatementExecutionTrace::verified(result.is_unknown())
                    }
                };
                let result = result.with_execution_trace(trace);
                Ok(result)
            }
            Err(error) => {
                let phase = execution_phase_for_error(&error);
                let message = error.trace_message();
                Err(error.with_execution_trace(StatementExecutionTrace::failed(phase, message)))
            }
        }
    }
}

fn execution_phase_for_error(error: &RuntimeError) -> StatementExecutionPhase {
    match error {
        RuntimeError::StoreFactError(_) | RuntimeError::InferError(_) => {
            StatementExecutionPhase::AffectEnvironment
        }
        RuntimeError::WellDefinedError(_)
        | RuntimeError::DefineParamsError(_)
        | RuntimeError::InstantiateError(_)
        | RuntimeError::NameAlreadyUsedError(_) => StatementExecutionPhase::VerifyWellDefinedness,
        RuntimeError::ExecStmtError(error) => {
            if let Some(previous_error) = error.previous_error.as_ref() {
                return execution_phase_for_error(previous_error);
            }
            StatementExecutionPhase::VerifyProcess
        }
        RuntimeError::ArithmeticError(_)
        | RuntimeError::NewFactError(_)
        | RuntimeError::ParseError(_)
        | RuntimeError::VerifyError(_)
        | RuntimeError::UnknownError(_) => StatementExecutionPhase::VerifyProcess,
    }
}
