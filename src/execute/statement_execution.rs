use crate::error::RuntimeError;
use crate::result::{StatementExecutionPhase, StatementExecutionTrace, StmtResult};
use crate::runtime::{ExecutionMode, Runtime};
use crate::stmt::Stmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum StatementExecutionContext {
    OrdinaryRun,
    TrustedPrefixRun,
}

impl StatementExecutionContext {
    fn is_trusted_prefix_run(self) -> bool {
        self == Self::TrustedPrefixRun
    }
}

impl Runtime {
    pub fn execute_statement(&mut self, stmt: &Stmt) -> Result<StmtResult, RuntimeError> {
        self.execute_statement_with_context(stmt, StatementExecutionContext::OrdinaryRun)
    }

    pub fn execute_statement_in_trusted_prefix_run(
        &mut self,
        stmt: &Stmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.execute_statement_with_context(stmt, StatementExecutionContext::TrustedPrefixRun)
    }

    fn execute_statement_with_context(
        &mut self,
        stmt: &Stmt,
        context: StatementExecutionContext,
    ) -> Result<StmtResult, RuntimeError> {
        self.clear_statement_proof_state();
        let execution_mode = self.current_execution_mode();
        let result = match execution_mode {
            ExecutionMode::Trusted => self.execute_statement_without_verification(stmt, context),
            ExecutionMode::Verified => {
                // The generated local-builtin catalog is parsed once per thread.
                // Do that work at the shallow statement boundary instead of on
                // first use from deep inside object/fact verification: the parser
                // intentionally has many precedence layers, and nesting that
                // one-time compilation below a recursive verifier can exhaust a
                // normal test thread's stack in debug builds.
                crate::verify::local_builtin_catalog::registered_local_builtin_rules()
                    .and_then(|_| self.execute_verified_statement(stmt))
            }
        };
        let result = self.finish_statement_execution_with_context(result, execution_mode, context);
        self.clear_statement_proof_state();
        result
    }

    pub fn finish_statement_execution(
        &mut self,
        result: Result<StmtResult, RuntimeError>,
        execution_mode: ExecutionMode,
    ) -> Result<StmtResult, RuntimeError> {
        self.finish_statement_execution_with_context(
            result,
            execution_mode,
            StatementExecutionContext::OrdinaryRun,
        )
    }

    pub fn finish_statement_execution_in_trusted_prefix_run(
        &mut self,
        result: Result<StmtResult, RuntimeError>,
        execution_mode: ExecutionMode,
    ) -> Result<StmtResult, RuntimeError> {
        self.finish_statement_execution_with_context(
            result,
            execution_mode,
            StatementExecutionContext::TrustedPrefixRun,
        )
    }

    fn finish_statement_execution_with_context(
        &mut self,
        result: Result<StmtResult, RuntimeError>,
        execution_mode: ExecutionMode,
        context: StatementExecutionContext,
    ) -> Result<StmtResult, RuntimeError> {
        match result {
            Ok(mut result) => {
                self.attach_known_fact_ids_to_stmt_result(&mut result)?;
                let trace = match (
                    context.is_trusted_prefix_run(),
                    execution_mode,
                    result.is_unknown(),
                ) {
                    (true, ExecutionMode::Trusted, false) => {
                        StatementExecutionTrace::trusted_prefix()
                    }
                    (true, ExecutionMode::Verified, false) => {
                        StatementExecutionTrace::verified(false).with_verified_status()
                    }
                    (_, ExecutionMode::Trusted, _) => StatementExecutionTrace::trusted(),
                    (_, ExecutionMode::Verified, process_is_unknown) => {
                        StatementExecutionTrace::verified(process_is_unknown)
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
