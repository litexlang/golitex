use crate::prelude::*;

impl Runtime {
    pub fn execute_statement(&mut self, stmt: &Stmt) -> Result<StmtResult, RuntimeError> {
        self.execute_statement_with_trusted_prefix_context(stmt, false)
    }

    /// Compatibility wrapper for the former abbreviated entry point.
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> Result<StmtResult, RuntimeError> {
        self.execute_statement(stmt)
    }

    pub fn execute_statement_in_trusted_prefix_run(
        &mut self,
        stmt: &Stmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.execute_statement_with_trusted_prefix_context(stmt, true)
    }

    /// Compatibility wrapper for the former abbreviated trusted-prefix entry.
    pub fn exec_stmt_in_trusted_prefix_run(
        &mut self,
        stmt: &Stmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.execute_statement_in_trusted_prefix_run(stmt)
    }

    fn execute_statement_with_trusted_prefix_context(
        &mut self,
        stmt: &Stmt,
        in_trusted_prefix_run: bool,
    ) -> Result<StmtResult, RuntimeError> {
        self.clear_statement_proof_state();
        let trusted = self.current_execution_is_trusted_file();
        let result = if trusted {
            self.execute_statement_without_verification(stmt, in_trusted_prefix_run)
        } else {
            // The generated local-builtin catalog is parsed once per thread.
            // Do that work at the shallow statement boundary instead of on
            // first use from deep inside object/fact verification: the parser
            // intentionally has many precedence layers, and nesting that
            // one-time compilation below a recursive verifier can exhaust a
            // normal test thread's stack in debug builds.
            crate::verify::local_builtin_catalog::registered_local_builtin_rules()
                .and_then(|_| self.execute_verified_statement(stmt))
        };
        let result = self.finish_statement_execution_with_trusted_prefix_context(
            result,
            trusted,
            in_trusted_prefix_run,
        );
        self.clear_statement_proof_state();
        result
    }

    pub fn finish_statement_execution(
        &mut self,
        result: Result<StmtResult, RuntimeError>,
        trusted: bool,
    ) -> Result<StmtResult, RuntimeError> {
        self.finish_statement_execution_with_trusted_prefix_context(result, trusted, false)
    }

    pub fn finish_statement_execution_in_trusted_prefix_run(
        &mut self,
        result: Result<StmtResult, RuntimeError>,
        trusted: bool,
    ) -> Result<StmtResult, RuntimeError> {
        self.finish_statement_execution_with_trusted_prefix_context(result, trusted, true)
    }

    fn finish_statement_execution_with_trusted_prefix_context(
        &mut self,
        result: Result<StmtResult, RuntimeError>,
        trusted: bool,
        in_trusted_prefix_run: bool,
    ) -> Result<StmtResult, RuntimeError> {
        match result {
            Ok(mut result) => {
                self.attach_known_fact_ids_to_stmt_result(&mut result)?;
                let trace = if in_trusted_prefix_run && !result.is_unknown() {
                    if trusted {
                        StatementExecutionTrace::trusted_prefix()
                    } else {
                        StatementExecutionTrace::verified(false).with_verified_status()
                    }
                } else if trusted {
                    StatementExecutionTrace::trusted()
                } else {
                    StatementExecutionTrace::verified(result.is_unknown())
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
