use crate::prelude::*;

impl Runtime {
    pub fn exec_let_stmt(&mut self, def_let_stmt: &DefLetStmt) -> Result<StmtResult, RuntimeError> {
        self.exec_let_stmt_verify_well_definedness(def_let_stmt)?;
        self.exec_let_stmt_verify_process(def_let_stmt)?;
        let infer_result = self.exec_let_stmt_affect_environment(def_let_stmt)?;
        Ok(NonFactualStmtSuccess::new(def_let_stmt.clone().into(), infer_result, vec![]).into())
    }

    fn exec_let_stmt_verify_well_definedness(
        &mut self,
        _def_let_stmt: &DefLetStmt,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn exec_let_stmt_verify_process(
        &mut self,
        def_let_stmt: &DefLetStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        if self.strict_mode_applies_to_current_module() {
            return Err(short_exec_error(
                def_let_stmt.clone().into(),
                DefLetStmt::strict_mode_rejection_message(),
                None,
                vec![],
            ));
        }
        Ok(vec![])
    }

    pub(crate) fn exec_let_stmt_affect_environment(
        &mut self,
        def_let_stmt: &DefLetStmt,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = if self.current_execution_is_trusted_file() {
            self.define_params_with_type_trusted(&def_let_stmt.param_def, ParamObjType::Identifier)
        } else {
            self.define_params_with_type(&def_let_stmt.param_def, false, ParamObjType::Identifier)
        }
        .map_err(|e| exec_stmt_error_with_stmt_and_cause(def_let_stmt.clone().into(), e))?;
        for fact in def_let_stmt.facts.iter() {
            let fact_infer_result = if self.current_execution_is_trusted_file() {
                self.store_trusted_fact_and_infer_with_reason(fact.clone(), InferReason::LetBinding)
            } else {
                self.verify_fact_well_defined_and_store_and_infer_with_reason(
                    fact.clone(),
                    &VerifyState::new(0, false),
                    InferReason::LetBinding,
                )
            }
            .map_err(|inner_exec_error| {
                exec_stmt_error_with_stmt_and_cause(def_let_stmt.clone().into(), inner_exec_error)
            })?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }
        Ok(infer_result)
    }

    pub(crate) fn exec_let_stmt_affect_environment_only(
        &mut self,
        def_let_stmt: &DefLetStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_let_stmt_affect_environment(def_let_stmt)?;
        Ok(NonFactualStmtSuccess::new(def_let_stmt.clone().into(), infer_result, vec![]).into())
    }
}
