use crate::prelude::*;

impl Runtime {
    pub fn exec_have_obj_in_nonempty_set_or_param_type_stmt(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_have_obj_in_nonempty_set_or_param_type_stmt_verify_well_definedness(stmt)?;
        let checks = self.exec_have_obj_in_nonempty_set_or_param_type_stmt_verify_process(stmt)?;
        let infer_result =
            self.exec_have_obj_in_nonempty_set_or_param_type_stmt_affect_environment(stmt)?;
        Ok((NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, checks)).into())
    }

    fn exec_have_obj_in_nonempty_set_or_param_type_stmt_verify_well_definedness(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<(), RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.define_params_with_type(&stmt.param_def, false, ParamObjType::Identifier)
                .map_err(|define_params_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
                })?;
            Ok(())
        })
    }

    fn exec_have_obj_in_nonempty_set_or_param_type_stmt_verify_process(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.define_params_with_type(&stmt.param_def, false, ParamObjType::Identifier)
                .map_err(|define_params_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
                })?;
            rt.object_introduction_nonempty_checks_for_param_def(&stmt.param_def)
                .map_err(|check_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), check_error)
                })
        })
    }

    pub(crate) fn exec_have_obj_in_nonempty_set_or_param_type_stmt_affect_environment(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = self
            .define_params_with_type(&stmt.param_def, false, ParamObjType::Identifier)
            .map_err(|define_params_error| {
                exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
            })?;
        infer_result.relabel_all_added_facts_with_store_reason(
            HaveObjInNonemptySetOrParamTypeStmt::store_reason(),
        );
        Ok(infer_result)
    }
}
