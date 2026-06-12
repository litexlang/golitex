use crate::prelude::*;

impl Runtime {
    pub fn exec_have_obj_in_nonempty_set_or_param_type_stmt(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let mut infer_result = self
            .define_params_with_type(&stmt.param_def, true, ParamObjType::Identifier)
            .map_err(|define_params_error| {
                exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
            })?;
        infer_result.relabel_all_added_facts(InferReason::ObjectIntroduction);
        let checks = self
            .object_introduction_nonempty_checks_for_param_def(&stmt.param_def)
            .map_err(|check_error| {
                exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), check_error)
            })?;
        Ok((NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, checks)).into())
    }
}
