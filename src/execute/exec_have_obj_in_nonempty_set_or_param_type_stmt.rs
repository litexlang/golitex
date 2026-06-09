use crate::prelude::*;

impl Runtime {
    pub fn exec_have_obj_in_nonempty_set_or_param_type_stmt(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self
            .define_params_with_type(&stmt.param_def, true, ParamObjType::Identifier)
            .map_err(|define_params_error| {
                exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
            })?;
        let checks = self
            .object_introduction_nonempty_checks_for_param_def(&stmt.param_def)
            .map_err(|check_error| {
                exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), check_error)
            })?;
        let introduces = self.object_introduction_items_for_defined_params(
            &stmt.param_def,
            stmt.line_file.clone(),
            ParamObjType::Identifier,
        );
        Ok((NonFactualStmtSuccess::new_with_accepted_by(
            stmt.clone().into(),
            infer_result,
            checks,
            AcceptedByResult::object_introduction(introduces),
        ))
        .into())
    }
}
