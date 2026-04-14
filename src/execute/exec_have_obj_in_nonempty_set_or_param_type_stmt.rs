use crate::prelude::*;

impl Runtime {
    pub fn exec_have_obj_in_nonempty_set_or_param_type_stmt(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self
            .define_params_with_type(&stmt.param_def, true)
            .map_err(|define_params_error| {
                let st: Stmt = stmt.clone().into();
                let lf = st.line_file();
                RuntimeErrorStruct::new(
                    Some(st),
                    "".to_string(),
                    lf,
                    Some(define_params_error),
                    vec![],
                )
            })?;
        Ok((NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![])).into())
    }
}
