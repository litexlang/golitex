use crate::prelude::*;

impl Runtime {
    pub fn exec_def_abstract_prop_stmt(
        &mut self,
        def_abstract_prop_stmt: &DefAbstractPropStmt,
    ) -> Result<StmtResult, RuntimeErrorStruct> {
        self.store_def_abstract_prop(def_abstract_prop_stmt)
            .map_err(|e| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    def_abstract_prop_stmt.clone().into(),
                    "".to_string(),
                    Some(RuntimeError::ExecStmtError(e)),
                    vec![],
                )
            })?;
        Ok((NonFactualStmtSuccess::new(
            def_abstract_prop_stmt.clone().into(),
            InferResult::new(),
            vec![],
        ))
        .into())
    }
}
