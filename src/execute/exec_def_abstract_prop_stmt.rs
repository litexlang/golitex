use crate::prelude::*;

impl Runtime {
    pub fn exec_def_abstract_prop_stmt(
        &mut self,
        def_abstract_prop_stmt: &DefAbstractPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.store_def_abstract_prop(def_abstract_prop_stmt)
            .map_err(|e| {
                let __stmt: Stmt = def_abstract_prop_stmt.clone().into();
                let __line_file = __stmt.line_file();
                RuntimeErrorStruct::new(Some(__stmt), "".to_string(), __line_file, Some(e), vec![])
            })?;
        Ok((NonFactualStmtSuccess::new(
            def_abstract_prop_stmt.clone().into(),
            InferResult::new(),
            vec![],
        ))
        .into())
    }
}
