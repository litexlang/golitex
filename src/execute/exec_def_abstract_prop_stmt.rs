use crate::prelude::*;

impl Runtime {
    pub fn exec_def_abstract_prop_stmt(
        &mut self,
        def_abstract_prop_stmt: &DefAbstractPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.store_def_abstract_prop(def_abstract_prop_stmt)
            .map_err(|e| {
                short_exec_error(def_abstract_prop_stmt.clone().into(), "", Some(e), vec![])
            })?;
        Ok((NonFactualStmtSuccess::new(
            def_abstract_prop_stmt.clone().into(),
            InferResult::new(),
            vec![],
        ))
        .into())
    }
}
