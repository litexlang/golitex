use crate::prelude::*;

impl Runtime {
    pub fn exec_def_abstract_prop_stmt(
        &mut self,
        def_abstract_prop_stmt: &DefAbstractPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.store_def_abstract_prop(def_abstract_prop_stmt)
            .map_err(|e| {
                exec_stmt_error_with_stmt_and_cause(def_abstract_prop_stmt.clone().into(), e)
            })?;
        Ok(NonFactualStmtSuccess::new_with_stmt(def_abstract_prop_stmt.clone().into()).into())
    }
}
