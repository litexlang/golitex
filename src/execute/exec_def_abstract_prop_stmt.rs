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
        let mut infers = InferResult::new();
        infers.add_abstract_prop_definition(
            def_abstract_prop_stmt.name.as_str(),
            &def_abstract_prop_stmt.params,
        );
        Ok(
            NonFactualStmtSuccess::new(def_abstract_prop_stmt.clone().into(), infers, vec![])
                .into(),
        )
    }
}
