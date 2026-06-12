use crate::prelude::*;

impl Runtime {
    pub fn exec_alias_prop_stmt(
        &mut self,
        stmt: &AliasPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let target_name = stmt.target_name.to_string();
        if self
            .get_abstract_prop_definition_by_name(&target_name)
            .is_some()
        {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "alias prop: `{}` is an abstract_prop; alias prop only supports concrete prop definitions",
                    target_name
                ),
                None,
                vec![],
            ));
        }
        let mut target = self
            .get_prop_definition_by_name(&target_name)
            .ok_or_else(|| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("alias prop: prop `{}` is not defined", target_name),
                    None,
                    vec![],
                )
            })?;
        target.name = stmt.new_name.clone();
        target.line_file = stmt.line_file.clone();
        self.store_def_prop(&target)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;
        Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone().into()).into())
    }

    pub fn exec_alias_thm_stmt(&mut self, stmt: &AliasThmStmt) -> Result<StmtResult, RuntimeError> {
        let target_name = stmt.target_name.to_string();
        let mut target = self
            .get_thm_definition_by_name(&target_name)
            .ok_or_else(|| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("alias thm: theorem `{}` is not defined", target_name),
                    None,
                    vec![],
                )
            })?;
        target.names = vec![stmt.new_name.clone()];
        target.line_file = stmt.line_file.clone();
        self.store_def_thm(&target)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;
        Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone().into()).into())
    }
}
