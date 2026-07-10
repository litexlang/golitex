use crate::prelude::*;

impl Runtime {
    pub fn exec_export_stmt(&mut self, stmt: &ExportStmt) -> Result<StmtResult, RuntimeError> {
        let message = if self.run_mode == RunMode::File {
            "export is unavailable in isolated file mode; declare exports in mod.lit and run the project with -r"
        } else {
            "export is declarative and can only appear in mod.lit"
        };
        Err(short_exec_error(
            stmt.clone().into(),
            message.to_string(),
            None,
            vec![],
        ))
    }

    pub fn exec_local_import_stmt(
        &mut self,
        stmt: &LocalImportStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let message = if self.run_mode == RunMode::File {
            "local_import is unavailable in isolated file mode; run a project with -r"
        } else {
            "local_import can only be run as a top-level statement"
        };
        Err(short_exec_error(
            stmt.clone().into(),
            message.to_string(),
            None,
            vec![],
        ))
    }

    pub fn exec_import_stmt(&mut self, stmt: &ImportStmt) -> Result<StmtResult, RuntimeError> {
        return Err(RuntimeError::ExecStmtError({
            let st: Stmt = stmt.clone().into();
            let lf = st.line_file();
            RuntimeErrorStruct::new(
                Some(st),
                "import can only be run as a top-level statement".to_string(),
                lf,
                None,
                vec![],
            )
        }));
    }

    pub fn exec_do_nothing_stmt(
        &mut self,
        stmt: &DoNothingStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_do_nothing_stmt_verify_well_definedness(stmt)?;
        let inside_results = self.exec_do_nothing_stmt_verify_process(stmt)?;
        let infer_result = self.exec_do_nothing_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, inside_results).into())
    }

    pub fn exec_clear_stmt(&mut self, stmt: &ClearStmt) -> Result<StmtResult, RuntimeError> {
        self.exec_clear_stmt_verify_well_definedness(stmt)?;
        let inside_results = self.exec_clear_stmt_verify_process(stmt)?;
        let infer_result = self.exec_clear_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, inside_results).into())
    }

    pub fn exec_stop_import_stmt(
        &mut self,
        stmt: &StopImportStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_stop_import_stmt_verify_well_definedness(stmt)?;
        let inside_results = self.exec_stop_import_stmt_verify_process(stmt)?;
        let infer_result = self.exec_stop_import_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, inside_results).into())
    }

    fn exec_do_nothing_stmt_verify_well_definedness(
        &mut self,
        _stmt: &DoNothingStmt,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn exec_do_nothing_stmt_verify_process(
        &mut self,
        _stmt: &DoNothingStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        Ok(vec![])
    }

    fn exec_do_nothing_stmt_affect_environment(
        &mut self,
        _stmt: &DoNothingStmt,
    ) -> Result<InferResult, RuntimeError> {
        Ok(InferResult::new())
    }

    fn exec_clear_stmt_verify_well_definedness(
        &mut self,
        _stmt: &ClearStmt,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn exec_clear_stmt_verify_process(
        &mut self,
        _stmt: &ClearStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        Ok(vec![])
    }

    fn exec_clear_stmt_affect_environment(
        &mut self,
        _stmt: &ClearStmt,
    ) -> Result<InferResult, RuntimeError> {
        self.clear_current_env_and_parse_name_scope();
        Ok(InferResult::new())
    }

    fn exec_stop_import_stmt_verify_well_definedness(
        &mut self,
        _stmt: &StopImportStmt,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn exec_stop_import_stmt_verify_process(
        &mut self,
        stmt: &StopImportStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let module_was_imported = self
            .module_manager
            .module_by_import_name(&stmt.module_name)
            .is_some_and(|module| module.status != ModuleStatus::Discovered);
        if !module_was_imported {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!("module `{}` has not been imported", stmt.module_name),
                None,
                vec![],
            ));
        }
        Ok(vec![])
    }

    fn exec_stop_import_stmt_affect_environment(
        &mut self,
        stmt: &StopImportStmt,
    ) -> Result<InferResult, RuntimeError> {
        self.module_manager
            .stop_imported_module(&stmt.module_name)
            .map_err(|msg| short_exec_error(stmt.clone().into(), msg, None, vec![]))?;
        Ok(InferResult::new())
    }

    pub fn exec_run_file_stmt(&mut self, stmt: &RunFileStmt) -> Result<StmtResult, RuntimeError> {
        return Err(RuntimeError::ExecStmtError({
            let st: Stmt = stmt.clone().into();
            let lf = st.line_file();
            RuntimeErrorStruct::new(
                Some(st),
                format!(
                    "{} can only be run as a top-level statement",
                    stmt.keyword()
                ),
                lf,
                None,
                vec![],
            )
        }));
    }
}
