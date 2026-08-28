use crate::prelude::*;

impl Runtime {
    pub fn exec_let_obj_stmt(&mut self, stmt: &LetObjStmt) -> Result<StmtResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&stmt.value, &VerifyState::initial())
            .map_err(|error| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), error))?;

        let infer_result = self.exec_let_obj_stmt_affect_environment(stmt)?;
        Ok(
            SuccessDefinitionStmtResult::LetObjStmt(Box::new(SuccessLetObjStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
            }))
            .into(),
        )
    }

    fn exec_let_obj_stmt_affect_environment(
        &mut self,
        stmt: &LetObjStmt,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_parameter_binding(&stmt.symbol_binding, BindingScope::DefinitionBinding)
            .map_err(|error| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), error))?;

        let defining_equality = EqualFact::new(
            Identifier::new_bound(
                stmt.symbol_binding.name().to_string(),
                stmt.symbol_binding.as_ref(),
            )
            .into(),
            stmt.value.clone(),
            stmt.line_file.clone(),
        );
        let equal_fact: AtomicFact = defining_equality.clone().into();
        let defining_fact: Fact = equal_fact.clone().into();
        let infer_result = self
            .store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                equal_fact,
                LetObjStmt::store_reason(),
            )
            .map_err(|error| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), error))?;
        let defining_equality_fact_id = self
            .require_known_fact_id_for_success_result(&defining_fact)
            .map_err(|error| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), error))?;
        let definition = TransparentObjectDefinition::new(
            stmt.value.clone(),
            defining_equality,
            defining_equality_fact_id,
        );
        self.top_level_env()
            .definitions
            .symbols
            .get_by_id_mut(stmt.symbol_binding.id())
            .expect("the let symbol was registered before its defining equality")
            .remember_transparent_object_definition(definition)
            .map_err(|_| {
                exec_stmt_error_with_stmt_and_cause(
                    stmt.clone().into(),
                    UnknownRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "conflicting transparent definition for `{}`",
                            stmt.symbol_binding.name()
                        ),
                        stmt.line_file.clone(),
                    ))
                    .into(),
                )
            })?;
        Ok(infer_result)
    }

    pub fn exec_let_obj_stmt_affect_environment_only(
        &mut self,
        stmt: &LetObjStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_let_obj_stmt_affect_environment(stmt)?;
        Ok(
            SuccessDefinitionStmtResult::LetObjStmt(Box::new(SuccessLetObjStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
            }))
            .into(),
        )
    }
}
