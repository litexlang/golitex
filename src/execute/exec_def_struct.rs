use crate::prelude::*;

impl Runtime {
    pub fn exec_def_struct_stmt(
        &mut self,
        stmt: &DefStructStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeErrorStruct> {
        self.def_struct_stmt_check_well_defined(stmt)?;

        self.store_struct_def(stmt).map_err(|store_error| {
            RuntimeErrorStruct::exec_stmt_new_with_stmt(
                Stmt::DefStructStmt(stmt.clone()),
                "".to_string(),
                Some(store_error.into()),
                vec![],
            )
        })?;

        let infer_result = InferResult::new();

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(Stmt::DefStructStmt(stmt.clone()), infer_result, vec![]),
        ))
    }

    fn def_struct_stmt_check_well_defined(
        &mut self,
        stmt: &DefStructStmt,
    ) -> Result<(), RuntimeErrorStruct> {
        self.push_env();
        let struct_check_well_defined_result = self.def_struct_stmt_check_well_defined_body(stmt);
        self.pop_env();
        struct_check_well_defined_result
    }

    fn def_struct_stmt_check_well_defined_body(
        &mut self,
        stmt: &DefStructStmt,
    ) -> Result<(), RuntimeErrorStruct> {
        let verify_state = VerifyState::new(0, false);

        self.define_params_with_type(
            &ParamGroupWithStructFieldType::to_param_groups_with_param_type(&stmt.param_defs),
            false,
        )
        .map_err(|define_params_error| {
            RuntimeErrorStruct::exec_stmt_new_with_stmt(
                Stmt::DefStructStmt(stmt.clone()),
                "".to_string(),
                Some(define_params_error),
                vec![],
            )
        })?;

        for dom_fact in stmt.dom_facts.iter() {
            self.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                dom_fact,
                &verify_state,
            )
            .map_err(|inner_exec_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    Stmt::DefStructStmt(stmt.clone()),
                    "".to_string(),
                    Some(RuntimeError::from(inner_exec_error)),
                    vec![],
                )
            })?;
        }

        for (_, field_param_type) in stmt.fields.iter() {
            self.verify_param_type_well_defined(&field_param_type.to_param_type(), &verify_state)
                .map_err(|well_defined_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        Stmt::DefStructStmt(stmt.clone()),
                        "".to_string(),
                        Some(well_defined_error.into()),
                        vec![],
                    )
                })?;
        }

        self.store_identifier_obj(SELF).map_err(|store_error| {
            RuntimeErrorStruct::exec_stmt_new_with_stmt(
                Stmt::DefStructStmt(stmt.clone()),
                "".to_string(),
                Some(store_error.into()),
                vec![],
            )
        })?;

        let mut struct_params = vec![];
        for param_def in stmt.param_defs.iter() {
            for field in param_def.params.iter() {
                struct_params.push(Obj::Identifier(Identifier::new(field.clone())));
            }
        }

        self.register_param_as_struct_instance(
            SELF,
            StructParamType::new(
                IdentifierOrIdentifierWithMod::Identifier(Identifier::new(stmt.name.clone())),
                struct_params,
            ),
        );

        let tmp_def = DefStructStmt::new(
            stmt.name.clone(),
            stmt.param_defs.clone(),
            stmt.dom_facts.clone(),
            stmt.fields.clone(),
            vec![],
            stmt.line_file.clone(),
        );

        self.store_struct_def(&tmp_def)?;

        for fact in stmt.facts.iter() {
            self.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                fact,
                &verify_state,
            )
            .map_err(|inner_exec_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    Stmt::DefStructStmt(stmt.clone()),
                    "".to_string(),
                    Some(RuntimeError::from(inner_exec_error)),
                    vec![],
                )
            })?;
        }

        Ok(())
    }
}
