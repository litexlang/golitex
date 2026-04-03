use crate::prelude::*;

impl Runtime {
    pub fn def_param_type_struct_stmt(
        &mut self,
        def_param_type_struct_stmt: &DefParamTypeStructStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeErrorStruct> {
        self.def_param_type_struct_stmt_check_well_defined(def_param_type_struct_stmt)?;

        self.store_struct_def(def_param_type_struct_stmt)
            .map_err(|store_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                    "".to_string(),
                    Some(store_error.into()),
                    vec![],
                )
            })?;

        let infer_result = InferResult::new();

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                infer_result,
                vec![],
            ),
        ))
    }

    fn def_param_type_struct_stmt_check_well_defined(
        &mut self,
        def_param_type_struct_stmt: &DefParamTypeStructStmt,
    ) -> Result<(), RuntimeErrorStruct> {
        self.push_env();
        let struct_check_well_defined_result =
            self.def_param_type_struct_stmt_check_well_defined_body(def_param_type_struct_stmt);
        self.pop_env();
        struct_check_well_defined_result
    }

    fn def_param_type_struct_stmt_check_well_defined_body(
        &mut self,
        def_param_type_struct_stmt: &DefParamTypeStructStmt,
    ) -> Result<(), RuntimeErrorStruct> {
        let verify_state = VerifyState::new(0, false);

        self.define_params_with_type(
            &ParamDefWithStructFieldTypeTuple::to_param_defs_with_param_type(
                &def_param_type_struct_stmt.param_defs,
            ),
            false,
        )
        .map_err(|define_params_error| {
            RuntimeErrorStruct::exec_stmt_new_with_stmt(
                Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                "".to_string(),
                Some(define_params_error),
                vec![],
            )
        })?;

        for dom_fact in def_param_type_struct_stmt.dom_facts.iter() {
            self.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                dom_fact,
                &verify_state,
            )
            .map_err(|inner_exec_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                    "".to_string(),
                    Some(RuntimeError::from(inner_exec_error)),
                    vec![],
                )
            })?;
        }

        for (_, field_param_type) in def_param_type_struct_stmt.fields.iter() {
            self.verify_param_type_well_defined(&field_param_type.to_param_type(), &verify_state)
                .map_err(|well_defined_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                        "".to_string(),
                        Some(well_defined_error.into()),
                        vec![],
                    )
                })?;
        }

        self.store_identifier_obj(SELF).map_err(|store_error| {
            RuntimeErrorStruct::exec_stmt_new_with_stmt(
                Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                "".to_string(),
                Some(store_error.into()),
                vec![],
            )
        })?;

        let mut struct_params = vec![];
        for param_def in def_param_type_struct_stmt.param_defs.iter() {
            for field in param_def.0.iter() {
                struct_params.push(Obj::Identifier(Identifier::new(field.clone())));
            }
        }

        self.register_param_as_struct_instance(
            SELF,
            StructParamType::new(
                IdentifierOrIdentifierWithMod::Identifier(Identifier::new(
                    def_param_type_struct_stmt.name.clone(),
                )),
                struct_params,
            ),
        );

        let tmp_def = DefParamTypeStructStmt::new(
            def_param_type_struct_stmt.name.clone(),
            def_param_type_struct_stmt.param_defs.clone(),
            def_param_type_struct_stmt.dom_facts.clone(),
            def_param_type_struct_stmt.fields.clone(),
            vec![],
            def_param_type_struct_stmt.line_file.clone(),
        );

        self.store_struct_def(&tmp_def)?;

        for fact in def_param_type_struct_stmt.facts.iter() {
            self.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                fact,
                &verify_state,
            )
            .map_err(|inner_exec_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                    "".to_string(),
                    Some(RuntimeError::from(inner_exec_error)),
                    vec![],
                )
            })?;
        }

        Ok(())
    }
}
