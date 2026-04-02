use crate::prelude::*;

impl Runtime {
    pub fn def_param_type_struct_stmt(
        &mut self,
        def_param_type_struct_stmt: &DefParamTypeStructStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self.def_param_type_struct_stmt_check_well_defined(def_param_type_struct_stmt)?;

        self.store_def_param_type_struct(def_param_type_struct_stmt)
            .map_err(|store_error| {
                ExecStmtError::new_with_stmt(
                    Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                    "".to_string(),
                    Some(store_error.into()),
                    vec![],
                )
            })?;

        let infer_result = InferResult::new();

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(
            Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
            infer_result,
            vec![],
        )))
    }

    fn def_param_type_struct_stmt_check_well_defined(
        &mut self,
        def_param_type_struct_stmt: &DefParamTypeStructStmt,
    ) -> Result<(), ExecStmtError> {
        self.push_env();
        let struct_check_well_defined_result = self
            .def_param_type_struct_stmt_check_well_defined_body(def_param_type_struct_stmt);
        self.pop_env();
        struct_check_well_defined_result
    }

    fn def_param_type_struct_stmt_check_well_defined_body(
        &mut self,
        def_param_type_struct_stmt: &DefParamTypeStructStmt,
    ) -> Result<(), ExecStmtError> {
        let verify_state = VerifyState::new(0, false);

        self.define_params_with_type(
            &ParamDefWithStructFieldType::to_param_defs_with_param_type(
                &def_param_type_struct_stmt.param_defs,
            ),
            false,
        )
            .map_err(|define_params_error| {
                ExecStmtError::new_with_stmt(
                    Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                    "".to_string(),
                    Some(define_params_error.into()),
                    vec![],
                )
            })?;

        for dom_fact in def_param_type_struct_stmt.dom_facts.iter() {
            self
                .verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                    dom_fact,
                    &verify_state,
                )
                .map_err(|inner_exec_error| {
                    ExecStmtError::new_with_stmt(
                        Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                        "".to_string(),
                        Some(RuntimeError::ExecStmtError(inner_exec_error)),
                        vec![],
                    )
                })?;
        }

        for (_, field_param_type) in def_param_type_struct_stmt.fields.iter() {
            self
                .verify_param_type_well_defined(&field_param_type.to_param_type(), &verify_state)
                .map_err(|well_defined_error| {
                    ExecStmtError::new_with_stmt(
                        Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                        "".to_string(),
                        Some(well_defined_error.into()),
                        vec![],
                    )
                })?;
        }

        // 必须先做这一步，再验 `<=>:` 里的 facts：那些事实会引用 `self`、`self.xxx` 等字段访问；
        // 若字段未先经 `define_param_binding_struct_with_def` 绑定（登记 inst_struct、字段类型事实、well-defined 缓存等），
        // 验证器会认为 `self.xxx` 未声明，从而报错。
        //
        // 等价于 `let self struct Name(R, S, ...)`：形参已绑定为标识符，用其实例化 `struct Name(...)` 并登记 inst_struct + 字段类型事实，
        // 使后面事实检查与运行时语义一致。
        let local_def = DefParamTypeStructStmt::new(
            def_param_type_struct_stmt.name.clone(),
            def_param_type_struct_stmt.param_defs.clone(),
            def_param_type_struct_stmt.dom_facts.clone(),
            def_param_type_struct_stmt.fields.clone(),
            vec![],
            def_param_type_struct_stmt.line_file,
        );

        self.store_identifier_obj(SELF).map_err(|store_error| {
            ExecStmtError::new_with_stmt(
                Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                "".to_string(),
                Some(store_error.into()),
                vec![],
            )
        })?;

        let param_names = ParamDefWithStructFieldType::collect_param_names(&local_def.param_defs);
        let struct_params: Vec<Obj> = param_names
            .iter()
            .map(|n| Obj::Identifier(Identifier::new(n.clone())))
            .collect();
        let struct_ty = StructParamType {
            name: IdentifierOrIdentifierWithMod::Identifier(Identifier::new(local_def.name.clone())),
            args: struct_params,
        };

        self.define_param_binding_struct(SELF, &struct_ty)
            .map_err(|runtime_error| {
                ExecStmtError::new_with_stmt(
                    Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                    "".to_string(),
                    Some(runtime_error),
                    vec![],
                )
            })?;

        for fact in def_param_type_struct_stmt.facts.iter() {
            self
                .verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                    fact,
                    &verify_state,
                )
                .map_err(|inner_exec_error| {
                    ExecStmtError::new_with_stmt(
                        Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                        "".to_string(),
                        Some(RuntimeError::ExecStmtError(inner_exec_error)),
                        vec![],
                    )
                })?;
        }

        Ok(())
    }
}
