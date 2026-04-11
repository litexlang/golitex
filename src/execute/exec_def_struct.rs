use crate::prelude::*;
use std::collections::HashSet;

impl Runtime {
    pub fn exec_def_struct_stmt(
        &mut self,
        stmt: &DefStructStmt,
    ) -> Result<StmtExecResult, RuntimeErrorStruct> {
        self.run_in_local_env(|rt| rt.def_struct_stmt_check_well_defined(stmt))?;

        self.store_struct_def(stmt).map_err(|store_error| {
            RuntimeErrorStruct::exec_stmt_new_with_stmt(
                Stmt::DefStructStmt(stmt.clone()),
                "".to_string(),
                Some(store_error.into()),
                vec![],
            )
        })?;

        let infer_result = InferResult::new();

        Ok(StmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(Stmt::DefStructStmt(stmt.clone()), infer_result, vec![]),
        ))
    }

    fn def_struct_stmt_check_well_defined(
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

        // struct 的参数和 field 不应该冲突, 比如 struct p(a set): a set 这样。虽然本质上好像不影响，但这样会看起来很怪。
        let param_names: HashSet<String> = stmt.get_params().into_iter().collect();
        for (field_name, _) in stmt.fields.iter() {
            if param_names.contains(field_name) {
                return Err(RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    Stmt::DefStructStmt(stmt.clone()),
                    format!(
                        "struct `{}`: field `{}` must not reuse a type parameter name",
                        stmt.name, field_name
                    ),
                    None,
                    vec![],
                ));
            }
        }

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
            StructObj::new(
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
