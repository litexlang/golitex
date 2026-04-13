use crate::prelude::*;

impl Runtime {
    /// `by family: family p(R)` — 存储 `family p(R) =` 定义体中 `equal_to` 用实参 `R` 替换形参后的对象。
    pub fn exec_by_family_stmt(
        &mut self,
        stmt: &ByFamilyStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let stmt_exec = stmt.clone().into();
        let family_ty = match &stmt.family_obj {
            Obj::FamilyObj(f) => f,
            _ => {
                return Err(RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        stmt_exec,
                        "by family: expected `family name(...)` object".to_string(),
                        None,
                        vec![],
                    )));
            }
        };

        let family_name = family_ty.name.to_string();
        let def = match self.get_cloned_family_definition_by_name(&family_name) {
            Some(d) => d,
            None => {
                return Err(RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        stmt_exec.clone(),
                        format!("by family: family `{}` is not defined", family_name),
                        None,
                        vec![],
                    )));
            }
        };

        let expected_count = def.params_def_with_type.number_of_params();
        if family_ty.params.len() != expected_count {
            return Err(RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec,
                    format!(
                        "by family: family `{}` expects {} type argument(s), got {}",
                        family_name,
                        expected_count,
                        family_ty.params.len()
                    ),
                    None,
                    vec![],
                )));
        }

        let param_to_arg_map = def
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(family_ty.params.as_slice());

        let right = self
            .inst_obj(&def.equal_to, &param_to_arg_map)
            .map_err(|e| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    "by family: failed to instantiate family body `equal_to`".to_string(),
                    Some(e.into()),
                    vec![],
                ))
            })?;

        let verify_state = VerifyState::new(0, false);
        self.verify_obj_well_defined_and_store_cache(&stmt.family_obj, &verify_state)
            .map_err(|e| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    format!(
                        "by family: left-hand side `{}` is not well-defined",
                        stmt.family_obj
                    ),
                    Some(e.into()),
                    vec![],
                ))
            })?;
        self.verify_obj_well_defined_and_store_cache(&right, &verify_state)
            .map_err(|e| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    format!("by family: instantiated body `{}` is not well-defined", right),
                    Some(e.into()),
                    vec![],
                ))
            })?;

        let equal_fact = EqualFact::new(
            stmt.family_obj.clone(),
            right,
            stmt.line_file.clone(),
        ).into();

        // 与 `by_enumerate` 一致：先把本语句直接生成的事实写进 `infer_facts`，再追加 store+infer 链上的结果。
        let mut infer_result = InferResult::new();
        infer_result.push_atomic_fact(&equal_fact);
        infer_result.new_infer_result_inside(
            self.store_atomic_fact_without_well_defined_verified_and_infer(equal_fact)?,
        );

        Ok((NonFactualStmtSuccess::new(stmt_exec, infer_result, vec![])).into())
    }
}
