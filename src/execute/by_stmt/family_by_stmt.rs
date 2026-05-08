use crate::prelude::*;

impl Runtime {
    // `by family as set: \p(R)` stores the instantiated `\p(R) =` body.
    pub fn exec_by_family_stmt(
        &mut self,
        stmt: &ByFamilyAsSetStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let stmt_exec: Stmt = stmt.clone().into();
        let family_ty = match &stmt.family_obj {
            Obj::FamilyObj(f) => f,
            _ => {
                return Err(short_exec_error(
                    stmt_exec,
                    "by family as set: expected `\\name(...)` family object".to_string(),
                    None,
                    vec![],
                ));
            }
        };

        let family_name = family_ty.name.to_string();
        let def = match self.get_cloned_family_definition_by_name(&family_name) {
            Some(d) => d,
            None => {
                return Err(short_exec_error(
                    stmt_exec.clone(),
                    format!("by family as set: family `{}` is not defined", family_name),
                    None,
                    vec![],
                ));
            }
        };

        let expected_count = def.params_def_with_type.number_of_params();
        if family_ty.params.len() != expected_count {
            return Err(short_exec_error(
                stmt_exec,
                format!(
                    "by family as set: family `{}` expects {} type argument(s), got {}",
                    family_name,
                    expected_count,
                    family_ty.params.len()
                ),
                None,
                vec![],
            ));
        }

        let param_to_arg_map = def
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(family_ty.params.as_slice());

        let right = self
            .inst_obj(&def.equal_to, &param_to_arg_map, ParamObjType::DefHeader)
            .map_err(|e| {
                short_exec_error(
                    stmt_exec.clone(),
                    "by family as set: failed to instantiate family body `equal_to`".to_string(),
                    Some(e),
                    vec![],
                )
            })?;

        let verify_state = VerifyState::new(0, false);
        self.verify_obj_well_defined_and_store_cache(&stmt.family_obj, &verify_state)
            .map_err(|e| {
                short_exec_error(
                    stmt_exec.clone(),
                    format!(
                        "by family as set: left-hand side `{}` is not well-defined",
                        stmt.family_obj
                    ),
                    Some(e),
                    vec![],
                )
            })?;
        self.verify_obj_well_defined_and_store_cache(&right, &verify_state)
            .map_err(|e| {
                short_exec_error(
                    stmt_exec.clone(),
                    format!(
                        "by family as set: instantiated body `{}` is not well-defined",
                        right
                    ),
                    Some(e),
                    vec![],
                )
            })?;

        let equal_fact =
            EqualFact::new(stmt.family_obj.clone(), right, stmt.line_file.clone()).into();

        // Keep the directly generated fact before appending store+infer results.
        let mut infer_result = InferResult::new();
        infer_result.push_atomic_fact(&equal_fact);
        infer_result.new_infer_result_inside(
            self.store_atomic_fact_without_well_defined_verified_and_infer(equal_fact)?,
        );

        Ok((NonFactualStmtSuccess::new(stmt_exec, infer_result, vec![])).into())
    }
}
