use crate::prelude::*;

impl Runtime {
    pub fn exec_have_exist_obj_stmt(
        &mut self,
        have_exist_obj_stmt: &HaveByExistStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let exist_fact_in_have_obj_stmt = &have_exist_obj_stmt.exist_fact_in_have_obj_st;
        let verify_state = VerifyState::new(0, false);

        let result = self
            .verify_exist_fact(exist_fact_in_have_obj_stmt, &verify_state)
            .map_err(|verify_error| {
                short_exec_error(
                    have_exist_obj_stmt.clone().into(),
                    "",
                    Some(verify_error),
                    vec![],
                )
            })?;
        if result.is_unknown() {
            return Err(short_exec_error(
                have_exist_obj_stmt.clone().into(),
                "have_exist_obj_stmt: exist fact is not verified".to_string(),
                None,
                vec![],
            ));
        }

        if exist_fact_in_have_obj_stmt
            .params_def_with_type
            .number_of_params()
            != have_exist_obj_stmt.equal_tos.len()
        {
            return Err(short_exec_error(
 have_exist_obj_stmt.clone().into(),
                    "have_exist_obj_stmt: number of params in exist does not match number of given objs".to_string(),
                    None,
                    vec![],
                ));
        }

        for obj in have_exist_obj_stmt.equal_tos.iter() {
            self.store_free_param_or_identifier_name(obj, ParamObjType::Exist)?;
        }

        let new_obj_names_as_identifier_objs = have_exist_obj_stmt
            .equal_tos
            .iter()
            .map(|s| Identifier::new(s.clone()).into())
            .collect();

        let mut infer_result = self
            .store_args_satisfy_param_type_when_not_defining_new_identifiers(
                &exist_fact_in_have_obj_stmt.params_def_with_type,
                &new_obj_names_as_identifier_objs,
                have_exist_obj_stmt.line_file.clone(),
                ParamObjType::Exist,
            )
            .map_err(|e| {
                short_exec_error(have_exist_obj_stmt.clone().into(), "", Some(e), vec![])
            })?;

        let param_to_obj_map = exist_fact_in_have_obj_stmt
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(new_obj_names_as_identifier_objs.as_slice());

        for fact in exist_fact_in_have_obj_stmt.facts.iter() {
            let instantiated_fact = self
                .inst_or_and_chain_atomic_fact(fact, &param_to_obj_map, ParamObjType::Exist)
                .map_err(|runtime_error| {
                    short_exec_error(
                        have_exist_obj_stmt.clone().into(),
                        "",
                        Some(runtime_error),
                        vec![],
                    )
                })?
                .to_fact();
            let fact_infer_result = self
                .verify_well_defined_and_store_and_infer_with_default_verify_state(instantiated_fact)
                .map_err(|store_fact_error| {
                    short_exec_error(
                        have_exist_obj_stmt.clone().into(),
                        "",
                        Some(store_fact_error),
                        vec![],
                    )
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }

        Ok(
            (NonFactualStmtSuccess::new(have_exist_obj_stmt.clone().into(), infer_result, vec![]))
                .into(),
        )
    }
}
