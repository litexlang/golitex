use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    // TODO: THIS IS A MESS
    pub fn exec_have_obj_equal_stmt(
        &mut self,
        have_obj_equal_stmt: &HaveObjEqualStmt,
    ) -> Result<StmtResult, RuntimeErrorStruct> {
        if have_obj_equal_stmt.param_def.number_of_params()
            != have_obj_equal_stmt.objs_equal_to.len()
        {
            return Err(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                have_obj_equal_stmt.clone().into(),
                "have_obj_equal_stmt: number of params in param_def does not match number of objs_equal_to".to_string(),
                None,
                vec![],
            ));
        }

        let mut current_index = 0;
        let mut param_to_obj_map: HashMap<String, Obj> = HashMap::new();
        for param_def in have_obj_equal_stmt.param_def.groups.iter() {
            let current_type_holder = self
                .inst_param_type(&param_def.param_type, &param_to_obj_map)
                .map_err(|runtime_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        have_obj_equal_stmt.clone().into(),
                        "".to_string(),
                        Some(runtime_error),
                        vec![],
                    )
                })?;
            let current_type = &current_type_holder;
            for name in param_def.params.iter() {
                let current_param_equal_to = &have_obj_equal_stmt.objs_equal_to[current_index];

                let verify_result = self
                    .verify_obj_satisfies_param_type(
                        current_param_equal_to.clone(),
                        current_type,
                        &VerifyState::new(0, false),
                    )
                    .map_err(|verify_error| {
                        RuntimeErrorStruct::exec_stmt_new_with_stmt(
                            have_obj_equal_stmt.clone().into(),
                            "".to_string(),
                            Some(verify_error),
                            vec![],
                        )
                    })?;
                if verify_result.is_unknown() {
                    let msg = format!(
                        "have_obj_equal_stmt: {} is not in type {}",
                        current_param_equal_to, current_type
                    );
                    return Err(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        have_obj_equal_stmt.clone().into(),
                        msg,
                        None,
                        vec![],
                    ));
                }

                param_to_obj_map.insert(name.clone(), current_param_equal_to.clone());
                current_index += 1;
            }
        }

        let mut infer_result = InferResult::new();

        let param_infer_result = self
            .define_params_with_type(&have_obj_equal_stmt.param_def, true)
            .map_err(|define_params_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_obj_equal_stmt.clone().into(),
                    "".to_string(),
                    Some(define_params_error),
                    vec![],
                )
            })?;
        infer_result.new_infer_result_inside(param_infer_result);

        for (name, obj) in have_obj_equal_stmt
            .param_def
            .collect_param_names()
            .iter()
            .zip(have_obj_equal_stmt.objs_equal_to.iter())
        {
            let equal_to_fact = EqualFact::new(
                name.clone().into(),
                obj.clone(),
                have_obj_equal_stmt.line_file.clone(),
            )
            .into();
            let equal_to_fact_infer_result = self
                .store_atomic_fact_without_well_defined_verified_and_infer(equal_to_fact)
                .map_err(|store_fact_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        have_obj_equal_stmt.clone().into(),
                        "".to_string(),
                        Some(RuntimeError::ExecStmtError(store_fact_error)),
                        vec![],
                    )
                })?;
            infer_result.new_infer_result_inside(equal_to_fact_infer_result);
        }

        Ok((NonFactualStmtSuccess::new(
            have_obj_equal_stmt.clone().into(),
            infer_result,
            vec![],
        ))
        .into())
    }
}
