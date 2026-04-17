use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn exec_by_induc_stmt(&mut self, stmt: &ByInducStmt) -> Result<StmtResult, RuntimeError> {
        let body_exec_result: Result<StmtResult, RuntimeError> = self.run_in_local_env(|rt| {
            let mut infer_result = InferResult::new();
            let mut inside_results: Vec<StmtResult> = Vec::new();
            for proof_stmt in stmt.proof.iter() {
                inside_results.push(rt.exec_stmt(proof_stmt)?);
            }
            for fact in stmt.to_prove.iter() {
                let one_fact_infer_result = rt.exec_by_induc_stmt_for_one_fact(stmt, fact)?;
                infer_result.new_infer_result_inside(one_fact_infer_result);
            }
            Ok(
                NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, inside_results)
                    .into(),
            )
        });

        let non_err_after_body: StmtResult = match body_exec_result {
            Ok(non_err_stmt_exec_result) => non_err_stmt_exec_result,
            Err(runtime_error) => return Err(runtime_error),
        };

        let corresponding_forall_fact = stmt
            .to_corresponding_forall_fact()
            .map_err(|msg| short_exec_error(stmt.clone().into(), msg, None, vec![]))?;
        let infer_after_store =
            self.store_fact_without_well_defined_verified_and_infer(corresponding_forall_fact)?;

        Ok(non_err_after_body.with_infers(infer_after_store))
    }
}

impl Runtime {
    fn exec_by_induc_stmt_for_one_fact(
        &mut self,
        stmt: &ByInducStmt,
        fact: &ExistOrAndChainAtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();

        let mut base_case_param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        base_case_param_to_arg_map.insert(stmt.param.clone(), stmt.induc_from.clone());
        let base_case_fact = self
            .inst_exist_or_and_chain_atomic_fact(fact, &base_case_param_to_arg_map)?
            .to_fact();
        self.verify_fact_return_err_if_not_true(&base_case_fact, &VerifyState::new(0, false))
            .map_err(|verify_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("by induc: base case is not proved `{}`", base_case_fact),
                    Some(verify_error),
                    vec![],
                )
            })?;

        let induc_from_in_z_fact = InFact::new(
            stmt.induc_from.clone(),
            StandardSet::Z.into(),
            stmt.line_file.clone(),
        )
        .into();
        let verify_induc_from_in_z_result = self
            .verify_atomic_fact(&induc_from_in_z_fact, &VerifyState::new(0, false))
            .map_err(|verify_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("by induc: failed to verify `{}`", induc_from_in_z_fact),
                    Some(verify_error),
                    vec![],
                )
            })?;
        if verify_induc_from_in_z_result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!("by induc: failed to verify `{}`", induc_from_in_z_fact),
                None,
                vec![],
            ));
        }

        let param_as_identifier: Obj = stmt.param.clone().into();
        let param_plus_one_obj = Add::new(
            param_as_identifier.clone(),
            Number::new("1".to_string()).into(),
        )
        .into();
        let mut induction_step_param_to_obj_map: HashMap<String, Obj> = HashMap::new();
        induction_step_param_to_obj_map.insert(stmt.param.clone(), param_plus_one_obj);
        let next_fact_of_induction_step =
            self.inst_exist_or_and_chain_atomic_fact(fact, &induction_step_param_to_obj_map)?;

        let corresponding_forall_fact = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![stmt.param.clone()],
                ParamType::Obj(StandardSet::Z.into()),
            )]),
            vec![
                GreaterEqualFact::new(
                    param_as_identifier,
                    stmt.induc_from.clone(),
                    stmt.line_file.clone(),
                )
                .into(),
                fact.clone().to_fact(),
            ],
            vec![next_fact_of_induction_step],
            stmt.line_file.clone(),
        )
        .into();

        self.verify_fact_return_err_if_not_true(
            &corresponding_forall_fact,
            &VerifyState::new(0, false),
        )
        .map_err(|well_defined_error| {
            short_exec_error(
                stmt.clone().into(),
                format!(
                    "by induc: generated step forall is not well-defined `{}`",
                    corresponding_forall_fact
                ),
                Some(well_defined_error),
                vec![],
            )
        })?;

        infer_result.new_fact(&corresponding_forall_fact);
        Ok(infer_result)
    }
}
