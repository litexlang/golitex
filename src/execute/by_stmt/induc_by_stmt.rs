use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn exec_by_induc_stmt(&mut self, stmt: &ByInducStmt) -> Result<StmtResult, RuntimeError> {
        let body_exec_result: Result<StmtResult, RuntimeError> = self.run_in_local_env(|rt| {
            if stmt.strong {
                rt.exec_strong_induc_stmt_assume_proof_context(stmt)?;
            } else {
                rt.exec_by_induc_stmt_assume_proof_context(stmt)?;
            }
            let mut infer_result = InferResult::new();
            let mut inside_results: Vec<StmtResult> = Vec::new();
            for proof_stmt in stmt.proof.iter() {
                inside_results.push(rt.exec_stmt(proof_stmt)?);
            }
            for fact in stmt.to_prove.iter() {
                let one_fact_infer_result = if stmt.strong {
                    rt.exec_strong_induc_stmt_for_one_fact(stmt, fact)?
                } else {
                    rt.exec_by_induc_stmt_for_one_fact(stmt, fact)?
                };
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

        let store_err_msg = if stmt.strong {
            "strong_induc: failed to build concluding forall fact"
        } else {
            "by induc: failed to build concluding forall fact"
        };
        let corresponding_forall_fact = self.by_induc_stmt_stored_forall_fact(stmt).map_err(
            |runtime_error| {
                short_exec_error(
                    stmt.clone().into(),
                    store_err_msg.to_string(),
                    Some(runtime_error),
                    vec![],
                )
            },
        )?;
        let infer_after_store =
            self.verify_well_defined_and_store_and_infer_with_default_verify_state(corresponding_forall_fact)?;

        Ok(non_err_after_body.with_infers(infer_after_store))
    }
}

impl Runtime {
    /// Inner bound variable name for `forall y` in strong induction; avoids clashing with the outer parameter.
    fn strong_induc_inner_param_name(outer: &str) -> String {
        if outer == "y" {
            "y_inner".to_string()
        } else {
            "y".to_string()
        }
    }

    /// Induction hypothesis for strong induc: `forall y, m <= y <= n =>: P(y)` in the case proof environment (`n` is [Induc]).
    fn strong_induc_ih_forall_fact(
        &self,
        stmt: &ByInducStmt,
        fact: &ExistOrAndChainAtomicFact,
    ) -> Result<Fact, RuntimeError> {
        let lf = stmt.line_file.clone();
        let inner = Self::strong_induc_inner_param_name(&stmt.param);
        let y_obj = obj_for_bound_param_in_scope(inner.clone(), ParamObjType::Forall);
        let n_induc = obj_for_bound_param_in_scope(stmt.param.clone(), ParamObjType::Induc);
        // `to_prove` uses the outer param name (e.g. `n` in `$p(n)`); substitute it with the inner `y` object.
        let y_map = HashMap::from([(stmt.param.clone(), y_obj.clone())]);
        let p_y = self.inst_exist_or_and_chain_atomic_fact(fact, &y_map, ParamObjType::Forall, None)?;
        Ok(
            ForallFact::new(
                ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                    vec![inner],
                    ParamType::Obj(StandardSet::Z.into()),
                )]),
                vec![
                    GreaterEqualFact::new(y_obj.clone(), stmt.induc_from.clone(), lf.clone()).into(),
                    LessEqualFact::new(y_obj, n_induc, lf.clone()).into(),
                ],
                vec![p_y],
                lf,
            )
            .into(),
        )
    }

    /// Step obligation for strong induc: `forall n, n >= m, (forall y, m<=y<=n =>: P(y)) =>: P(n+1)`.
    fn strong_induc_step_forall_fact(
        &self,
        stmt: &ByInducStmt,
        fact: &ExistOrAndChainAtomicFact,
    ) -> Result<Fact, RuntimeError> {
        let lf = stmt.line_file.clone();
        let inner = Self::strong_induc_inner_param_name(&stmt.param);
        let n_forall = obj_for_bound_param_in_scope(stmt.param.clone(), ParamObjType::Forall);
        let y_obj = obj_for_bound_param_in_scope(inner.clone(), ParamObjType::Forall);
        // Same as IH: map outer param name in `$p(n)` to the inner `y` binding.
        let y_map = HashMap::from([(stmt.param.clone(), y_obj.clone())]);
        let p_y = self.inst_exist_or_and_chain_atomic_fact(fact, &y_map, ParamObjType::Forall, None)?;
        let inner_forall: Fact = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![inner],
                ParamType::Obj(StandardSet::Z.into()),
            )]),
            vec![
                GreaterEqualFact::new(y_obj.clone(), stmt.induc_from.clone(), lf.clone()).into(),
                LessEqualFact::new(y_obj, n_forall.clone(), lf.clone()).into(),
            ],
            vec![p_y],
            lf.clone(),
        )
        .into();

        let param_plus_one_obj = Add::new(
            n_forall.clone(),
            Number::new("1".to_string()).into(),
        )
        .into();
        let mut n_to_n1: HashMap<String, Obj> = HashMap::new();
        n_to_n1.insert(stmt.param.clone(), param_plus_one_obj);
        let p_n1 = self.inst_exist_or_and_chain_atomic_fact(
            fact,
            &n_to_n1,
            ParamObjType::Forall,
            None,
        )?;

        Ok(ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![stmt.param.clone()],
                ParamType::Obj(StandardSet::Z.into()),
            )]),
            vec![
                GreaterEqualFact::new(n_forall, stmt.induc_from.clone(), lf.clone()).into(),
                inner_forall,
            ],
            vec![p_n1],
            lf,
        )
        .into())
    }

    fn exec_strong_induc_stmt_assume_proof_context(
        &mut self,
        stmt: &ByInducStmt,
    ) -> Result<(), RuntimeError> {
        let params_def = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
            vec![stmt.param.clone()],
            ParamType::Obj(StandardSet::Z.into()),
        )]);
        self.define_params_with_type(&params_def, false, ParamObjType::Induc)
            .map_err(|e| {
                short_exec_error(
                    stmt.clone().into(),
                    "strong_induc: failed to declare induction parameter in proof".to_string(),
                    Some(e),
                    vec![],
                )
            })?;

        let dom_ge: Fact = GreaterEqualFact::new(
            obj_for_bound_param_in_scope(stmt.param.clone(), ParamObjType::Induc),
            stmt.induc_from.clone(),
            stmt.line_file.clone(),
        )
        .into();
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(dom_ge)
            .map_err(|e| {
                short_exec_error(
                    stmt.clone().into(),
                    "strong_induc: failed to assume domain (param >= induction start) in proof"
                        .to_string(),
                    Some(e),
                    vec![],
                )
            })?;

        for fact in stmt.to_prove.iter() {
            let ih = self.strong_induc_ih_forall_fact(stmt, fact)?;
            self.verify_well_defined_and_store_and_infer_with_default_verify_state(ih).map_err(
                |e| {
                    short_exec_error(
                        stmt.clone().into(),
                        "strong_induc: failed to assume strong induction hypothesis in proof"
                            .to_string(),
                        Some(e),
                        vec![],
                    )
                },
            )?;
        }
        Ok(())
    }

    fn exec_strong_induc_stmt_for_one_fact(
        &mut self,
        stmt: &ByInducStmt,
        fact: &ExistOrAndChainAtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();

        let mut base_case_param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        base_case_param_to_arg_map.insert(stmt.param.clone(), stmt.induc_from.clone());
        let base_case_fact = self
            .inst_exist_or_and_chain_atomic_fact(
                fact,
                &base_case_param_to_arg_map,
                ParamObjType::Induc,
                None,
            )?
            .to_fact();
        self.verify_fact_return_err_if_not_true(&base_case_fact, &VerifyState::new(0, false))
            .map_err(|verify_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("strong_induc: base case is not proved `{}`", base_case_fact),
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
                    format!("strong_induc: failed to verify `{}`", induc_from_in_z_fact),
                    Some(verify_error),
                    vec![],
                )
            })?;
        if verify_induc_from_in_z_result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!("strong_induc: failed to verify `{}`", induc_from_in_z_fact),
                None,
                vec![],
            ));
        }

        let corresponding_forall_fact = self.strong_induc_step_forall_fact(stmt, fact)?;

        self.verify_fact_return_err_if_not_true(
            &corresponding_forall_fact,
            &VerifyState::new(0, false),
        )
        .map_err(|well_defined_error| {
            short_exec_error(
                stmt.clone().into(),
                format!(
                    "strong_induc: generated step forall is not well-defined `{}`",
                    corresponding_forall_fact
                ),
                Some(well_defined_error),
                vec![],
            )
        })?;

        infer_result.new_fact(&corresponding_forall_fact);
        Ok(infer_result)
    }

    /// `x $in Z`, `x >= induc_from`, and each `to_prove` instantiated at `x` (induction hypothesis)
    /// for the step — same assumptions the checker uses when verifying the generated step `forall`.
    fn exec_by_induc_stmt_assume_proof_context(
        &mut self,
        stmt: &ByInducStmt,
    ) -> Result<(), RuntimeError> {
        let params_def = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
            vec![stmt.param.clone()],
            ParamType::Obj(StandardSet::Z.into()),
        )]);
        self.define_params_with_type(&params_def, false, ParamObjType::Induc)
            .map_err(|e| {
                short_exec_error(
                    stmt.clone().into(),
                    "by induc: failed to declare induction parameter in proof".to_string(),
                    Some(e),
                    vec![],
                )
            })?;

        let dom_ge: Fact = GreaterEqualFact::new(
            obj_for_bound_param_in_scope(stmt.param.clone(), ParamObjType::Induc),
            stmt.induc_from.clone(),
            stmt.line_file.clone(),
        )
        .into();
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(dom_ge)
            .map_err(|e| {
                short_exec_error(
                    stmt.clone().into(),
                    "by induc: failed to assume domain (param >= induction start) in proof"
                        .to_string(),
                    Some(e),
                    vec![],
                )
            })?;

        let induc_param_obj =
            obj_for_bound_param_in_scope(stmt.param.clone(), ParamObjType::Induc);
        let induc_map: HashMap<String, Obj> =
            HashMap::from([(stmt.param.clone(), induc_param_obj)]);
        for fact in stmt.to_prove.iter() {
            let inst = self
                .inst_exist_or_and_chain_atomic_fact(fact, &induc_map, ParamObjType::Induc, None)?
                .to_fact();
            self.verify_well_defined_and_store_and_infer_with_default_verify_state(inst)
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        "by induc: failed to assume induction hypothesis in proof".to_string(),
                        Some(e),
                        vec![],
                    )
                })?;
        }
        Ok(())
    }

    fn induc_stmt_forall_param_map(param: &str) -> HashMap<String, Obj> {
        let mut m = HashMap::with_capacity(1);
        m.insert(
            param.to_string(),
            obj_for_bound_param_in_scope(param.to_string(), ParamObjType::Forall),
        );
        m
    }

    fn by_induc_stmt_stored_forall_fact(&self, stmt: &ByInducStmt) -> Result<Fact, RuntimeError> {
        let forall_map = Self::induc_stmt_forall_param_map(&stmt.param);
        let mut then_facts: Vec<ExistOrAndChainAtomicFact> =
            Vec::with_capacity(stmt.to_prove.len());
        for fact in stmt.to_prove.iter() {
            then_facts.push(self.inst_exist_or_and_chain_atomic_fact(
                fact,
                &forall_map,
                ParamObjType::Forall,
                None,
            )?);
        }
        Ok(
            ForallFact::new(
                ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                    vec![stmt.param.clone()],
                    ParamType::Obj(StandardSet::Z.into()),
                )]),
                vec![GreaterEqualFact::new(
                    obj_for_bound_param_in_scope(stmt.param.clone(), ParamObjType::Forall),
                    stmt.induc_from.clone(),
                    stmt.line_file.clone(),
                )
                .into()],
                then_facts,
                stmt.line_file.clone(),
            )
            .into(),
        )
    }

    fn exec_by_induc_stmt_for_one_fact(
        &mut self,
        stmt: &ByInducStmt,
        fact: &ExistOrAndChainAtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();

        let mut base_case_param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        base_case_param_to_arg_map.insert(stmt.param.clone(), stmt.induc_from.clone());
        let base_case_fact = self
            .inst_exist_or_and_chain_atomic_fact(
                fact,
                &base_case_param_to_arg_map,
                ParamObjType::Induc,
                None,
            )?
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

        let forall_bound_param =
            obj_for_bound_param_in_scope(stmt.param.clone(), ParamObjType::Forall);
        let forall_map = Self::induc_stmt_forall_param_map(&stmt.param);
        let dom_p_fact = self.inst_exist_or_and_chain_atomic_fact(
            fact,
            &forall_map,
            ParamObjType::Forall,
            None,
        )?;
        let param_plus_one_obj = Add::new(
            forall_bound_param.clone(),
            Number::new("1".to_string()).into(),
        )
        .into();
        let mut induction_step_param_to_obj_map: HashMap<String, Obj> = HashMap::new();
        induction_step_param_to_obj_map.insert(stmt.param.clone(), param_plus_one_obj);
        let next_fact_of_induction_step = self.inst_exist_or_and_chain_atomic_fact(
            fact,
            &induction_step_param_to_obj_map,
            ParamObjType::Forall,
            None,
        )?;

        let corresponding_forall_fact = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![stmt.param.clone()],
                ParamType::Obj(StandardSet::Z.into()),
            )]),
            vec![
                GreaterEqualFact::new(
                    forall_bound_param,
                    stmt.induc_from.clone(),
                    stmt.line_file.clone(),
                )
                .into(),
                dom_p_fact.to_fact(),
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
