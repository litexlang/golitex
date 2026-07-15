use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn exec_by_induc_stmt(&mut self, stmt: &ByInducStmt) -> Result<StmtResult, RuntimeError> {
        let body_exec_result: Result<StmtResult, RuntimeError> = if stmt.has_structured_proof() {
            self.exec_structured_induc_stmt_body(stmt)
        } else {
            self.run_in_local_env(|rt| {
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
            })
        };

        let mut non_err_after_body: StmtResult = match body_exec_result {
            Ok(non_err_stmt_exec_result) => non_err_stmt_exec_result,
            Err(runtime_error) => return Err(runtime_error),
        };

        let store_err_msg = if stmt.strong {
            "strong_induc: failed to build concluding forall fact"
        } else {
            "by induc: failed to build concluding forall fact"
        };
        let corresponding_forall_fact =
            self.by_induc_stmt_stored_forall_fact(stmt)
                .map_err(|runtime_error| {
                    short_exec_error(
                        stmt.clone().into(),
                        store_err_msg.to_string(),
                        Some(runtime_error),
                        vec![],
                    )
                })?;
        let by_verification =
            self.by_induc_verification_result(stmt, &corresponding_forall_fact)?;
        if let Some(success) = non_err_after_body.non_factual_success_mut() {
            success.by_verification = Some(by_verification.into());
        }
        let infer_after_store = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state(
                corresponding_forall_fact,
            )?;

        Ok(non_err_after_body.with_infers(infer_after_store))
    }

    pub(crate) fn exec_by_induc_stmt_affect_environment_only(
        &mut self,
        stmt: &ByInducStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let corresponding_forall_fact =
            self.by_induc_stmt_stored_forall_fact(stmt)
                .map_err(|runtime_error| {
                    short_exec_error(
                        stmt.clone().into(),
                        "by induc: failed to build concluding forall fact".to_string(),
                        Some(runtime_error),
                        vec![],
                    )
                })?;
        let infer_result = self.store_trusted_fact_and_infer_with_reason(
            corresponding_forall_fact,
            InferReason::VerifiedStatement,
        )?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
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
        let p_y =
            self.inst_exist_or_and_chain_atomic_fact(fact, &y_map, ParamObjType::Forall, None)?;
        Ok(ForallFact::new(
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
        )?
        .into())
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
        let p_y =
            self.inst_exist_or_and_chain_atomic_fact(fact, &y_map, ParamObjType::Forall, None)?;
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
        )?
        .into();

        let param_plus_one_obj =
            Add::new(n_forall.clone(), Number::new("1".to_string()).into()).into();
        let mut n_to_n1: HashMap<String, Obj> = HashMap::new();
        n_to_n1.insert(stmt.param.clone(), param_plus_one_obj);
        let p_n1 =
            self.inst_exist_or_and_chain_atomic_fact(fact, &n_to_n1, ParamObjType::Forall, None)?;

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
        )?
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
            self.verify_well_defined_and_store_and_infer_with_default_verify_state(ih)
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        "strong_induc: failed to assume strong induction hypothesis in proof"
                            .to_string(),
                        Some(e),
                        vec![],
                    )
                })?;
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

        let induc_param_obj = obj_for_bound_param_in_scope(stmt.param.clone(), ParamObjType::Induc);
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
        Ok(ForallFact::new(
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
        )?
        .into())
    }

    fn by_induc_verification_result(
        &self,
        stmt: &ByInducStmt,
        generated_forall: &Fact,
    ) -> Result<ByInducVerificationResult, RuntimeError> {
        let param_obj = obj_for_bound_param_in_scope(stmt.param.clone(), ParamObjType::Induc);
        let base_assumptions = vec![
            (
                InFact::new(
                    param_obj.clone(),
                    StandardSet::Z.into(),
                    stmt.line_file.clone(),
                )
                .to_string(),
                "induction parameter".to_string(),
            ),
            (
                EqualFact::new(
                    param_obj.clone(),
                    stmt.induc_from.clone(),
                    stmt.line_file.clone(),
                )
                .to_string(),
                "base case".to_string(),
            ),
        ];

        let mut step_assumptions = vec![
            (
                InFact::new(
                    param_obj.clone(),
                    StandardSet::Z.into(),
                    stmt.line_file.clone(),
                )
                .to_string(),
                "induction parameter".to_string(),
            ),
            (
                GreaterEqualFact::new(
                    param_obj.clone(),
                    stmt.induc_from.clone(),
                    stmt.line_file.clone(),
                )
                .to_string(),
                "induction domain".to_string(),
            ),
        ];
        let induc_map: HashMap<String, Obj> = HashMap::from([(stmt.param.clone(), param_obj)]);
        for fact in stmt.to_prove.iter() {
            let assumption_fact = if stmt.strong {
                self.strong_induc_ih_forall_fact(stmt, fact)?
            } else {
                self.inst_exist_or_and_chain_atomic_fact(
                    fact,
                    &induc_map,
                    ParamObjType::Induc,
                    None,
                )?
                .to_fact()
            };
            let reason = if stmt.strong {
                "strong induction hypothesis"
            } else {
                "induction hypothesis"
            };
            step_assumptions.push((assumption_fact.to_string(), reason.to_string()));
        }

        let structured = stmt.has_structured_proof();
        let base_proof_step_count = stmt
            .base_proof
            .as_ref()
            .map(|proof| proof.len())
            .unwrap_or(0);
        let step_proof_step_count = stmt
            .step_proof
            .as_ref()
            .map(|proof| proof.len())
            .unwrap_or(0);
        let base_result_count = if structured {
            base_proof_step_count + stmt.to_prove.len()
        } else {
            0
        };
        let step_result_count = if structured {
            step_proof_step_count + stmt.to_prove.len()
        } else {
            0
        };

        Ok(ByInducVerificationResult::new(
            stmt.strong,
            false,
            structured,
            stmt.param.clone(),
            stmt.induc_from.to_string(),
            stmt.to_prove.iter().map(|fact| fact.to_string()).collect(),
            generated_forall.to_string(),
            stmt.proof.len(),
            base_assumptions,
            base_proof_step_count,
            base_result_count,
            step_assumptions,
            step_proof_step_count,
            step_result_count,
        ))
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
        )?
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

    fn exec_structured_induc_stmt_body(
        &mut self,
        stmt: &ByInducStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.verify_induc_from_in_z(stmt)?;

            let mut inside_results: Vec<StmtResult> = Vec::new();
            inside_results.extend(rt.exec_structured_induc_base_proof(stmt)?);
            inside_results.extend(rt.exec_structured_induc_step_proof(stmt)?);

            Ok(
                NonFactualStmtSuccess::new(stmt.clone().into(), InferResult::new(), inside_results)
                    .into(),
            )
        })
    }

    fn exec_structured_induc_base_proof(
        &mut self,
        stmt: &ByInducStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let base_proof = stmt
            .base_proof
            .as_ref()
            .expect("structured induction proof must have a base proof");
        self.run_in_local_env(|rt| {
            rt.exec_structured_induc_base_context(stmt)?;
            let mut inside_results =
                rt.exec_structured_induc_proof_stmts(stmt, base_proof, "induc base proof")?;

            for fact in stmt.to_prove.iter() {
                let base_fact = rt.induc_goal_fact_at_obj(stmt, fact, stmt.induc_from.clone())?;
                let result = rt
                    .verify_fact_return_err_if_not_true(&base_fact, &VerifyState::new(0, false))
                    .map_err(|verify_error| {
                        short_exec_error(
                            stmt.clone().into(),
                            format!(
                                "{}: base case is not proved `{}`",
                                Self::induc_stmt_error_prefix(stmt),
                                base_fact
                            ),
                            Some(verify_error),
                            std::mem::take(&mut inside_results),
                        )
                    })?;
                inside_results.push(result);
            }

            Ok(inside_results)
        })
    }

    fn exec_structured_induc_step_proof(
        &mut self,
        stmt: &ByInducStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let step_proof = stmt
            .step_proof
            .as_ref()
            .expect("structured induction proof must have a step proof");
        self.run_in_local_env(|rt| {
            if stmt.strong {
                rt.exec_strong_induc_stmt_assume_proof_context(stmt)?;
            } else {
                rt.exec_by_induc_stmt_assume_proof_context(stmt)?;
            }

            let mut inside_results =
                rt.exec_structured_induc_proof_stmts(stmt, step_proof, "induc step proof")?;
            let next_obj = rt.induc_step_next_obj(stmt);

            for fact in stmt.to_prove.iter() {
                let next_fact = rt.induc_goal_fact_at_obj(stmt, fact, next_obj.clone())?;
                let result = rt
                    .verify_fact_return_err_if_not_true(&next_fact, &VerifyState::new(0, false))
                    .map_err(|verify_error| {
                        short_exec_error(
                            stmt.clone().into(),
                            format!(
                                "{}: induction step is not proved `{}`",
                                Self::induc_stmt_error_prefix(stmt),
                                next_fact
                            ),
                            Some(verify_error),
                            std::mem::take(&mut inside_results),
                        )
                    })?;
                inside_results.push(result);
            }

            Ok(inside_results)
        })
    }

    fn exec_structured_induc_base_context(
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
                    format!(
                        "{}: failed to declare induction parameter in base proof",
                        Self::induc_stmt_error_prefix(stmt)
                    ),
                    Some(e),
                    vec![],
                )
            })?;

        let param_obj = obj_for_bound_param_in_scope(stmt.param.clone(), ParamObjType::Induc);
        let base_eq: Fact =
            EqualFact::new(param_obj, stmt.induc_from.clone(), stmt.line_file.clone()).into();
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(base_eq)
            .map_err(|e| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "{}: failed to assume base equality",
                        Self::induc_stmt_error_prefix(stmt)
                    ),
                    Some(e),
                    vec![],
                )
            })?;

        Ok(())
    }

    fn exec_structured_induc_proof_stmts(
        &mut self,
        stmt: &ByInducStmt,
        proof: &[Stmt],
        label: &str,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let mut inside_results: Vec<StmtResult> = Vec::new();
        let proof_len = proof.len();
        for (proof_index, proof_stmt) in proof.iter().enumerate() {
            let exec_result = self.exec_stmt(proof_stmt);
            match exec_result {
                Ok(result) => inside_results.push(result),
                Err(statement_error) => {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "{}: proof step {}/{} failed: `{}`",
                            label,
                            proof_index + 1,
                            proof_len,
                            proof_stmt
                        ),
                        Some(statement_error),
                        inside_results,
                    ));
                }
            }
        }
        Ok(inside_results)
    }

    fn verify_induc_from_in_z(&mut self, stmt: &ByInducStmt) -> Result<(), RuntimeError> {
        let induc_from_in_z_fact = InFact::new(
            stmt.induc_from.clone(),
            StandardSet::Z.into(),
            stmt.line_file.clone(),
        )
        .into();
        let verify_result = self
            .verify_atomic_fact(&induc_from_in_z_fact, &VerifyState::new(0, false))
            .map_err(|verify_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "{}: failed to verify `{}`",
                        Self::induc_stmt_error_prefix(stmt),
                        induc_from_in_z_fact
                    ),
                    Some(verify_error),
                    vec![],
                )
            })?;
        if verify_result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "{}: failed to verify `{}`",
                    Self::induc_stmt_error_prefix(stmt),
                    induc_from_in_z_fact
                ),
                None,
                vec![],
            ));
        }
        Ok(())
    }

    fn induc_goal_fact_at_obj(
        &mut self,
        stmt: &ByInducStmt,
        fact: &ExistOrAndChainAtomicFact,
        obj: Obj,
    ) -> Result<Fact, RuntimeError> {
        let param_to_obj_map: HashMap<String, Obj> = HashMap::from([(stmt.param.clone(), obj)]);
        Ok(self
            .inst_exist_or_and_chain_atomic_fact(
                fact,
                &param_to_obj_map,
                ParamObjType::Induc,
                None,
            )?
            .to_fact())
    }

    fn induc_step_next_obj(&self, stmt: &ByInducStmt) -> Obj {
        Add::new(
            obj_for_bound_param_in_scope(stmt.param.clone(), ParamObjType::Induc),
            Number::new("1".to_string()).into(),
        )
        .into()
    }

    fn induc_stmt_error_prefix(stmt: &ByInducStmt) -> &'static str {
        if stmt.strong {
            "strong_induc"
        } else {
            "by induc"
        }
    }
}
