use crate::prelude::*;
use std::collections::HashMap;

fn completed_finite_set_induc_case_results(
    proof_steps: &mut Vec<StmtResult>,
    conclusion_checks: &mut Vec<StmtResult>,
) -> Vec<StmtResult> {
    let mut completed = std::mem::take(proof_steps);
    completed.append(conclusion_checks);
    completed
}

impl Runtime {
    // Finite-set structural induction: establish Phi({}) and
    // x not in S, Phi(S) => Phi(union({x}, S)), then conclude forall finite P, Phi(P).
    // An explicit carrier restricts P and the inserted x to that carrier.
    // Example: a finite-set sum proof can expose its empty sum and fresh-singleton step.
    pub fn exec_by_finite_set_induc_stmt(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let proof = self.run_in_local_env(
            |rt| -> Result<SuccessVerifyByFiniteSetInducResult, RuntimeError> {
                let (base_assumptions, step_assumptions) = rt.finite_set_induc_assumptions(stmt)?;
                let base = rt.exec_finite_set_induc_base_proof(stmt, base_assumptions)?;
                let step = rt.exec_finite_set_induc_step_proof(stmt, step_assumptions)?;
                Ok(SuccessVerifyByFiniteSetInducResult { base, step })
            },
        )?;

        let corresponding_forall_fact =
            self.finite_set_induc_stored_forall_fact(stmt)
                .map_err(|runtime_error| {
                    short_exec_error(
                        stmt.clone().into(),
                        "finite-set induc: failed to build concluding forall fact".to_string(),
                        Some(runtime_error),
                        vec![],
                    )
                })?;
        let Fact::ForallFact(generated_forall) = &corresponding_forall_fact else {
            unreachable!("finite-set induction conclusion is constructed as a forall fact")
        };
        let verification = SuccessVerifyByInducResult::new(
            stmt.param_binding.clone(),
            obj_for_bound_param_in_scope(&stmt.param_binding, ParamObjType::Induc),
            stmt.to_prove
                .iter()
                .map(|fact| fact.clone().to_fact())
                .collect(),
            generated_forall.clone(),
            SuccessVerifyByInducProofResult::FiniteSet(Box::new(proof)),
        );
        let result: StmtResult = SuccessByStmtResult::ByFiniteSetInducStmt(Box::new(
            SuccessByFiniteSetInducStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                verification: Some(verification),
            },
        ))
        .into();
        let infer_result = self
            .store_with_well_defined_verification_and_infer_with_default_verify_state(
                corresponding_forall_fact,
            )?;
        Ok(result.with_infers(infer_result))
    }

    pub(crate) fn exec_by_finite_set_induc_stmt_affect_environment_only(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let corresponding_forall_fact =
            self.finite_set_induc_stored_forall_fact(stmt)
                .map_err(|runtime_error| {
                    short_exec_error(
                        stmt.clone().into(),
                        "finite-set induc: failed to build concluding forall fact".to_string(),
                        Some(runtime_error),
                        vec![],
                    )
                })?;
        let infer_result = self.store_trusted_fact_and_infer_with_reason(
            corresponding_forall_fact,
            InferReason::VerifiedStatement,
        )?;
        Ok(
            SuccessByStmtResult::ByFiniteSetInducStmt(Box::new(
                SuccessByFiniteSetInducStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: None,
                },
            ))
            .into(),
        )
    }

    fn exec_finite_set_induc_base_proof(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
        assumptions: Vec<(String, String)>,
    ) -> Result<SuccessVerifyByInducCaseResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.exec_finite_set_induc_base_context(stmt)?;
            let mut proof_steps = rt.exec_finite_set_induc_proof_stmts(
                stmt,
                &stmt.base_proof,
                "finite-set induc base proof",
            )?;
            let mut conclusion_checks = Vec::new();
            let empty_set: Obj = ListSet::new(vec![]).into();
            for fact in stmt.to_prove.iter() {
                let base_fact =
                    rt.finite_set_induc_goal_fact_at_obj(stmt, fact, empty_set.clone())?;
                let result = rt
                    .verify_fact_return_err_if_not_true(
                        &base_fact,
                        &UseContextVerifyState::new(0, false),
                    )
                    .map_err(|verify_error| {
                        short_exec_error(
                            stmt.clone().into(),
                            format!("finite-set induc: base case is not proved `{}`", base_fact),
                            Some(verify_error),
                            completed_finite_set_induc_case_results(
                                &mut proof_steps,
                                &mut conclusion_checks,
                            ),
                        )
                    })?;
                conclusion_checks.push(result);
            }
            Ok(SuccessVerifyByInducCaseResult {
                assumptions,
                proof_steps,
                conclusion_checks,
            })
        })
    }

    fn exec_finite_set_induc_step_proof(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
        assumptions: Vec<(String, String)>,
    ) -> Result<SuccessVerifyByInducCaseResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.exec_finite_set_induc_step_context(stmt)?;
            let mut proof_steps = rt.exec_finite_set_induc_proof_stmts(
                stmt,
                &stmt.step_proof,
                "finite-set induc step proof",
            )?;
            let mut conclusion_checks = Vec::new();
            let extension = rt.finite_set_induc_extension_obj(stmt);
            for fact in stmt.to_prove.iter() {
                let extension_fact =
                    rt.finite_set_induc_goal_fact_at_obj(stmt, fact, extension.clone())?;
                let result = rt
                    .verify_fact_return_err_if_not_true(
                        &extension_fact,
                        &UseContextVerifyState::new(0, false),
                    )
                    .map_err(|verify_error| {
                        short_exec_error(
                            stmt.clone().into(),
                            format!(
                                "finite-set induc: insertion step is not proved `{}`",
                                extension_fact
                            ),
                            Some(verify_error),
                            completed_finite_set_induc_case_results(
                                &mut proof_steps,
                                &mut conclusion_checks,
                            ),
                        )
                    })?;
                conclusion_checks.push(result);
            }
            Ok(SuccessVerifyByInducCaseResult {
                assumptions,
                proof_steps,
                conclusion_checks,
            })
        })
    }

    fn exec_finite_set_induc_base_context(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
    ) -> Result<(), RuntimeError> {
        let params = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
            vec![stmt.param_binding.clone()],
            ParamType::FiniteSet(FiniteSet::new()),
        )]);
        self.define_params_with_type(&params, false, ParamObjType::Induc)
            .map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    "finite-set induc: failed to declare the base finite set".to_string(),
                    Some(error),
                    vec![],
                )
            })?;
        let empty_set: Obj = ListSet::new(vec![]).into();
        let base_eq: Fact = EqualFact::new(
            obj_for_bound_param_in_scope(&stmt.param_binding, ParamObjType::Induc),
            empty_set,
            stmt.line_file.clone(),
        )
        .into();
        self.store_with_well_defined_verification_and_infer_with_default_verify_state(base_eq)
            .map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    "finite-set induc: failed to assume the empty base set".to_string(),
                    Some(error),
                    vec![],
                )
            })?;
        if let Some(carrier_set) = &stmt.carrier_set {
            let base_subset: Fact = SubsetFact::new(
                obj_for_bound_param_in_scope(&stmt.param_binding, ParamObjType::Induc),
                carrier_set.clone(),
                stmt.line_file.clone(),
            )
            .into();
            self.store_with_well_defined_verification_and_infer_with_default_verify_state(
                base_subset,
            )
            .map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    "finite-set induc: failed to assume the base carrier subset".to_string(),
                    Some(error),
                    vec![],
                )
            })?;
        }
        Ok(())
    }

    fn exec_finite_set_induc_step_context(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
    ) -> Result<(), RuntimeError> {
        let element_type = match &stmt.carrier_set {
            Some(carrier_set) => ParamType::Obj(carrier_set.clone()),
            None => ParamType::Set(Set::new()),
        };
        let params = ParamDefWithType::new(vec![
            ParamGroupWithParamType::new(vec![stmt.element_param_binding.clone()], element_type),
            ParamGroupWithParamType::new(
                vec![stmt.smaller_set_param_binding.clone()],
                ParamType::FiniteSet(FiniteSet::new()),
            ),
        ]);
        self.define_params_with_type(&params, false, ParamObjType::Induc)
            .map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    "finite-set induc: failed to declare the insertion parameters".to_string(),
                    Some(error),
                    vec![],
                )
            })?;

        let element =
            obj_for_bound_param_in_scope(&stmt.element_param_binding, ParamObjType::Induc);
        let smaller_set =
            obj_for_bound_param_in_scope(&stmt.smaller_set_param_binding, ParamObjType::Induc);
        let fresh_fact: Fact =
            NotInFact::new(element, smaller_set.clone(), stmt.line_file.clone()).into();
        self.store_with_well_defined_verification_and_infer_with_default_verify_state(fresh_fact)
            .map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    "finite-set induc: failed to assume the fresh insertion element".to_string(),
                    Some(error),
                    vec![],
                )
            })?;

        if let Some(carrier_set) = &stmt.carrier_set {
            let smaller_subset: Fact = SubsetFact::new(
                smaller_set.clone(),
                carrier_set.clone(),
                stmt.line_file.clone(),
            )
            .into();
            self.store_with_well_defined_verification_and_infer_with_default_verify_state(
                smaller_subset,
            )
            .map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    "finite-set induc: failed to assume the smaller carrier subset".to_string(),
                    Some(error),
                    vec![],
                )
            })?;
        }

        for fact in stmt.to_prove.iter() {
            let ih = self.finite_set_induc_goal_fact_at_obj(stmt, fact, smaller_set.clone())?;
            self.store_with_well_defined_verification_and_infer_with_default_verify_state(ih)
                .map_err(|error| {
                    short_exec_error(
                        stmt.clone().into(),
                        "finite-set induc: failed to assume the induction hypothesis".to_string(),
                        Some(error),
                        vec![],
                    )
                })?;
        }
        Ok(())
    }

    fn exec_finite_set_induc_proof_stmts(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
        proof: &[Stmt],
        label: &str,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let mut inside_results = Vec::new();
        for (index, proof_stmt) in proof.iter().enumerate() {
            match self.exec_stmt(proof_stmt) {
                Ok(result) => inside_results.push(result),
                Err(error) => {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "{}: proof step {}/{} failed: `{}`",
                            label,
                            index + 1,
                            proof.len(),
                            proof_stmt
                        ),
                        Some(error),
                        inside_results,
                    ));
                }
            }
        }
        Ok(inside_results)
    }

    fn finite_set_induc_goal_fact_at_obj(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
        fact: &ExistOrAndChainAtomicFact,
        set: Obj,
    ) -> Result<Fact, RuntimeError> {
        let mut param_to_set = HashMap::new();
        insert_symbol_substitution(&mut param_to_set, &stmt.param_binding, set);
        Ok(self
            .inst_exist_or_and_chain_atomic_fact(fact, &param_to_set, ParamObjType::Induc, None)?
            .to_fact())
    }

    fn finite_set_induc_extension_obj(&self, stmt: &ByFiniteSetInducStmt) -> Obj {
        let element =
            obj_for_bound_param_in_scope(&stmt.element_param_binding, ParamObjType::Induc);
        let smaller_set =
            obj_for_bound_param_in_scope(&stmt.smaller_set_param_binding, ParamObjType::Induc);
        Union::new(ListSet::new(vec![element]).into(), smaller_set).into()
    }

    fn finite_set_induc_stored_forall_fact(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
    ) -> Result<Fact, RuntimeError> {
        let (forall_names, param_to_forall) = self.fresh_binder_retag_plan_for_bindings(
            std::slice::from_ref(&stmt.param_binding),
            ParamObjType::Forall,
        );
        let param = param_to_forall[stmt.param()].clone();
        let mut then_facts = Vec::with_capacity(stmt.to_prove.len());
        for fact in stmt.to_prove.iter() {
            then_facts.push(self.inst_exist_or_and_chain_atomic_fact(
                fact,
                &param_to_forall,
                ParamObjType::BinderRetag(BinderRetagSource::Induc),
                None,
            )?);
        }
        let mut dom_facts = Vec::new();
        if let Some(carrier_set) = &stmt.carrier_set {
            dom_facts.push(
                SubsetFact::new(param.clone(), carrier_set.clone(), stmt.line_file.clone()).into(),
            );
        }
        Ok(ForallFact::new_canonical_forall(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![forall_names[0].clone()],
                ParamType::FiniteSet(FiniteSet::new()),
            )]),
            dom_facts,
            then_facts,
            stmt.line_file.clone(),
        )?
        .into())
    }

    fn finite_set_induc_assumptions(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
    ) -> Result<(Vec<(String, String)>, Vec<(String, String)>), RuntimeError> {
        let param = obj_for_bound_param_in_scope(&stmt.param_binding, ParamObjType::Induc);
        let empty_set: Obj = ListSet::new(vec![]).into();
        let mut base_assumptions = vec![
            (
                IsFiniteSetFact::new(param.clone(), stmt.line_file.clone()).to_string(),
                "finite induction parameter".to_string(),
            ),
            (
                EqualFact::new(param.clone(), empty_set, stmt.line_file.clone()).to_string(),
                "empty base case".to_string(),
            ),
        ];
        if let Some(carrier_set) = &stmt.carrier_set {
            base_assumptions.push((
                SubsetFact::new(param.clone(), carrier_set.clone(), stmt.line_file.clone())
                    .to_string(),
                "finite induction carrier".to_string(),
            ));
        }

        let element =
            obj_for_bound_param_in_scope(&stmt.element_param_binding, ParamObjType::Induc);
        let smaller_set =
            obj_for_bound_param_in_scope(&stmt.smaller_set_param_binding, ParamObjType::Induc);
        let mut step_assumptions = vec![
            (
                IsFiniteSetFact::new(smaller_set.clone(), stmt.line_file.clone()).to_string(),
                "smaller finite set".to_string(),
            ),
            (
                NotInFact::new(element.clone(), smaller_set.clone(), stmt.line_file.clone())
                    .to_string(),
                "fresh insertion element".to_string(),
            ),
        ];
        if let Some(carrier_set) = &stmt.carrier_set {
            step_assumptions.insert(
                0,
                (
                    InFact::new(element.clone(), carrier_set.clone(), stmt.line_file.clone())
                        .to_string(),
                    "new element in the induction carrier".to_string(),
                ),
            );
            step_assumptions.insert(
                2,
                (
                    SubsetFact::new(
                        smaller_set.clone(),
                        carrier_set.clone(),
                        stmt.line_file.clone(),
                    )
                    .to_string(),
                    "smaller set in the induction carrier".to_string(),
                ),
            );
        } else {
            step_assumptions.insert(
                0,
                (
                    IsSetFact::new(element.clone(), stmt.line_file.clone()).to_string(),
                    "new element".to_string(),
                ),
            );
        }
        for fact in stmt.to_prove.iter() {
            let ih = self.finite_set_induc_goal_fact_at_obj(stmt, fact, smaller_set.clone())?;
            step_assumptions.push((ih.to_string(), "induction hypothesis".to_string()));
        }

        Ok((base_assumptions, step_assumptions))
    }
}
