use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    // Finite-set structural induction: establish Phi({}) and
    // x not in S, Phi(S) => Phi(union({x}, S)), then conclude forall finite P, Phi(P).
    // An explicit carrier restricts P and the inserted x to that carrier.
    // Example: a finite-set sum proof can expose its empty sum and fresh-singleton step.
    pub fn exec_by_finite_set_induc_stmt(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let mut result: StmtResult =
            self.run_in_local_env(|rt| -> Result<StmtResult, RuntimeError> {
                let mut inside_results = Vec::new();
                inside_results.extend(rt.exec_finite_set_induc_base_proof(stmt)?);
                inside_results.extend(rt.exec_finite_set_induc_step_proof(stmt)?);
                Ok(NonFactualStmtSuccess::new(
                    stmt.clone().into(),
                    InferResult::new(),
                    inside_results,
                )
                .into())
            })?;

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
        let verification =
            self.finite_set_induc_verification_result(stmt, &corresponding_forall_fact)?;
        if let Some(success) = result.non_factual_success_mut() {
            success.by_verification = Some(verification.into());
        }
        let infer_result = self.verify_well_defined_and_store_and_infer_with_default_verify_state(
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
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }

    fn exec_finite_set_induc_base_proof(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.exec_finite_set_induc_base_context(stmt)?;
            let mut inside_results = rt.exec_finite_set_induc_proof_stmts(
                stmt,
                &stmt.base_proof,
                "finite-set induc base proof",
            )?;
            let empty_set: Obj = ListSet::new(vec![]).into();
            for fact in stmt.to_prove.iter() {
                let base_fact =
                    rt.finite_set_induc_goal_fact_at_obj(stmt, fact, empty_set.clone())?;
                let result = rt
                    .verify_fact_return_err_if_not_true(&base_fact, &VerifyState::new(0, false))
                    .map_err(|verify_error| {
                        short_exec_error(
                            stmt.clone().into(),
                            format!("finite-set induc: base case is not proved `{}`", base_fact),
                            Some(verify_error),
                            std::mem::take(&mut inside_results),
                        )
                    })?;
                inside_results.push(result);
            }
            Ok(inside_results)
        })
    }

    fn exec_finite_set_induc_step_proof(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.exec_finite_set_induc_step_context(stmt)?;
            let mut inside_results = rt.exec_finite_set_induc_proof_stmts(
                stmt,
                &stmt.step_proof,
                "finite-set induc step proof",
            )?;
            let extension = rt.finite_set_induc_extension_obj(stmt);
            for fact in stmt.to_prove.iter() {
                let extension_fact =
                    rt.finite_set_induc_goal_fact_at_obj(stmt, fact, extension.clone())?;
                let result = rt
                    .verify_fact_return_err_if_not_true(
                        &extension_fact,
                        &VerifyState::new(0, false),
                    )
                    .map_err(|verify_error| {
                        short_exec_error(
                            stmt.clone().into(),
                            format!(
                                "finite-set induc: insertion step is not proved `{}`",
                                extension_fact
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

    fn exec_finite_set_induc_base_context(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
    ) -> Result<(), RuntimeError> {
        let params = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
            vec![stmt.param.clone()],
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
            obj_for_bound_param_in_scope(stmt.param.clone(), ParamObjType::Induc),
            empty_set,
            stmt.line_file.clone(),
        )
        .into();
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(base_eq)
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
                obj_for_bound_param_in_scope(stmt.param.clone(), ParamObjType::Induc),
                carrier_set.clone(),
                stmt.line_file.clone(),
            )
            .into();
            self.verify_well_defined_and_store_and_infer_with_default_verify_state(base_subset)
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
            ParamGroupWithParamType::new(vec![stmt.element_param.clone()], element_type),
            ParamGroupWithParamType::new(
                vec![stmt.smaller_set_param.clone()],
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

        let element = obj_for_bound_param_in_scope(stmt.element_param.clone(), ParamObjType::Induc);
        let smaller_set =
            obj_for_bound_param_in_scope(stmt.smaller_set_param.clone(), ParamObjType::Induc);
        let fresh_fact: Fact =
            NotInFact::new(element, smaller_set.clone(), stmt.line_file.clone()).into();
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(fresh_fact)
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
            self.verify_well_defined_and_store_and_infer_with_default_verify_state(smaller_subset)
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
            self.verify_well_defined_and_store_and_infer_with_default_verify_state(ih)
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
        let param_to_set = HashMap::from([(stmt.param.clone(), set)]);
        Ok(self
            .inst_exist_or_and_chain_atomic_fact(fact, &param_to_set, ParamObjType::Induc, None)?
            .to_fact())
    }

    fn finite_set_induc_extension_obj(&self, stmt: &ByFiniteSetInducStmt) -> Obj {
        let element = obj_for_bound_param_in_scope(stmt.element_param.clone(), ParamObjType::Induc);
        let smaller_set =
            obj_for_bound_param_in_scope(stmt.smaller_set_param.clone(), ParamObjType::Induc);
        Union::new(ListSet::new(vec![element]).into(), smaller_set).into()
    }

    fn finite_set_induc_stored_forall_fact(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
    ) -> Result<Fact, RuntimeError> {
        let param = obj_for_bound_param_in_scope(stmt.param.clone(), ParamObjType::Forall);
        let param_to_forall = HashMap::from([(stmt.param.clone(), param.clone())]);
        let mut then_facts = Vec::with_capacity(stmt.to_prove.len());
        for fact in stmt.to_prove.iter() {
            then_facts.push(self.inst_exist_or_and_chain_atomic_fact(
                fact,
                &param_to_forall,
                ParamObjType::Forall,
                None,
            )?);
        }
        let mut dom_facts = Vec::new();
        if let Some(carrier_set) = &stmt.carrier_set {
            dom_facts.push(
                SubsetFact::new(param.clone(), carrier_set.clone(), stmt.line_file.clone()).into(),
            );
        }
        Ok(ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![stmt.param.clone()],
                ParamType::FiniteSet(FiniteSet::new()),
            )]),
            dom_facts,
            then_facts,
            stmt.line_file.clone(),
        )?
        .into())
    }

    fn finite_set_induc_verification_result(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
        generated_forall: &Fact,
    ) -> Result<ByInducVerificationResult, RuntimeError> {
        let param = obj_for_bound_param_in_scope(stmt.param.clone(), ParamObjType::Induc);
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

        let element = obj_for_bound_param_in_scope(stmt.element_param.clone(), ParamObjType::Induc);
        let smaller_set =
            obj_for_bound_param_in_scope(stmt.smaller_set_param.clone(), ParamObjType::Induc);
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

        Ok(ByInducVerificationResult::new(
            false,
            true,
            true,
            stmt.param.clone(),
            "{}".to_string(),
            stmt.to_prove.iter().map(|fact| fact.to_string()).collect(),
            generated_forall.to_string(),
            0,
            base_assumptions,
            stmt.base_proof.len(),
            stmt.base_proof.len() + stmt.to_prove.len(),
            step_assumptions,
            stmt.step_proof.len(),
            stmt.step_proof.len() + stmt.to_prove.len(),
        ))
    }
}
