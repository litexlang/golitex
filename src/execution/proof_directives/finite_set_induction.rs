use crate::prelude::*;
use std::collections::HashMap;

fn completed_finite_set_induc_case_results(
    proof_steps: &mut Vec<StmtResult>,
    conclusions: &mut Vec<SuccessVerifyByInducConclusionResult>,
) -> Vec<StmtResult> {
    let mut completed = std::mem::take(proof_steps);
    completed.extend(
        std::mem::take(conclusions)
            .into_iter()
            .map(|conclusion| *conclusion.check),
    );
    completed
}

struct SuccessExecFiniteSetInducCaseContextResult {
    assumptions: Vec<SuccessVerifyByInducAssumptionResult>,
    infers: SuccessInferResult,
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
                let base = rt.exec_finite_set_induc_base_proof(stmt)?;
                let step = rt.exec_finite_set_induc_step_proof(stmt)?;
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
            obj_for_bound_param_in_scope(&stmt.param_binding),
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

    pub fn exec_by_finite_set_induc_stmt_affect_environment_only(
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
        let infer_result = self.store_fact_with_trust_and_infer_with_reason(
            corresponding_forall_fact,
            InferReason::StatementWithVerification,
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
    ) -> Result<SuccessVerifyByInducCaseResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            let context = rt.exec_finite_set_induc_base_context(stmt)?;
            let mut proof_steps = rt.exec_finite_set_induc_proof_stmts(
                stmt,
                &stmt.base_proof,
                "finite-set induc base proof",
            )?;
            let mut conclusions = Vec::new();
            let empty_set: Obj = ListSet::new(vec![]).into();
            for fact in stmt.to_prove.iter() {
                let base_fact =
                    rt.finite_set_induc_goal_fact_at_obj(stmt, fact, empty_set.clone())?;
                let mut result = rt
                    .verify_fact_or_error(&base_fact, &VerifyState::initial())
                    .map_err(|verify_error| {
                        short_exec_error(
                            stmt.clone().into(),
                            format!("finite-set induc: base case is not proved `{}`", base_fact),
                            Some(verify_error),
                            completed_finite_set_induc_case_results(
                                &mut proof_steps,
                                &mut conclusions,
                            ),
                        )
                    })?;
                rt.attach_known_fact_ids_to_stmt_result(&mut result)?;
                conclusions.push(SuccessVerifyByInducConclusionResult {
                    goal: base_fact,
                    check: Box::new(result),
                });
            }
            for proof_step in proof_steps.iter_mut() {
                rt.attach_known_fact_ids_to_stmt_result(proof_step)?;
            }
            Ok(SuccessVerifyByInducCaseResult {
                assumptions: context.assumptions,
                assumption_infers: context.infers,
                proof_steps,
                conclusions,
            })
        })
    }

    fn exec_finite_set_induc_step_proof(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
    ) -> Result<SuccessVerifyByInducCaseResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            let context = rt.exec_finite_set_induc_step_context(stmt)?;
            let mut proof_steps = rt.exec_finite_set_induc_proof_stmts(
                stmt,
                &stmt.step_proof,
                "finite-set induc step proof",
            )?;
            let mut conclusions = Vec::new();
            let extension = rt.finite_set_induc_extension_obj(stmt);
            for fact in stmt.to_prove.iter() {
                let extension_fact =
                    rt.finite_set_induc_goal_fact_at_obj(stmt, fact, extension.clone())?;
                let mut result = rt
                    .verify_fact_or_error(&extension_fact, &VerifyState::initial())
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
                                &mut conclusions,
                            ),
                        )
                    })?;
                rt.attach_known_fact_ids_to_stmt_result(&mut result)?;
                conclusions.push(SuccessVerifyByInducConclusionResult {
                    goal: extension_fact,
                    check: Box::new(result),
                });
            }
            for proof_step in proof_steps.iter_mut() {
                rt.attach_known_fact_ids_to_stmt_result(proof_step)?;
            }
            Ok(SuccessVerifyByInducCaseResult {
                assumptions: context.assumptions,
                assumption_infers: context.infers,
                proof_steps,
                conclusions,
            })
        })
    }

    fn exec_finite_set_induc_base_context(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
    ) -> Result<SuccessExecFiniteSetInducCaseContextResult, RuntimeError> {
        let params = TypedParameterList::new(vec![TypedParameterGroup::new(
            vec![stmt.param_binding.clone()],
            ParamType::FiniteSet(FiniteSet::new()),
        )]);
        let mut infers = self
            .define_params_with_type(&params, false, BindingScope::LocalBinder)
            .map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    "finite-set induc: failed to bind the base finite set".to_string(),
                    Some(error),
                    vec![],
                )
            })?;
        let param = obj_for_bound_param_in_scope(&stmt.param_binding);
        let parameter_type_fact: Fact =
            IsFiniteSetFact::new(param.clone(), stmt.line_file.clone()).into();
        let empty_set: Obj = ListSet::new(vec![]).into();
        let base_eq: Fact = EqualFact::new(param.clone(), empty_set, stmt.line_file.clone()).into();
        let base_infers = self
            .store_with_well_defined_verification_and_infer_with_default_verify_state(
                base_eq.clone(),
            )
            .map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    "finite-set induc: failed to assume the empty base set".to_string(),
                    Some(error),
                    vec![],
                )
            })?;
        infers.new_infer_result_inside(base_infers);
        let mut assumptions = vec![
            self.finite_set_induc_assumption_result(
                parameter_type_fact,
                SuccessVerifyByInducAssumptionRole::ParameterType,
                None,
            )?,
            self.finite_set_induc_assumption_result(
                base_eq,
                SuccessVerifyByInducAssumptionRole::BaseCaseEquality,
                None,
            )?,
        ];
        if let Some(carrier_set) = &stmt.carrier_set {
            let base_subset: Fact =
                SubsetFact::new(param, carrier_set.clone(), stmt.line_file.clone()).into();
            let subset_infers = self
                .store_with_well_defined_verification_and_infer_with_default_verify_state(
                    base_subset.clone(),
                )
                .map_err(|error| {
                    short_exec_error(
                        stmt.clone().into(),
                        "finite-set induc: failed to assume the base carrier subset".to_string(),
                        Some(error),
                        vec![],
                    )
                })?;
            infers.new_infer_result_inside(subset_infers);
            assumptions.push(self.finite_set_induc_assumption_result(
                base_subset,
                SuccessVerifyByInducAssumptionRole::CarrierConstraint,
                None,
            )?);
        }
        self.attach_known_fact_ids_to_infer_result(&mut infers)?;
        Ok(SuccessExecFiniteSetInducCaseContextResult {
            assumptions,
            infers,
        })
    }

    fn exec_finite_set_induc_step_context(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
    ) -> Result<SuccessExecFiniteSetInducCaseContextResult, RuntimeError> {
        let element_type = match &stmt.carrier_set {
            Some(carrier_set) => ParamType::Obj(carrier_set.clone()),
            None => ParamType::Set(Set::new()),
        };
        let params = TypedParameterList::new(vec![
            TypedParameterGroup::new(vec![stmt.element_param_binding.clone()], element_type),
            TypedParameterGroup::new(
                vec![stmt.smaller_set_param_binding.clone()],
                ParamType::FiniteSet(FiniteSet::new()),
            ),
        ]);
        let mut infers = self
            .define_params_with_type(&params, false, BindingScope::LocalBinder)
            .map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    "finite-set induc: failed to bind the insertion parameters".to_string(),
                    Some(error),
                    vec![],
                )
            })?;

        let element = obj_for_bound_param_in_scope(&stmt.element_param_binding);
        let smaller_set = obj_for_bound_param_in_scope(&stmt.smaller_set_param_binding);
        let element_type_fact: Fact = match &stmt.carrier_set {
            Some(carrier_set) => {
                InFact::new(element.clone(), carrier_set.clone(), stmt.line_file.clone()).into()
            }
            None => IsSetFact::new(element.clone(), stmt.line_file.clone()).into(),
        };
        let smaller_type_fact: Fact =
            IsFiniteSetFact::new(smaller_set.clone(), stmt.line_file.clone()).into();
        let mut assumptions = vec![
            self.finite_set_induc_assumption_result(
                element_type_fact,
                SuccessVerifyByInducAssumptionRole::ParameterType,
                None,
            )?,
            self.finite_set_induc_assumption_result(
                smaller_type_fact,
                SuccessVerifyByInducAssumptionRole::ParameterType,
                None,
            )?,
        ];
        let fresh_fact: Fact =
            NotInFact::new(element, smaller_set.clone(), stmt.line_file.clone()).into();
        let fresh_infers = self
            .store_with_well_defined_verification_and_infer_with_default_verify_state(
                fresh_fact.clone(),
            )
            .map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    "finite-set induc: failed to assume the fresh insertion element".to_string(),
                    Some(error),
                    vec![],
                )
            })?;
        infers.new_infer_result_inside(fresh_infers);

        if let Some(carrier_set) = &stmt.carrier_set {
            let smaller_subset: Fact = SubsetFact::new(
                smaller_set.clone(),
                carrier_set.clone(),
                stmt.line_file.clone(),
            )
            .into();
            let subset_infers = self
                .store_with_well_defined_verification_and_infer_with_default_verify_state(
                    smaller_subset.clone(),
                )
                .map_err(|error| {
                    short_exec_error(
                        stmt.clone().into(),
                        "finite-set induc: failed to assume the smaller carrier subset".to_string(),
                        Some(error),
                        vec![],
                    )
                })?;
            infers.new_infer_result_inside(subset_infers);
            assumptions.push(self.finite_set_induc_assumption_result(
                smaller_subset,
                SuccessVerifyByInducAssumptionRole::CarrierConstraint,
                None,
            )?);
        }
        assumptions.push(self.finite_set_induc_assumption_result(
            fresh_fact,
            SuccessVerifyByInducAssumptionRole::FreshInsertionElement,
            None,
        )?);

        for (goal_index, fact) in stmt.to_prove.iter().enumerate() {
            let ih = self.finite_set_induc_goal_fact_at_obj(stmt, fact, smaller_set.clone())?;
            let ih_infers = self
                .store_with_well_defined_verification_and_infer_with_default_verify_state(
                    ih.clone(),
                )
                .map_err(|error| {
                    short_exec_error(
                        stmt.clone().into(),
                        "finite-set induc: failed to assume the induction hypothesis".to_string(),
                        Some(error),
                        vec![],
                    )
                })?;
            infers.new_infer_result_inside(ih_infers);
            assumptions.push(self.finite_set_induc_assumption_result(
                ih,
                SuccessVerifyByInducAssumptionRole::InductionHypothesis,
                Some(goal_index),
            )?);
        }
        self.attach_known_fact_ids_to_infer_result(&mut infers)?;
        Ok(SuccessExecFiniteSetInducCaseContextResult {
            assumptions,
            infers,
        })
    }

    fn exec_finite_set_induc_proof_stmts(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
        proof: &[Stmt],
        label: &str,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let mut inside_results = Vec::new();
        for (index, proof_stmt) in proof.iter().enumerate() {
            match self.execute_statement(proof_stmt) {
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
            .inst_exist_or_and_chain_atomic_fact(
                fact,
                &param_to_set,
                SubstitutionMode::Exact,
                None,
            )?
            .to_fact())
    }

    fn finite_set_induc_extension_obj(&self, stmt: &ByFiniteSetInducStmt) -> Obj {
        let element = obj_for_bound_param_in_scope(&stmt.element_param_binding);
        let smaller_set = obj_for_bound_param_in_scope(&stmt.smaller_set_param_binding);
        Union::new(ListSet::new(vec![element]).into(), smaller_set).into()
    }

    fn finite_set_induc_stored_forall_fact(
        &mut self,
        stmt: &ByFiniteSetInducStmt,
    ) -> Result<Fact, RuntimeError> {
        let (forall_names, param_to_forall) =
            self.fresh_binder_retag_plan_for_bindings(std::slice::from_ref(&stmt.param_binding));
        let param = param_to_forall[stmt.param()].clone();
        let mut then_facts = Vec::with_capacity(stmt.to_prove.len());
        for fact in stmt.to_prove.iter() {
            then_facts.push(self.inst_exist_or_and_chain_atomic_fact(
                fact,
                &param_to_forall,
                SubstitutionMode::Exact,
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
            TypedParameterList::new(vec![TypedParameterGroup::new(
                vec![forall_names[0].clone()],
                ParamType::FiniteSet(FiniteSet::new()),
            )]),
            dom_facts,
            then_facts,
            stmt.line_file.clone(),
        )?
        .into())
    }

    fn finite_set_induc_assumption_result(
        &self,
        fact: Fact,
        role: SuccessVerifyByInducAssumptionRole,
        goal_index: Option<usize>,
    ) -> Result<SuccessVerifyByInducAssumptionResult, RuntimeError> {
        let fact_id = self.require_known_fact_id_for_success_result(&fact)?;
        Ok(SuccessVerifyByInducAssumptionResult {
            fact,
            fact_id,
            role,
            goal_index,
        })
    }
}
