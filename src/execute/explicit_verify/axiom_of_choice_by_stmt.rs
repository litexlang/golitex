use super::helpers_by_stmt::section_inferred_fact_id;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_axiom_of_choice_stmt(
        &mut self,
        stmt: &ByAxiomOfChoiceStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&stmt.family, &VerifyState::initial())
            .map_err(|well_defined_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by axiom_of_choice: family `{}` is not well-defined",
                        stmt.family
                    ),
                    Some(well_defined_error),
                    vec![],
                )
            })?;

        let (mut inside_results, obligations_for_output) = self.run_in_local_env(|rt| {
            let mut inside_results: Vec<StmtResult> = Vec::new();
            for proof_stmt in stmt.proof.iter() {
                let mut result = rt
                    .execute_statement(proof_stmt)
                    .map_err(|statement_error| {
                        short_exec_error(
                            stmt.clone().into(),
                            format!(
                                "by axiom_of_choice: failed to execute proof stmt `{}`",
                                proof_stmt
                            ),
                            Some(statement_error),
                            std::mem::take(&mut inside_results),
                        )
                    })?;
                rt.attach_known_fact_ids_to_stmt_result(&mut result)?;
                inside_results.push(result);
            }

            let obligations =
                axiom_of_choice_obligations(rt, stmt.family.clone(), stmt.line_file.clone())?;
            let mut obligations_for_output = Vec::new();
            for (role, fact) in obligations {
                if let Some(fact_id) = section_inferred_fact_id(&inside_results, &fact) {
                    obligations_for_output.push((role, fact, fact_id, false));
                    continue;
                }
                let mut result = rt
                    .verify_fact_or_error(&fact, &VerifyState::initial())
                    .map_err(|verify_error| {
                        short_exec_error(
                            stmt.clone().into(),
                            format!(
                                "by axiom_of_choice: failed to prove {} obligation `{}`",
                                choice_obligation_label(role),
                                fact
                            ),
                            Some(verify_error),
                            std::mem::take(&mut inside_results),
                        )
                    })?;
                let store = rt
                    .store_with_well_defined_verification_and_infer_with_default_verify_state(
                        fact.clone(),
                    )
                    .map_err(|store_error| {
                        short_exec_error(
                            stmt.clone().into(),
                            format!(
                                "by axiom_of_choice: failed to retain verified {} obligation `{}`",
                                choice_obligation_label(role),
                                fact
                            ),
                            Some(store_error),
                            std::mem::take(&mut inside_results),
                        )
                    })?;
                result = result.with_infers(store);
                rt.attach_known_fact_ids_to_stmt_result(&mut result)?;
                let fact_id = result
                    .fact_id()
                    .map(Ok)
                    .unwrap_or_else(|| rt.require_known_fact_id_for_success_result(&fact))?;
                obligations_for_output.push((role, fact, fact_id, true));
                inside_results.push(result);
            }
            Ok::<_, RuntimeError>((inside_results, obligations_for_output))
        })?;
        let proof_steps = inside_results.drain(..stmt.proof.len()).collect::<Vec<_>>();
        let mut checked_obligations = inside_results.into_iter();
        let obligations = obligations_for_output
            .into_iter()
            .map(
                |(role, fact, fact_id, checked)| SuccessVerifyByChoiceObligationResult {
                    role,
                    fact,
                    fact_id,
                    check: checked.then(|| {
                        Box::new(
                            checked_obligations
                                .next()
                                .expect("checked choice obligation retains its result"),
                        )
                    }),
                },
            )
            .collect();

        // Trusted axiom-of-choice step. The quantified selection condition is
        // exposed through a named builtin predicate, so the existential body
        // remains atomic:
        // exist f fn(A S) big_union(S) st {
        //     $is_choice_function_for(S, S, fn(A S) S {A}, f)
        // }.
        let choice_fact =
            axiom_of_choice_exist_fact(self, stmt.family.clone(), stmt.line_file.clone())?;
        let infer_result = self
            .store_with_well_defined_verification_and_infer_with_default_verify_state(
                choice_fact.clone(),
            )
            .map_err(|store_error| {
                short_exec_error(
                    stmt.clone().into(),
                    "by axiom_of_choice: failed to store choice-function conclusion".to_string(),
                    Some(store_error),
                    vec![],
                )
            })?;
        let choice_fact_id = self.require_known_fact_id_for_success_result(&choice_fact)?;

        let by_verification = SuccessVerifyByChoiceResult::new(
            SuccessVerifyByChoiceProofKind::AxiomOfChoice,
            SuccessVerifyByChoiceTargetResult::AxiomOfChoice {
                family: stmt.family.clone(),
            },
            proof_steps,
            obligations,
            choice_fact,
            choice_fact_id,
        );
        Ok(
            SuccessByStmtResult::ByAxiomOfChoiceStmt(Box::new(SuccessByAxiomOfChoiceStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: Some(by_verification),
            }))
            .into(),
        )
    }

    pub fn exec_by_axiom_of_choice_stmt_affect_environment_only(
        &mut self,
        stmt: &ByAxiomOfChoiceStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let choice_fact =
            axiom_of_choice_exist_fact(self, stmt.family.clone(), stmt.line_file.clone())?;
        let infer_result = self.store_trusted_fact_and_infer_with_reason(
            choice_fact,
            InferReason::VerifiedStatement,
        )?;
        Ok(
            SuccessByStmtResult::ByAxiomOfChoiceStmt(Box::new(SuccessByAxiomOfChoiceStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: None,
            }))
            .into(),
        )
    }
}

fn axiom_of_choice_obligations(
    runtime: &Runtime,
    family: Obj,
    line_file: LineFile,
) -> Result<Vec<(SuccessVerifyByChoiceObligationRole, Fact)>, RuntimeError> {
    Ok(vec![
        (
            SuccessVerifyByChoiceObligationRole::ChoiceFamilyIsSet,
            IsSetFact::new(family.clone(), line_file.clone()).into(),
        ),
        (
            SuccessVerifyByChoiceObligationRole::ChoiceMembersNonempty,
            axiom_of_choice_members_nonempty_fact(runtime, family, line_file)?,
        ),
    ])
}

fn choice_obligation_label(role: SuccessVerifyByChoiceObligationRole) -> &'static str {
    match role {
        SuccessVerifyByChoiceObligationRole::ChoiceFamilyIsSet => "family_is_set",
        SuccessVerifyByChoiceObligationRole::ChoiceMembersNonempty => "members_nonempty",
        _ => unreachable!("axiom-of-choice producer only creates choice obligation roles"),
    }
}

fn axiom_of_choice_members_nonempty_fact(
    runtime: &Runtime,
    family: Obj,
    line_file: LineFile,
) -> Result<Fact, RuntimeError> {
    let a_name = runtime.generate_internal_binder_name();
    let a_group =
        runtime.fresh_param_group_with_type(vec![a_name], ParamType::Obj(family.clone()))?;
    let a = obj_for_bound_param_in_scope(&a_group.params[0]);
    Ok(ForallFact::new_canonical_forall(
        TypedParameterList::new(vec![a_group]),
        vec![],
        vec![IsNonemptySetFact::new(a, line_file.clone()).into()],
        line_file,
    )?
    .into())
}

fn axiom_of_choice_exist_fact(
    runtime: &Runtime,
    family: Obj,
    line_file: LineFile,
) -> Result<Fact, RuntimeError> {
    let choice_index_name = runtime.generate_internal_binder_name();
    let choice_index_group =
        runtime.fresh_param_group_with_set(vec![choice_index_name], family.clone())?;
    let choice_fn_set = FnSet::new(
        vec![choice_index_group],
        vec![],
        BigUnion::new(family.clone()).into(),
    )?;

    let f_name = runtime.generate_internal_binder_name();
    let f_group =
        runtime.fresh_param_group_with_type(vec![f_name], ParamType::Obj(choice_fn_set.into()))?;
    let f = obj_for_bound_param_in_scope(&f_group.params[0]);

    let identity_index_name = runtime.generate_internal_binder_name();
    let identity_index_group =
        runtime.fresh_param_group_with_set(vec![identity_index_name], family.clone())?;
    let identity_value = obj_for_bound_param_in_scope(&identity_index_group.params[0]);
    let identity_family: Obj = AnonymousFn::new(
        vec![identity_index_group],
        vec![],
        family.clone(),
        identity_value,
    )?
    .into();

    let named_choice_fact = crate::verify::choice_function_for_fact(
        family.clone(),
        family,
        identity_family,
        f,
        line_file.clone(),
    );
    let body = ExistentialSpec::new(
        TypedParameterList::new(vec![f_group]),
        vec![QuantifierFreeFact::AtomicFact(named_choice_fact)],
        line_file,
    )?;
    Ok(ExistFactEnum::ExistFact(body).into())
}
