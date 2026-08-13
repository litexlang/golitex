use super::helpers_by_stmt::section_inferred_fact;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_axiom_of_choice_stmt(
        &mut self,
        stmt: &ByAxiomOfChoiceStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(
            &stmt.family,
            &UseContextVerifyState::new(0, false),
        )
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

        let (inside_results, obligations_for_output) = self.run_in_local_env(|rt| {
            let mut inside_results: Vec<StmtResult> = Vec::new();
            for proof_stmt in stmt.proof.iter() {
                let result = rt.exec_stmt(proof_stmt).map_err(|statement_error| {
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
                inside_results.push(result);
            }

            let obligations =
                axiom_of_choice_obligations(rt, stmt.family.clone(), stmt.line_file.clone())?;
            let mut obligations_for_output = Vec::new();
            for (label, fact) in obligations {
                if section_inferred_fact(&inside_results, &fact) {
                    obligations_for_output.push((label, fact.to_string(), false));
                    continue;
                }
                let result = rt
                    .verify_fact_return_err_if_not_true(
                        &fact,
                        &UseContextVerifyState::new(0, false),
                    )
                    .map_err(|verify_error| {
                        short_exec_error(
                            stmt.clone().into(),
                            format!(
                                "by axiom_of_choice: failed to prove {} obligation `{}`",
                                label, fact
                            ),
                            Some(verify_error),
                            std::mem::take(&mut inside_results),
                        )
                    })?;
                obligations_for_output.push((label, fact.to_string(), true));
                inside_results.push(result);
            }
            Ok::<_, RuntimeError>((inside_results, obligations_for_output))
        })?;

        // Trusted axiom-of-choice step. The quantified selection condition is
        // exposed through a named builtin predicate, so the existential body
        // remains atomic:
        // exist f fn(A S) big_union(S) st {
        //     $is_choice_function_for(S, S, fn(A S) S {A}, f)
        // }.
        let choice_fact =
            axiom_of_choice_exist_fact(self, stmt.family.clone(), stmt.line_file.clone())?;
        let choice_fact_string = choice_fact.to_string();
        let infer_result = self
            .store_with_well_defined_verification_and_infer_with_default_verify_state(choice_fact)
            .map_err(|store_error| {
                short_exec_error(
                    stmt.clone().into(),
                    "by axiom_of_choice: failed to store choice-function conclusion".to_string(),
                    Some(store_error),
                    vec![],
                )
            })?;

        let by_verification = ByChoiceVerificationResult::new(
            "by axiom_of_choice proof".to_string(),
            stmt.family.to_string(),
            stmt.proof.len(),
            obligations_for_output,
            choice_fact_string,
        );
        Ok(NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            infer_result,
            inside_results,
            ByVerificationResult::AxiomOfChoice(by_verification),
        )
        .into())
    }

    pub(crate) fn exec_by_axiom_of_choice_stmt_affect_environment_only(
        &mut self,
        stmt: &ByAxiomOfChoiceStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let choice_fact =
            axiom_of_choice_exist_fact(self, stmt.family.clone(), stmt.line_file.clone())?;
        let infer_result = self.store_trusted_fact_and_infer_with_reason(
            choice_fact,
            InferReason::VerifiedStatement,
        )?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }
}

fn axiom_of_choice_obligations(
    runtime: &Runtime,
    family: Obj,
    line_file: LineFile,
) -> Result<Vec<(String, Fact)>, RuntimeError> {
    Ok(vec![
        (
            "family_is_set".to_string(),
            IsSetFact::new(family.clone(), line_file.clone()).into(),
        ),
        (
            "members_nonempty".to_string(),
            axiom_of_choice_members_nonempty_fact(runtime, family, line_file)?,
        ),
    ])
}

fn axiom_of_choice_members_nonempty_fact(
    runtime: &Runtime,
    family: Obj,
    line_file: LineFile,
) -> Result<Fact, RuntimeError> {
    let a_name = runtime.generate_internal_binder_name();
    let a_group =
        runtime.fresh_param_group_with_type(vec![a_name], ParamType::Obj(family.clone()))?;
    let a = obj_for_bound_param_in_scope(&a_group.params[0], ParamObjType::Forall);
    Ok(ForallFact::new_canonical_forall(
        ParamDefWithType::new(vec![a_group]),
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
    let f = obj_for_bound_param_in_scope(&f_group.params[0], ParamObjType::Exist);

    let identity_index_name = runtime.generate_internal_binder_name();
    let identity_index_group =
        runtime.fresh_param_group_with_set(vec![identity_index_name], family.clone())?;
    let identity_value =
        obj_for_bound_param_in_scope(&identity_index_group.params[0], ParamObjType::FnSet);
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
        ParamDefWithType::new(vec![f_group]),
        vec![QuantifierFreeFact::AtomicFact(named_choice_fact)],
        line_file,
    )?;
    Ok(ExistFactEnum::ExistFact(body).into())
}
