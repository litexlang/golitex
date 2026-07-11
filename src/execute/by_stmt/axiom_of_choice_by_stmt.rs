use super::helpers_by_stmt::section_inferred_fact;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_axiom_of_choice_stmt(
        &mut self,
        stmt: &ByAxiomOfChoiceStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&stmt.family, &VerifyState::new(0, false))
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
                axiom_of_choice_obligations(stmt.family.clone(), stmt.line_file.clone())?;
            let mut obligations_for_output = Vec::new();
            for (label, fact) in obligations {
                if section_inferred_fact(&inside_results, &fact) {
                    obligations_for_output.push((label, fact.to_string(), false));
                    continue;
                }
                let result = rt
                    .verify_fact_return_err_if_not_true(&fact, &VerifyState::new(0, false))
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

        // Trusted axiom of choice step: once S is a set whose members are
        // nonempty, infer the existence of a function choosing one element
        // from each member. Example: by axiom_of_choice: set S: stores
        // exist f fn(A S) cup(S) st {forall! A S => {f(A) $in A}}.
        let choice_fact = axiom_of_choice_exist_fact(stmt.family.clone(), stmt.line_file.clone())?;
        let choice_fact_string = choice_fact.to_string();
        let infer_result = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state(choice_fact)
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
        let choice_fact = axiom_of_choice_exist_fact(stmt.family.clone(), stmt.line_file.clone())?;
        let infer_result = self.store_trusted_fact_and_infer_with_reason(
            choice_fact,
            InferReason::VerifiedStatement,
        )?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }
}

fn axiom_of_choice_obligations(
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
            axiom_of_choice_members_nonempty_fact(family, line_file)?,
        ),
    ])
}

fn axiom_of_choice_members_nonempty_fact(
    family: Obj,
    line_file: LineFile,
) -> Result<Fact, RuntimeError> {
    let a_name = "A".to_string();
    let a = forall_obj(&a_name);
    Ok(ForallFact::new(
        ParamDefWithType::new(vec![ParamGroupWithParamType::new(
            vec![a_name],
            ParamType::Obj(family),
        )]),
        vec![],
        vec![IsNonemptySetFact::new(a, line_file.clone()).into()],
        line_file,
    )?
    .into())
}

fn axiom_of_choice_exist_fact(family: Obj, line_file: LineFile) -> Result<Fact, RuntimeError> {
    let f_name = "f".to_string();
    let a_name = "A".to_string();
    let choice_fn_set = FnSet::new(
        vec![ParamGroupWithSet::new(vec![a_name.clone()], family.clone())],
        vec![],
        Cup::new(family.clone()).into(),
    )?;
    let body = ExistFactBody::new(
        ParamDefWithType::new(vec![ParamGroupWithParamType::new(
            vec![f_name.clone()],
            ParamType::Obj(choice_fn_set.into()),
        )]),
        vec![ExistBodyFact::InlineForall(axiom_of_choice_value_fact(
            family,
            f_name,
            a_name,
            line_file.clone(),
        )?)],
        line_file,
    )?;
    Ok(ExistFactEnum::ExistFact(body).into())
}

fn axiom_of_choice_value_fact(
    family: Obj,
    f_name: String,
    a_name: String,
    line_file: LineFile,
) -> Result<ForallFact, RuntimeError> {
    let a = forall_obj(&a_name);
    let f_head: FnObjHead = ExistFreeParamObj::new(f_name).into();
    let f_of_a: Obj = FnObj::new(f_head, vec![vec![Box::new(a.clone())]]).into();
    ForallFact::new(
        ParamDefWithType::new(vec![ParamGroupWithParamType::new(
            vec![a_name],
            ParamType::Obj(family),
        )]),
        vec![],
        vec![InFact::new(f_of_a, a, line_file.clone()).into()],
        line_file,
    )
}

fn forall_obj(name: &str) -> Obj {
    obj_for_bound_param_in_scope(name.to_string(), ParamObjType::Forall)
}
