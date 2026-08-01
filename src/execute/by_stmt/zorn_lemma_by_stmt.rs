use super::helpers_by_stmt::{section_inferred_fact, user_defined_prop_arity};
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_zorn_lemma_stmt(
        &mut self,
        stmt: &ByZornLemmaStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let prop_name = stmt.prop_name.to_string();
        match user_defined_prop_arity(self, &prop_name) {
            Some(arity) => {
                if arity != 2 {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by zorn_lemma: `{}` must be a binary user-defined prop",
                            prop_name
                        ),
                        None,
                        vec![],
                    ));
                }
            }
            None => {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!("by zorn_lemma: `{}` must be a user-defined prop", prop_name),
                    None,
                    vec![],
                ));
            }
        }

        self.verify_obj_well_defined_and_store_cache(
            &stmt.set,
            &UseContextVerifyState::new(0, false),
        )
        .map_err(|well_defined_error| {
            short_exec_error(
                stmt.clone().into(),
                format!("by zorn_lemma: set `{}` is not well-defined", stmt.set),
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
                            "by zorn_lemma: failed to execute proof stmt `{}`",
                            proof_stmt
                        ),
                        Some(statement_error),
                        std::mem::take(&mut inside_results),
                    )
                })?;
                inside_results.push(result);
            }

            let obligations = zorn_lemma_obligations(
                rt,
                stmt.set.clone(),
                stmt.prop_name.clone(),
                stmt.line_file.clone(),
            )?;
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
                                "by zorn_lemma: failed to prove {} obligation `{}`",
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

        // Trusted Zorn step: once the local section proves nonempty, partial order,
        // and chain upper-bound obligations on S, infer a maximal element of S.
        // Example: by zorn_lemma: set S, prop leq: stores exist m S st {forall! x S: $leq(m, x) => {x = m}}.
        let maximal_fact = zorn_lemma_maximal_fact(
            self,
            stmt.set.clone(),
            stmt.prop_name.clone(),
            stmt.line_file.clone(),
        )?;
        let maximal_fact_string = maximal_fact.to_string();
        let infer_result = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state(maximal_fact)
            .map_err(|store_error| {
                short_exec_error(
                    stmt.clone().into(),
                    "by zorn_lemma: failed to store maximal element conclusion".to_string(),
                    Some(store_error),
                    vec![],
                )
            })?;

        let by_verification = ByChoiceVerificationResult::new(
            "by zorn_lemma proof".to_string(),
            format!("set {}, prop {}", stmt.set, stmt.prop_name),
            stmt.proof.len(),
            obligations_for_output,
            maximal_fact_string,
        );
        Ok(NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            infer_result,
            inside_results,
            ByVerificationResult::ZornLemma(by_verification),
        )
        .into())
    }

    pub(crate) fn exec_by_zorn_lemma_stmt_affect_environment_only(
        &mut self,
        stmt: &ByZornLemmaStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let prop_name = stmt.prop_name.to_string();
        match user_defined_prop_arity(self, &prop_name) {
            Some(arity) => {
                if arity != 2 {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by zorn_lemma: `{}` must be a binary user-defined prop",
                            prop_name
                        ),
                        None,
                        vec![],
                    ));
                }
            }
            None => {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!("by zorn_lemma: `{}` must be a user-defined prop", prop_name),
                    None,
                    vec![],
                ));
            }
        }

        let maximal_fact = zorn_lemma_maximal_fact(
            self,
            stmt.set.clone(),
            stmt.prop_name.clone(),
            stmt.line_file.clone(),
        )?;
        let infer_result = self.store_trusted_fact_and_infer_with_reason(
            maximal_fact,
            InferReason::VerifiedStatement,
        )?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }
}

fn zorn_lemma_obligations(
    runtime: &Runtime,
    set: Obj,
    prop_name: AtomicName,
    line_file: LineFile,
) -> Result<Vec<(String, Fact)>, RuntimeError> {
    Ok(vec![
        (
            "nonempty".to_string(),
            IsNonemptySetFact::new(set.clone(), line_file.clone()).into(),
        ),
        (
            "reflexive".to_string(),
            zorn_reflexive_fact(runtime, set.clone(), prop_name.clone(), line_file.clone())?,
        ),
        (
            "transitive".to_string(),
            zorn_transitive_fact(runtime, set.clone(), prop_name.clone(), line_file.clone())?,
        ),
        (
            "antisymmetric".to_string(),
            zorn_antisymmetric_fact(runtime, set.clone(), prop_name.clone(), line_file.clone())?,
        ),
        (
            "chain_upper_bound".to_string(),
            zorn_chain_upper_bound_fact(runtime, set, prop_name, line_file)?,
        ),
    ])
}

fn zorn_reflexive_fact(
    runtime: &Runtime,
    set: Obj,
    prop_name: AtomicName,
    line_file: LineFile,
) -> Result<Fact, RuntimeError> {
    let x_name = runtime.generate_internal_binder_name();
    let params = runtime.fresh_param_group_with_type(vec![x_name], ParamType::Obj(set))?;
    let x = obj_for_bound_param_in_scope(&params.params[0], ParamObjType::Forall);
    Ok(ForallFact::new(
        ParamDefWithType::new(vec![params]),
        vec![],
        vec![normal_prop_fact(prop_name, vec![x.clone(), x], line_file.clone()).into()],
        line_file,
    )?
    .into())
}

fn zorn_transitive_fact(
    runtime: &Runtime,
    set: Obj,
    prop_name: AtomicName,
    line_file: LineFile,
) -> Result<Fact, RuntimeError> {
    let x_name = runtime.generate_internal_binder_name();
    let y_name = runtime.generate_internal_binder_name();
    let z_name = runtime.generate_internal_binder_name();
    let params =
        runtime.fresh_param_group_with_type(vec![x_name, y_name, z_name], ParamType::Obj(set))?;
    let x = obj_for_bound_param_in_scope(&params.params[0], ParamObjType::Forall);
    let y = obj_for_bound_param_in_scope(&params.params[1], ParamObjType::Forall);
    let z = obj_for_bound_param_in_scope(&params.params[2], ParamObjType::Forall);
    Ok(ForallFact::new(
        ParamDefWithType::new(vec![params]),
        vec![
            normal_prop_fact(
                prop_name.clone(),
                vec![x.clone(), y.clone()],
                line_file.clone(),
            )
            .into(),
            normal_prop_fact(prop_name.clone(), vec![y, z.clone()], line_file.clone()).into(),
        ],
        vec![normal_prop_fact(prop_name, vec![x, z], line_file.clone()).into()],
        line_file,
    )?
    .into())
}

fn zorn_antisymmetric_fact(
    runtime: &Runtime,
    set: Obj,
    prop_name: AtomicName,
    line_file: LineFile,
) -> Result<Fact, RuntimeError> {
    let x_name = runtime.generate_internal_binder_name();
    let y_name = runtime.generate_internal_binder_name();
    let params = runtime.fresh_param_group_with_type(vec![x_name, y_name], ParamType::Obj(set))?;
    let x = obj_for_bound_param_in_scope(&params.params[0], ParamObjType::Forall);
    let y = obj_for_bound_param_in_scope(&params.params[1], ParamObjType::Forall);
    Ok(ForallFact::new(
        ParamDefWithType::new(vec![params]),
        vec![
            normal_prop_fact(
                prop_name.clone(),
                vec![x.clone(), y.clone()],
                line_file.clone(),
            )
            .into(),
            normal_prop_fact(
                prop_name.clone(),
                vec![y.clone(), x.clone()],
                line_file.clone(),
            )
            .into(),
        ],
        vec![EqualFact::new(x, y, line_file.clone()).into()],
        line_file,
    )?
    .into())
}

fn zorn_chain_upper_bound_fact(
    runtime: &Runtime,
    set: Obj,
    prop_name: AtomicName,
    line_file: LineFile,
) -> Result<Fact, RuntimeError> {
    let c_name = runtime.generate_internal_binder_name();
    let c_group = runtime.fresh_param_group_with_type(
        vec![c_name],
        ParamType::Obj(PowerSet::new(set.clone()).into()),
    )?;
    let c = obj_for_bound_param_in_scope(&c_group.params[0], ParamObjType::Forall);
    let chain_total_fact =
        zorn_chain_total_fact(runtime, c.clone(), prop_name.clone(), line_file.clone())?;
    let upper_bound_fact =
        zorn_upper_bound_exist_fact(runtime, set.clone(), c, prop_name, line_file.clone())?;

    Ok(ForallFact::new(
        ParamDefWithType::new(vec![c_group]),
        vec![chain_total_fact],
        vec![upper_bound_fact.into()],
        line_file,
    )?
    .into())
}

fn zorn_chain_total_fact(
    runtime: &Runtime,
    chain: Obj,
    prop_name: AtomicName,
    line_file: LineFile,
) -> Result<Fact, RuntimeError> {
    let x_name = runtime.generate_internal_binder_name();
    let y_name = runtime.generate_internal_binder_name();
    let params =
        runtime.fresh_param_group_with_type(vec![x_name, y_name], ParamType::Obj(chain))?;
    let x = obj_for_bound_param_in_scope(&params.params[0], ParamObjType::Forall);
    let y = obj_for_bound_param_in_scope(&params.params[1], ParamObjType::Forall);
    let left: AndChainAtomicFact = normal_prop_fact(
        prop_name.clone(),
        vec![x.clone(), y.clone()],
        line_file.clone(),
    )
    .into();
    let right: AndChainAtomicFact =
        normal_prop_fact(prop_name, vec![y, x], line_file.clone()).into();

    Ok(ForallFact::new(
        ParamDefWithType::new(vec![params]),
        vec![],
        vec![OrFact::new(vec![left, right], line_file.clone()).into()],
        line_file,
    )?
    .into())
}

fn zorn_upper_bound_exist_fact(
    runtime: &Runtime,
    set: Obj,
    chain: Obj,
    prop_name: AtomicName,
    line_file: LineFile,
) -> Result<ExistFactEnum, RuntimeError> {
    let u_name = runtime.generate_internal_binder_name();
    let u_group = runtime.fresh_param_group_with_type(vec![u_name], ParamType::Obj(set))?;
    let u = obj_for_bound_param_in_scope(&u_group.params[0], ParamObjType::Exist);
    let upper_forall =
        zorn_upper_bound_forall_fact(runtime, chain, u, prop_name, line_file.clone())?;
    let body = ExistFactBody::new(
        ParamDefWithType::new(vec![u_group]),
        vec![ExistBodyFact::InlineForall(upper_forall)],
        line_file,
    )?;
    Ok(ExistFactEnum::ExistFact(body))
}

fn zorn_upper_bound_forall_fact(
    runtime: &Runtime,
    chain: Obj,
    upper: Obj,
    prop_name: AtomicName,
    line_file: LineFile,
) -> Result<ForallFact, RuntimeError> {
    let x_name = runtime.generate_internal_binder_name();
    let x_group = runtime.fresh_param_group_with_type(vec![x_name], ParamType::Obj(chain))?;
    let x = obj_for_bound_param_in_scope(&x_group.params[0], ParamObjType::Forall);
    ForallFact::new(
        ParamDefWithType::new(vec![x_group]),
        vec![],
        vec![normal_prop_fact(prop_name, vec![x, upper], line_file.clone()).into()],
        line_file,
    )
}

fn zorn_lemma_maximal_fact(
    runtime: &Runtime,
    set: Obj,
    prop_name: AtomicName,
    line_file: LineFile,
) -> Result<Fact, RuntimeError> {
    let m_name = runtime.generate_internal_binder_name();
    let m_group = runtime.fresh_param_group_with_type(vec![m_name], ParamType::Obj(set.clone()))?;
    let m = obj_for_bound_param_in_scope(&m_group.params[0], ParamObjType::Exist);
    let maximal_forall = zorn_maximal_forall_fact(
        runtime,
        set.clone(),
        m.clone(),
        prop_name,
        line_file.clone(),
    )?;
    let body = ExistFactBody::new(
        ParamDefWithType::new(vec![m_group]),
        vec![ExistBodyFact::InlineForall(maximal_forall)],
        line_file,
    )?;
    Ok(ExistFactEnum::ExistFact(body).into())
}

fn zorn_maximal_forall_fact(
    runtime: &Runtime,
    set: Obj,
    maximal: Obj,
    prop_name: AtomicName,
    line_file: LineFile,
) -> Result<ForallFact, RuntimeError> {
    let x_name = runtime.generate_internal_binder_name();
    let x_group = runtime.fresh_param_group_with_type(vec![x_name], ParamType::Obj(set))?;
    let x = obj_for_bound_param_in_scope(&x_group.params[0], ParamObjType::Forall);
    ForallFact::new(
        ParamDefWithType::new(vec![x_group]),
        vec![normal_prop_fact(
            prop_name,
            vec![maximal.clone(), x.clone()],
            line_file.clone(),
        )
        .into()],
        vec![EqualFact::new(x, maximal, line_file.clone()).into()],
        line_file,
    )
}

fn normal_prop_fact(prop_name: AtomicName, body: Vec<Obj>, line_file: LineFile) -> AtomicFact {
    NormalAtomicFact::new(prop_name, body, line_file).into()
}
