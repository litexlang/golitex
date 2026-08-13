use super::helpers_by_stmt::{section_inferred_fact, user_defined_prop_arity};
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_zorn_lemma_stmt(
        &mut self,
        stmt: &ByZornLemmaStmt,
    ) -> Result<StmtResult, RuntimeError> {
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
        validate_zorn_named_properties(self, stmt)?;

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
                stmt.upper_bound_prop_name.clone(),
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

        // Trusted Zorn step. Both quantified conditions that occur below an
        // existential are public named props: the chain obligation concludes
        // `exist u S st {$U(c, u)}`, and this step concludes
        // `exist m S st {$M(m)}`. Their exact definitions were checked above.
        let maximal_fact = zorn_lemma_maximal_fact(
            self,
            stmt.set.clone(),
            stmt.maximal_prop_name.clone(),
            stmt.line_file.clone(),
        )?;
        let maximal_fact_string = maximal_fact.to_string();
        let infer_result = self
            .store_with_well_defined_verification_and_infer_with_default_verify_state(maximal_fact)
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
            format!(
                "set {}, prop {}, prop {}, prop {}",
                stmt.set,
                stmt.prop_name,
                stmt.upper_bound_prop_name,
                stmt.maximal_prop_name
            ),
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
        validate_zorn_named_properties(self, stmt)?;
        let maximal_fact = zorn_lemma_maximal_fact(
            self,
            stmt.set.clone(),
            stmt.maximal_prop_name.clone(),
            stmt.line_file.clone(),
        )?;
        let infer_result = self.store_trusted_fact_and_infer_with_reason(
            maximal_fact,
            InferReason::VerifiedStatement,
        )?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }
}

fn validate_zorn_named_properties(
    runtime: &Runtime,
    stmt: &ByZornLemmaStmt,
) -> Result<(), RuntimeError> {
    let relation_name = stmt.prop_name.to_string();
    match user_defined_prop_arity(runtime, &relation_name) {
        Some(2) => {}
        Some(_) => {
            return Err(zorn_interface_error(
                stmt,
                format!(
                    "by zorn_lemma: relation `{}` must be a binary user-defined prop",
                    relation_name
                ),
                None,
            ))
        }
        None => {
            return Err(zorn_interface_error(
                stmt,
                format!(
                    "by zorn_lemma: relation `{}` must be a user-defined prop",
                    relation_name
                ),
                None,
            ))
        }
    }

    validate_zorn_upper_bound_prop(runtime, stmt)?;
    validate_zorn_maximal_prop(runtime, stmt)?;
    Ok(())
}

fn validate_zorn_upper_bound_prop(
    runtime: &Runtime,
    stmt: &ByZornLemmaStmt,
) -> Result<(), RuntimeError> {
    let name = stmt.upper_bound_prop_name.to_string();
    let Some(definition) = runtime.get_prop_definition_by_name(&name) else {
        return Err(zorn_interface_error(
            stmt,
            format!(
                "by zorn_lemma: upper-bound `{}` must be a concrete named prop",
                name
            ),
            None,
        ));
    };
    if definition.params_def_with_type.number_of_params() != 2 {
        return Err(zorn_interface_error(
            stmt,
            format!(
                "by zorn_lemma: upper-bound `{}` must have two parameters `(c power_set(S), u S)`",
                name
            ),
            None,
        ));
    }

    let chain_group = runtime.fresh_param_group_with_type(
        vec![runtime.generate_internal_binder_name()],
        ParamType::Obj(PowerSet::new(stmt.set.clone()).into()),
    )?;
    let chain = obj_for_bound_param_in_scope(&chain_group.params[0], ParamObjType::Forall);
    let upper_group = runtime.fresh_param_group_with_type(
        vec![runtime.generate_internal_binder_name()],
        ParamType::Obj(stmt.set.clone()),
    )?;
    let upper = obj_for_bound_param_in_scope(&upper_group.params[0], ParamObjType::Forall);
    let args = vec![chain.clone(), upper.clone()];
    if !zorn_prop_header_types_match(
        runtime,
        &definition,
        &args,
        &[
            PowerSet::new(stmt.set.clone()).into(),
            stmt.set.clone(),
        ],
    )? {
        return Err(zorn_interface_error(
            stmt,
            format!(
                "by zorn_lemma: upper-bound `{}` must declare `(c power_set({}), u {})`",
                name, stmt.set, stmt.set
            ),
            None,
        ));
    }

    let expected = zorn_upper_bound_forall_fact(
        runtime,
        chain,
        upper,
        stmt.prop_name.clone(),
        stmt.line_file.clone(),
    )?;
    if !zorn_prop_has_exact_forall_definition(runtime, &definition, &args, &expected)? {
        return Err(zorn_interface_error(
            stmt,
            format!(
                "by zorn_lemma: upper-bound `{}` must have exactly the definition `forall x c: ${}(x, u)`",
                name, stmt.prop_name
            ),
            None,
        ));
    }
    Ok(())
}

fn validate_zorn_maximal_prop(
    runtime: &Runtime,
    stmt: &ByZornLemmaStmt,
) -> Result<(), RuntimeError> {
    let name = stmt.maximal_prop_name.to_string();
    let Some(definition) = runtime.get_prop_definition_by_name(&name) else {
        return Err(zorn_interface_error(
            stmt,
            format!(
                "by zorn_lemma: maximality `{}` must be a concrete named prop",
                name
            ),
            None,
        ));
    };
    if definition.params_def_with_type.number_of_params() != 1 {
        return Err(zorn_interface_error(
            stmt,
            format!(
                "by zorn_lemma: maximality `{}` must have one parameter `(m S)`",
                name
            ),
            None,
        ));
    }

    let maximal_group = runtime.fresh_param_group_with_type(
        vec![runtime.generate_internal_binder_name()],
        ParamType::Obj(stmt.set.clone()),
    )?;
    let maximal = obj_for_bound_param_in_scope(&maximal_group.params[0], ParamObjType::Forall);
    let args = vec![maximal.clone()];
    if !zorn_prop_header_types_match(runtime, &definition, &args, &[stmt.set.clone()])? {
        return Err(zorn_interface_error(
            stmt,
            format!(
                "by zorn_lemma: maximality `{}` must declare `(m {})`",
                name, stmt.set
            ),
            None,
        ));
    }

    let expected = zorn_maximal_forall_fact(
        runtime,
        stmt.set.clone(),
        maximal,
        stmt.prop_name.clone(),
        stmt.line_file.clone(),
    )?;
    if !zorn_prop_has_exact_forall_definition(runtime, &definition, &args, &expected)? {
        return Err(zorn_interface_error(
            stmt,
            format!(
                "by zorn_lemma: maximality `{}` must have exactly the definition `forall x {}: ${}(m, x) => x = m`",
                name, stmt.set, stmt.prop_name
            ),
            None,
        ));
    }
    Ok(())
}

fn zorn_prop_header_types_match(
    runtime: &Runtime,
    definition: &DefPropStmt,
    args: &[Obj],
    expected_sets: &[Obj],
) -> Result<bool, RuntimeError> {
    let instantiated_types = runtime.inst_param_def_with_type_one_by_one(
        &definition.params_def_with_type,
        &args.to_vec(),
        ParamObjType::DefHeader,
    )?;
    if instantiated_types.len() != expected_sets.len() {
        return Ok(false);
    }
    for (actual, expected) in instantiated_types.iter().zip(expected_sets.iter()) {
        let ParamType::Obj(actual) = actual else {
            return Ok(false);
        };
        if !objs_equal_with_nested_binder_alpha_equivalence(actual, expected) {
            return Ok(false);
        }
    }
    Ok(true)
}

fn zorn_prop_has_exact_forall_definition(
    runtime: &Runtime,
    definition: &DefPropStmt,
    args: &[Obj],
    expected: &ForallFact,
) -> Result<bool, RuntimeError> {
    let [Fact::ForallFact(actual)] = definition.iff_facts.as_slice() else {
        return Ok(false);
    };
    let param_to_arg_map = runtime.params_to_arg_map(&definition.params_def_with_type, args)?;
    let actual = runtime.inst_forall_fact_without_capture_preparation(
        actual,
        &param_to_arg_map,
        ParamObjType::DefHeader,
        None,
    )?;
    Ok(runtime.alpha_normalized_forall_cache_key(&actual)?
        == runtime.alpha_normalized_forall_cache_key(expected)?)
}

fn zorn_interface_error(
    stmt: &ByZornLemmaStmt,
    message: String,
    previous_error: Option<RuntimeError>,
) -> RuntimeError {
    short_exec_error(stmt.clone().into(), message, previous_error, vec![])
}

fn zorn_lemma_obligations(
    runtime: &Runtime,
    set: Obj,
    prop_name: AtomicName,
    upper_bound_prop_name: AtomicName,
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
            zorn_chain_upper_bound_fact(
                runtime,
                set,
                prop_name,
                upper_bound_prop_name,
                line_file,
            )?,
        ),
    ])
}

fn zorn_reflexive_fact(
    runtime: &Runtime,
    set: Obj,
    prop_name: AtomicName,
    line_file: LineFile,
) -> Result<Fact, RuntimeError> {
    let x_group = runtime.fresh_param_group_with_type(
        vec![runtime.generate_internal_binder_name()],
        ParamType::Obj(set),
    )?;
    let x = obj_for_bound_param_in_scope(&x_group.params[0], ParamObjType::Forall);
    Ok(ForallFact::new_canonical_forall(
        ParamDefWithType::new(vec![x_group]),
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
    let params = runtime.fresh_param_group_with_type(
        vec![
            runtime.generate_internal_binder_name(),
            runtime.generate_internal_binder_name(),
            runtime.generate_internal_binder_name(),
        ],
        ParamType::Obj(set),
    )?;
    let x = obj_for_bound_param_in_scope(&params.params[0], ParamObjType::Forall);
    let y = obj_for_bound_param_in_scope(&params.params[1], ParamObjType::Forall);
    let z = obj_for_bound_param_in_scope(&params.params[2], ParamObjType::Forall);
    Ok(ForallFact::new_canonical_forall(
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
    let params = runtime.fresh_param_group_with_type(
        vec![
            runtime.generate_internal_binder_name(),
            runtime.generate_internal_binder_name(),
        ],
        ParamType::Obj(set),
    )?;
    let x = obj_for_bound_param_in_scope(&params.params[0], ParamObjType::Forall);
    let y = obj_for_bound_param_in_scope(&params.params[1], ParamObjType::Forall);
    Ok(ForallFact::new_canonical_forall(
        ParamDefWithType::new(vec![params]),
        vec![
            normal_prop_fact(
                prop_name.clone(),
                vec![x.clone(), y.clone()],
                line_file.clone(),
            )
            .into(),
            normal_prop_fact(
                prop_name,
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
    upper_bound_prop_name: AtomicName,
    line_file: LineFile,
) -> Result<Fact, RuntimeError> {
    let c_group = runtime.fresh_param_group_with_type(
        vec![runtime.generate_internal_binder_name()],
        ParamType::Obj(PowerSet::new(set.clone()).into()),
    )?;
    let c = obj_for_bound_param_in_scope(&c_group.params[0], ParamObjType::Forall);
    let chain_total_fact =
        zorn_chain_total_fact(runtime, c.clone(), prop_name, line_file.clone())?;
    let upper_bound_fact = zorn_upper_bound_exist_fact(
        runtime,
        set,
        c,
        upper_bound_prop_name,
        line_file.clone(),
    )?;

    Ok(ForallFact::new_canonical_forall(
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
    let params = runtime.fresh_param_group_with_type(
        vec![
            runtime.generate_internal_binder_name(),
            runtime.generate_internal_binder_name(),
        ],
        ParamType::Obj(chain),
    )?;
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

    Ok(ForallFact::new_canonical_forall(
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
    upper_bound_prop_name: AtomicName,
    line_file: LineFile,
) -> Result<ExistFactEnum, RuntimeError> {
    let u_group = runtime.fresh_param_group_with_type(
        vec![runtime.generate_internal_binder_name()],
        ParamType::Obj(set),
    )?;
    let u = obj_for_bound_param_in_scope(&u_group.params[0], ParamObjType::Exist);
    let named_upper_bound =
        normal_prop_fact(upper_bound_prop_name, vec![chain, u], line_file.clone());
    let body = ExistFactBody::new(
        ParamDefWithType::new(vec![u_group]),
        vec![ExistBodyFact::AtomicFact(named_upper_bound)],
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
    let x_group = runtime.fresh_param_group_with_type(
        vec![runtime.generate_internal_binder_name()],
        ParamType::Obj(chain),
    )?;
    let x = obj_for_bound_param_in_scope(&x_group.params[0], ParamObjType::Forall);
    ForallFact::new_canonical_forall(
        ParamDefWithType::new(vec![x_group]),
        vec![],
        vec![normal_prop_fact(prop_name, vec![x, upper], line_file.clone()).into()],
        line_file,
    )
}

fn zorn_lemma_maximal_fact(
    runtime: &Runtime,
    set: Obj,
    maximal_prop_name: AtomicName,
    line_file: LineFile,
) -> Result<Fact, RuntimeError> {
    let m_group = runtime.fresh_param_group_with_type(
        vec![runtime.generate_internal_binder_name()],
        ParamType::Obj(set),
    )?;
    let m = obj_for_bound_param_in_scope(&m_group.params[0], ParamObjType::Exist);
    let named_maximal = normal_prop_fact(maximal_prop_name, vec![m], line_file.clone());
    let body = ExistFactBody::new(
        ParamDefWithType::new(vec![m_group]),
        vec![ExistBodyFact::AtomicFact(named_maximal)],
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
    let x_group = runtime.fresh_param_group_with_type(
        vec![runtime.generate_internal_binder_name()],
        ParamType::Obj(set),
    )?;
    let x = obj_for_bound_param_in_scope(&x_group.params[0], ParamObjType::Forall);
    ForallFact::new_canonical_forall(
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
