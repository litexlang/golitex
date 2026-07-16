use crate::prelude::*;
use std::collections::HashMap;
use std::result::Result;

fn real_line_comparison_exist_fact_non_witness_operands(
    exist_fact: &ExistFactEnum,
) -> Option<Vec<&Obj>> {
    if !exist_fact.is_plain_exist() || exist_fact.facts().len() != 1 {
        return None;
    }

    let param_names = exist_fact.params_def_with_type().collect_param_names();
    if !(param_names.len() == 1 || param_names.len() == 2) {
        return None;
    }
    if !exist_fact
        .params_def_with_type()
        .groups
        .iter()
        .all(|group| {
            matches!(
                &group.param_type,
                ParamType::Obj(Obj::StandardSet(StandardSet::R))
            )
        })
    {
        return None;
    }

    let ExistBodyFact::AtomicFact(atomic_fact) = &exist_fact.facts()[0] else {
        return None;
    };
    let (left, right) = match atomic_fact {
        AtomicFact::EqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::LessFact(fact) => (&fact.left, &fact.right),
        AtomicFact::GreaterFact(fact) => (&fact.left, &fact.right),
        AtomicFact::LessEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::GreaterEqualFact(fact) => (&fact.left, &fact.right),
        _ => return None,
    };

    let direct_exist_param_name = |obj: &Obj| match obj {
        Obj::Atom(AtomObj::Exist(param)) => Some(param.name.clone()),
        _ => None,
    };

    if param_names.len() == 1 {
        let witness_name = &param_names[0];
        let other = if direct_exist_param_name(left).as_deref() == Some(witness_name.as_str()) {
            right
        } else if direct_exist_param_name(right).as_deref() == Some(witness_name.as_str()) {
            left
        } else {
            return None;
        };
        if Runtime::obj_depends_on_given_exist_param(other, param_names.as_slice()) {
            return None;
        }
        return Some(vec![other]);
    } else {
        let (Some(left_name), Some(right_name)) = (
            direct_exist_param_name(left),
            direct_exist_param_name(right),
        ) else {
            return None;
        };
        if left_name == right_name
            || !param_names.iter().any(|name| name == &left_name)
            || !param_names.iter().any(|name| name == &right_name)
        {
            return None;
        }
    }

    Some(vec![])
}

fn rational_integer_ratio_exist_fact_non_witness_operand(
    exist_fact: &ExistFactEnum,
) -> Option<&Obj> {
    if !exist_fact.is_plain_exist() || exist_fact.facts().len() != 1 {
        return None;
    }

    let params = exist_fact
        .params_def_with_type()
        .collect_param_names_with_types();
    if params.len() != 2 {
        return None;
    }
    let (numerator_name, numerator_type) = &params[0];
    let (denominator_name, denominator_type) = &params[1];
    if !matches!(
        numerator_type,
        ParamType::Obj(Obj::StandardSet(StandardSet::Z))
    ) || !matches!(
        denominator_type,
        ParamType::Obj(Obj::StandardSet(StandardSet::ZNz))
    ) {
        return None;
    }

    let ExistBodyFact::AtomicFact(AtomicFact::EqualFact(equal_fact)) = &exist_fact.facts()[0]
    else {
        return None;
    };

    let is_selected_ratio = |obj: &Obj| match obj {
        Obj::Div(div) => {
            matches!(
                div.left.as_ref(),
                Obj::Atom(AtomObj::Exist(param)) if param.name.as_str() == numerator_name.as_str()
            ) && matches!(
                div.right.as_ref(),
                Obj::Atom(AtomObj::Exist(param)) if param.name.as_str() == denominator_name.as_str()
            )
        }
        _ => false,
    };

    let other = if is_selected_ratio(&equal_fact.left) {
        &equal_fact.right
    } else if is_selected_ratio(&equal_fact.right) {
        &equal_fact.left
    } else {
        return None;
    };
    if Runtime::obj_depends_on_given_exist_param(
        other,
        &[numerator_name.clone(), denominator_name.clone()],
    ) {
        return None;
    }
    Some(other)
}

impl Runtime {
    pub fn verify_exist_fact(
        &mut self,
        exist_fact: &ExistFactEnum,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&exist_fact.clone().into())
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_exist_fact_well_defined(exist_fact, verify_state) {
                return Err({
                    VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(exist_fact.clone()).into_stmt()),
                        String::new(),
                        exist_fact.line_file(),
                        Some(e),
                        vec![],
                    ))
                    .into()
                });
            }
        }

        // The real line has witnesses above, below, equal to, and distinct from every real.
        // Example: `have x R:` followed by `x > 100`.
        if let Some(non_witness_operands) =
            real_line_comparison_exist_fact_non_witness_operands(exist_fact)
        {
            if let Some(steps) = self.verify_objects_are_known_reals(
                non_witness_operands.as_slice(),
                &exist_fact.line_file(),
                verify_state,
            )? {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        exist_fact.clone().into(),
                        "exist: real-line comparison witness".to_string(),
                        steps,
                    )
                    .into(),
                );
            }
        }

        // Every rational is represented by an integer numerator and a nonzero
        // integer denominator. Example: `exist a Z, b Z_nz st {q = a / b}`
        // for `q Q`.
        if let Some(rational) = rational_integer_ratio_exist_fact_non_witness_operand(exist_fact) {
            let in_q: AtomicFact = InFact::new(
                rational.clone(),
                StandardSet::Q.into(),
                exist_fact.line_file(),
            )
            .into();
            let rational_membership =
                self.verify_non_equational_known_then_builtin_rules_only(&in_q, verify_state)?;
            if rational_membership.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        exist_fact.clone().into(),
                        "exist: rational integer ratio representation".to_string(),
                        vec![rational_membership],
                    )
                    .into(),
                );
            }
        }

        let result = self.verify_exist_fact_with_known_exist_fact(exist_fact, exist_fact)?;
        if result.is_true() {
            return Ok(result);
        }

        if verify_state.is_round_0() {
            let result = self.verify_exist_fact_with_known_forall(exist_fact, verify_state)?;
            if result.is_true() {
                return Ok(result);
            }

            if exist_fact.is_exist_unique() {
                if let Some(proved) = self.try_verify_exist_unique_by_exist_and_uniqueness_forall(
                    exist_fact,
                    verify_state,
                )? {
                    return Ok(proved);
                }
            }
        }

        Ok(StmtUnknown::new().into())
    }

    pub(crate) fn build_exist_unique_uniqueness_forall_fact(
        &self,
        exist_fact: &ExistFactEnum,
    ) -> Result<ForallFact, RuntimeError> {
        self.build_exist_unique_uniqueness_forall_fact_inner(exist_fact, false)
    }

    pub(crate) fn build_exist_unique_component_uniqueness_forall_fact(
        &self,
        exist_fact: &ExistFactEnum,
    ) -> Result<ForallFact, RuntimeError> {
        self.build_exist_unique_uniqueness_forall_fact_inner(exist_fact, true)
    }

    fn build_exist_unique_uniqueness_forall_fact_inner(
        &self,
        exist_fact: &ExistFactEnum,
        component_conclusion: bool,
    ) -> Result<ForallFact, RuntimeError> {
        let lf = exist_fact.line_file();
        let flat_orig = exist_fact.params_def_with_type().collect_param_names();
        let n = flat_orig.len();
        let flat_a: Vec<String> = flat_orig.iter().map(|name| format!("{}1", name)).collect();
        let flat_b: Vec<String> = flat_orig.iter().map(|name| format!("{}2", name)).collect();

        let mut map_running_a: HashMap<String, Obj> = HashMap::new();
        let mut map_running_b: HashMap<String, Obj> = HashMap::new();
        let mut forall_groups: Vec<ParamGroupWithParamType> = Vec::new();
        for group in exist_fact.params_def_with_type().groups.iter() {
            let chunk_a: Vec<String> = group
                .params
                .iter()
                .map(|name| format!("{}1", name))
                .collect();
            for (orig, nm) in group.params.iter().zip(chunk_a.iter()) {
                map_running_a.insert(
                    orig.clone(),
                    obj_for_bound_param_in_scope(nm.clone(), ParamObjType::Forall),
                );
            }
            let pt_a =
                self.inst_param_type(&group.param_type, &map_running_a, ParamObjType::Forall)?;
            forall_groups.push(ParamGroupWithParamType::new(chunk_a, pt_a));
        }
        for group in exist_fact.params_def_with_type().groups.iter() {
            let chunk_b: Vec<String> = group
                .params
                .iter()
                .map(|name| format!("{}2", name))
                .collect();
            for (orig, nm) in group.params.iter().zip(chunk_b.iter()) {
                map_running_b.insert(
                    orig.clone(),
                    obj_for_bound_param_in_scope(nm.clone(), ParamObjType::Forall),
                );
            }
            let pt_b =
                self.inst_param_type(&group.param_type, &map_running_b, ParamObjType::Forall)?;
            forall_groups.push(ParamGroupWithParamType::new(chunk_b, pt_b));
        }

        let map_a: HashMap<String, Obj> = flat_orig
            .iter()
            .cloned()
            .zip(
                flat_a
                    .iter()
                    .cloned()
                    .map(|s| obj_for_bound_param_in_scope(s, ParamObjType::Forall)),
            )
            .collect();
        let map_b: HashMap<String, Obj> = flat_orig
            .iter()
            .cloned()
            .zip(
                flat_b
                    .iter()
                    .cloned()
                    .map(|s| obj_for_bound_param_in_scope(s, ParamObjType::Forall)),
            )
            .collect();

        // Witness parameters in `exist_fact.facts` are [`ExistFreeParamObj`]; only `inst_*` with
        // [`ParamObjType::Exist`] substitutes them from `map_a` / `map_b` into the forall copies.
        let mut dom_facts: Vec<Fact> = Vec::new();
        for inner in exist_fact.facts().iter() {
            let f_a = self.inst_exist_body_fact(inner, &map_a, ParamObjType::Exist, None)?;
            dom_facts.push(f_a.to_fact());
        }
        for inner in exist_fact.facts().iter() {
            let f_b = self.inst_exist_body_fact(inner, &map_b, ParamObjType::Exist, None)?;
            dom_facts.push(f_b.to_fact());
        }

        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        if n == 1 {
            let eq = EqualFact::new(
                obj_for_bound_param_in_scope(flat_a[0].clone(), ParamObjType::Forall),
                obj_for_bound_param_in_scope(flat_b[0].clone(), ParamObjType::Forall),
                lf.clone(),
            );
            then_facts.push(ExistOrAndChainAtomicFact::AtomicFact(eq.into()));
        } else if component_conclusion {
            let mut equal_facts: Vec<AtomicFact> = Vec::new();
            for (left_name, right_name) in flat_a.iter().zip(flat_b.iter()) {
                equal_facts.push(
                    EqualFact::new(
                        obj_for_bound_param_in_scope(left_name.clone(), ParamObjType::Forall),
                        obj_for_bound_param_in_scope(right_name.clone(), ParamObjType::Forall),
                        lf.clone(),
                    )
                    .into(),
                );
            }
            then_facts.push(AndFact::new(equal_facts, lf.clone()).into());
        } else {
            let left_tuple: Obj = Tuple::new(
                flat_a
                    .iter()
                    .cloned()
                    .map(|s| obj_for_bound_param_in_scope(s, ParamObjType::Forall))
                    .collect::<Vec<Obj>>(),
            )
            .into();
            let right_tuple: Obj = Tuple::new(
                flat_b
                    .iter()
                    .cloned()
                    .map(|s| obj_for_bound_param_in_scope(s, ParamObjType::Forall))
                    .collect::<Vec<Obj>>(),
            )
            .into();
            let eq = EqualFact::new(left_tuple, right_tuple, lf.clone());
            then_facts.push(ExistOrAndChainAtomicFact::AtomicFact(eq.into()));
        }

        let forall_fact = ForallFact::new(
            ParamDefWithType::new(forall_groups),
            dom_facts,
            then_facts,
            lf,
        )?;

        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        for group in forall_fact.params_def_with_type.groups.iter() {
            for param in group.params.iter() {
                param_to_arg_map
                    .insert(param.clone(), ForallFreeParamObj::new(param.clone()).into());
            }
        }

        let forall_fact = self.inst_fact(
            &forall_fact.into(),
            &param_to_arg_map,
            ParamObjType::Forall,
            None,
        )?;

        match forall_fact {
            Fact::ForallFact(x) => Ok(x.clone()),
            _ => {
                unreachable!();
            }
        }
    }

    fn try_verify_exist_unique_by_exist_and_uniqueness_forall(
        &mut self,
        exist_fact: &ExistFactEnum,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if exist_fact.params_def_with_type().number_of_params() == 0 {
            return Ok(None);
        }
        let plain = ExistFactEnum::ExistFact(ExistFactBody::new(
            exist_fact.params_def_with_type().clone(),
            exist_fact.facts().clone(),
            exist_fact.line_file(),
        )?);
        let wd_ok = verify_state.with_well_defined_already_verified();
        let plain_res = self.verify_exist_fact(&plain, &wd_ok)?;
        if !plain_res.is_true() {
            return Ok(None);
        }

        let uniqueness_forall = self.build_exist_unique_uniqueness_forall_fact(exist_fact)?;

        let uniqueness_fact: Fact = uniqueness_forall.clone().into();
        let uniq_res = self.verify_fact_full(&uniqueness_fact, &wd_ok)?;
        if !uniq_res.is_true() {
            return Ok(None);
        }

        let mut infers = InferResult::new();
        infers.new_fact(&exist_fact.clone().into());
        infers.new_infer_result_inside(stmt_result_infers(&plain_res));
        infers.new_infer_result_inside(stmt_result_infers(&uniq_res));
        infers.new_fact(&uniqueness_fact);

        let out = FactualStmtSuccess::new_with_verified_by_known_fact_and_infer(
            exist_fact.clone().into(),
            infers,
            VerifiedByResult::cited_fact(
                exist_fact.clone().into(),
                uniqueness_fact.clone(),
                Some("exist!: witness exist and uniqueness forall verified".to_string()),
            ),
            vec![],
        );
        Ok(Some(out.into()))
    }

    pub fn verify_exist_fact_with_known_exist_fact(
        &mut self,
        exist_fact: &ExistFactEnum,
        known_exist_fact: &ExistFactEnum,
    ) -> Result<StmtResult, RuntimeError> {
        for environment in self.iter_environments_from_top() {
            let result = Self::verify_exist_fact_with_known_exist_fact_with_facts_in_environment(
                self,
                environment,
                exist_fact,
                known_exist_fact,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub fn verify_exist_fact_with_known_exist_fact_with_facts_in_environment(
        runtime: &Runtime,
        environment: &Environment,
        exist_fact: &ExistFactEnum,
        known_exist_fact: &ExistFactEnum,
    ) -> Result<StmtResult, RuntimeError> {
        let goal_keys = Self::known_exist_lookup_keys(known_exist_fact);
        let target_body_string = Self::exist_fact_normalized_body_string(runtime, exist_fact)
            .map_err(|e| {
                RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                    Some(Fact::from(exist_fact.clone()).into_stmt()),
                    String::new(),
                    exist_fact.line_file(),
                    Some(e),
                    vec![],
                )))
            })?;
        for key in goal_keys.iter() {
            let Some(known_exist_facts) = environment.known_exist_facts.get(key) else {
                continue;
            };
            for known_fact in known_exist_facts.iter() {
                if !known_fact.can_be_used_to_verify_goal(exist_fact) {
                    continue;
                }
                let known_body_string =
                    Self::exist_fact_normalized_body_string(runtime, known_fact).map_err(|e| {
                        RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                            Some(Fact::from(exist_fact.clone()).into_stmt()),
                            String::new(),
                            exist_fact.line_file(),
                            Some(e),
                            vec![],
                        )))
                    })?;
                if target_body_string == known_body_string {
                    return Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
                        exist_fact.clone().into(),
                        VerifiedByResult::cited_fact(
                            exist_fact.clone().into(),
                            known_fact.clone().into(),
                            None,
                        ),
                        Vec::new(),
                    ))
                    .into());
                }
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    fn known_exist_lookup_keys(goal: &ExistFactEnum) -> Vec<String> {
        let mut keys = vec![goal.key()];
        if let ExistFactEnum::ExistFact(body) = goal {
            keys.push(ExistFactEnum::ExistUniqueFact(body.clone()).key());
        }
        keys.sort();
        keys.dedup();
        keys
    }

    fn exist_fact_normalized_body_string(
        runtime: &Runtime,
        exist_fact: &ExistFactEnum,
    ) -> Result<String, RuntimeError> {
        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        let mut normalized_params: Vec<ParamGroupWithParamType> = Vec::new();
        let mut param_index: usize = 0;

        for param_def_with_type in exist_fact.params_def_with_type().groups.iter() {
            let mut new_param_names: Vec<String> = Vec::new();
            for original_name in param_def_with_type.params.iter() {
                let normalized_name = format!("#{}", param_index);
                param_index += 1;

                param_to_arg_map.insert(
                    original_name.clone(),
                    obj_for_bound_param_in_scope(normalized_name.clone(), ParamObjType::Exist),
                );
                new_param_names.push(normalized_name);
            }

            let instantiated_param_type = runtime.inst_param_type(
                &param_def_with_type.param_type,
                &param_to_arg_map,
                ParamObjType::Exist,
            )?;
            normalized_params.push(ParamGroupWithParamType::new(
                new_param_names,
                instantiated_param_type,
            ));
        }

        let instantiated_exist_fact =
            runtime.inst_exist_fact(exist_fact, &param_to_arg_map, ParamObjType::Exist, None)?;

        let mut fact_strings: Vec<String> = Vec::new();
        for fact in instantiated_exist_fact.facts().iter() {
            let fact_as_fact = fact.from_ref_to_cloned_fact();
            fact_strings.push(fact_as_fact.to_string());
        }

        let mut params_string_parts: Vec<String> = Vec::new();
        for param_def_with_type in normalized_params.iter() {
            params_string_parts.push(format!(
                "{} {}",
                param_def_with_type.params.join(","),
                param_def_with_type.param_type
            ));
        }
        let params_string = params_string_parts.join("; ");
        let facts_string = fact_strings.join("; ");
        Ok(format!("{} || {}", params_string, facts_string))
    }
}

fn stmt_result_infers(result: &StmtResult) -> InferResult {
    result.infer_result()
}
