use crate::prelude::*;

impl Runtime {
    pub fn verify_non_equational_atomic_fact_with_known_atomic_facts(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let result = if atomic_fact.number_of_args() == 1 {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param(atomic_fact)?
        } else if atomic_fact.number_of_args() == 2 {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params(atomic_fact)?
        } else {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params(
                atomic_fact,
            )?
        };

        if result.is_true() {
            return Ok(result);
        }

        Ok(result)
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let module_names = self.atomic_fact_referenced_module_names(atomic_fact);
        let all_objs_equal_to_arg =
            self.all_objs_equal_to_arg_for_known_atomic_fact(&atomic_fact.args()[0], &module_names);

        for environment in self.iter_environments_from_top() {
            let result = Self::verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param_with_facts_in_environment(environment, atomic_fact, &all_objs_equal_to_arg)?;
            if result.is_true() {
                return Ok(result);
            }
        }
        for module_name in module_names.iter() {
            if let Some(environment) = self.active_imported_module_environment(module_name) {
                let result = Self::verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param_with_facts_in_environment(environment.as_ref(), atomic_fact, &all_objs_equal_to_arg)?;
                if result.is_true() {
                    return Ok(result);
                }
            }
        }

        let arg = atomic_fact.args()[0].clone();
        let arg_resolved = self.resolve_obj(&arg);
        if arg_resolved.to_string() != arg.to_string() {
            let rewritten =
                Self::atomic_fact_with_resolved_unary_operand(atomic_fact, arg_resolved);
            return self
                .verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param(&rewritten);
        }

        Ok((StmtUnknown::new()).into())
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let module_names = self.atomic_fact_referenced_module_names(atomic_fact);
        let all_objs_equal_to_arg0 =
            self.all_objs_equal_to_arg_for_known_atomic_fact(&atomic_fact.args()[0], &module_names);
        let all_objs_equal_to_arg1 =
            self.all_objs_equal_to_arg_for_known_atomic_fact(&atomic_fact.args()[1], &module_names);

        for environment in self.iter_environments_from_top() {
            let result = Self::verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params_with_facts_in_environment(environment, atomic_fact, &all_objs_equal_to_arg0, &all_objs_equal_to_arg1)?;
            if result.is_true() {
                return Ok(result);
            }
        }
        for module_name in module_names.iter() {
            if let Some(environment) = self.active_imported_module_environment(module_name) {
                let result = Self::verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params_with_facts_in_environment(environment.as_ref(), atomic_fact, &all_objs_equal_to_arg0, &all_objs_equal_to_arg1)?;
                if result.is_true() {
                    return Ok(result);
                }
            }
        }

        let left = atomic_fact.args()[0].clone();
        let right = atomic_fact.args()[1].clone();
        let left_resolved = self.resolve_obj(&left);
        let right_resolved = self.resolve_obj(&right);
        if left_resolved.to_string() != left.to_string()
            || right_resolved.to_string() != right.to_string()
        {
            let rewritten = Self::atomic_fact_with_resolved_binary_operands(
                atomic_fact,
                left_resolved,
                right_resolved,
            );
            return self
                .verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params(&rewritten);
        }

        Ok((StmtUnknown::new()).into())
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let module_names = self.atomic_fact_referenced_module_names(atomic_fact);
        let mut all_objs_equal_to_each_arg: Vec<Vec<String>> = Vec::new();
        for arg in atomic_fact.args().iter() {
            all_objs_equal_to_each_arg
                .push(self.all_objs_equal_to_arg_for_known_atomic_fact(arg, &module_names));
        }

        for environment in self.iter_environments_from_top() {
            let result = Self::verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params_with_facts_in_environment(
                environment,
                atomic_fact,
                &all_objs_equal_to_each_arg,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }
        for module_name in module_names.iter() {
            if let Some(environment) = self.active_imported_module_environment(module_name) {
                let result = Self::verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params_with_facts_in_environment(
                    environment.as_ref(),
                    atomic_fact,
                    &all_objs_equal_to_each_arg,
                )?;
                if result.is_true() {
                    return Ok(result);
                }
            }
        }

        let old_args = atomic_fact.args();
        let mut new_args: Vec<Obj> = Vec::with_capacity(old_args.len());
        let mut any_changed = false;
        for a in old_args.iter() {
            let r = self.resolve_obj(a);
            if r.to_string() != a.to_string() {
                any_changed = true;
            }
            new_args.push(r);
        }
        if any_changed {
            let rewritten = Self::atomic_fact_with_resolved_predicate_args(atomic_fact, new_args);
            return self
                .verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params(
                    &rewritten,
                );
        }

        Ok((StmtUnknown::new()).into())
    }

    fn all_objs_equal_to_arg_for_known_atomic_fact(
        &self,
        arg: &Obj,
        module_names: &[String],
    ) -> Vec<String> {
        let mut all_objs_equal_to_arg = vec![];
        self.extend_all_objs_equal_to_given_from_current_and_imported_envs(
            &mut all_objs_equal_to_arg,
            &arg.to_string(),
            module_names,
        );

        if let Some(calculated_obj) = self.resolve_obj_to_number(arg) {
            if calculated_obj.to_string() != arg.to_string() {
                self.extend_all_objs_equal_to_given_from_current_and_imported_envs(
                    &mut all_objs_equal_to_arg,
                    &calculated_obj.to_string(),
                    module_names,
                );
            }
        }

        if all_objs_equal_to_arg.is_empty() {
            all_objs_equal_to_arg.push(arg.to_string());
        }
        dedup_strings(&mut all_objs_equal_to_arg);
        all_objs_equal_to_arg
    }

    fn extend_all_objs_equal_to_given_from_current_and_imported_envs(
        &self,
        result: &mut Vec<String>,
        given: &str,
        module_names: &[String],
    ) {
        result.extend(self.get_all_objs_equal_to_given(given));
        for module_name in module_names.iter() {
            if let Some(environment) = self.active_imported_module_environment(module_name) {
                result.extend(Self::get_all_objs_equal_to_given_in_environment(
                    environment.as_ref(),
                    given,
                ));
            }
        }
    }

    fn atomic_fact_with_resolved_unary_operand(fact: &AtomicFact, x: Obj) -> AtomicFact {
        let line_file = fact.line_file();
        match fact {
            AtomicFact::IsSetFact(_) => IsSetFact::new(x, line_file).into(),
            AtomicFact::IsNonemptySetFact(_) => IsNonemptySetFact::new(x, line_file).into(),
            AtomicFact::IsFiniteSetFact(_) => IsFiniteSetFact::new(x, line_file).into(),
            AtomicFact::IsCartFact(_) => IsCartFact::new(x, line_file).into(),
            AtomicFact::IsTupleFact(_) => IsTupleFact::new(x, line_file).into(),
            AtomicFact::NotIsSetFact(_) => NotIsSetFact::new(x, line_file).into(),
            AtomicFact::NotIsNonemptySetFact(_) => NotIsNonemptySetFact::new(x, line_file).into(),
            AtomicFact::NotIsFiniteSetFact(_) => NotIsFiniteSetFact::new(x, line_file).into(),
            AtomicFact::NotIsCartFact(_) => NotIsCartFact::new(x, line_file).into(),
            AtomicFact::NotIsTupleFact(_) => NotIsTupleFact::new(x, line_file).into(),
            AtomicFact::NormalAtomicFact(n) => {
                NormalAtomicFact::new(n.predicate.clone(), vec![x], line_file).into()
            }
            AtomicFact::NotNormalAtomicFact(n) => {
                NotNormalAtomicFact::new(n.predicate.clone(), vec![x], line_file).into()
            }
            _ => unreachable!(
                "atomic_fact_with_resolved_unary_operand: expected a one-argument atomic fact"
            ),
        }
    }

    fn atomic_fact_with_resolved_binary_operands(
        fact: &AtomicFact,
        left: Obj,
        right: Obj,
    ) -> AtomicFact {
        let line_file = fact.line_file();
        match fact {
            AtomicFact::EqualFact(_) => EqualFact::new(left, right, line_file).into(),
            AtomicFact::LessFact(_) => LessFact::new(left, right, line_file).into(),
            AtomicFact::GreaterFact(_) => GreaterFact::new(left, right, line_file).into(),
            AtomicFact::LessEqualFact(_) => LessEqualFact::new(left, right, line_file).into(),
            AtomicFact::GreaterEqualFact(_) => GreaterEqualFact::new(left, right, line_file).into(),
            AtomicFact::InFact(_) => InFact::new(left, right, line_file).into(),
            AtomicFact::SubsetFact(_) => SubsetFact::new(left, right, line_file).into(),
            AtomicFact::SupersetFact(_) => SupersetFact::new(left, right, line_file).into(),
            AtomicFact::NotEqualFact(_) => NotEqualFact::new(left, right, line_file).into(),
            AtomicFact::NotLessFact(_) => NotLessFact::new(left, right, line_file).into(),
            AtomicFact::NotGreaterFact(_) => NotGreaterFact::new(left, right, line_file).into(),
            AtomicFact::NotLessEqualFact(_) => NotLessEqualFact::new(left, right, line_file).into(),
            AtomicFact::NotGreaterEqualFact(_) => {
                NotGreaterEqualFact::new(left, right, line_file).into()
            }
            AtomicFact::NotInFact(_) => NotInFact::new(left, right, line_file).into(),
            AtomicFact::NotSubsetFact(_) => NotSubsetFact::new(left, right, line_file).into(),
            AtomicFact::NotSupersetFact(_) => NotSupersetFact::new(left, right, line_file).into(),
            AtomicFact::RestrictFact(_) => RestrictFact::new(left, right, line_file).into(),
            AtomicFact::NotRestrictFact(_) => NotRestrictFact::new(left, right, line_file).into(),
            AtomicFact::NormalAtomicFact(x) => {
                NormalAtomicFact::new(x.predicate.clone(), vec![left, right], line_file).into()
            }
            AtomicFact::NotNormalAtomicFact(x) => {
                NotNormalAtomicFact::new(x.predicate.clone(), vec![left, right], line_file).into()
            }
            _ => unreachable!(
                "atomic_fact_with_resolved_binary_operands: expected a two-argument atomic fact"
            ),
        }
    }

    fn atomic_fact_with_resolved_predicate_args(fact: &AtomicFact, args: Vec<Obj>) -> AtomicFact {
        let line_file = fact.line_file();
        match fact {
            AtomicFact::NormalAtomicFact(x) => {
                NormalAtomicFact::new(x.predicate.clone(), args, line_file).into()
            }
            AtomicFact::NotNormalAtomicFact(x) => {
                NotNormalAtomicFact::new(x.predicate.clone(), args, line_file).into()
            }
            _ => unreachable!(
                "atomic_fact_with_resolved_predicate_args: expected NormalAtomicFact or NotNormalAtomicFact"
            ),
        }
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param_with_facts_in_environment(
        environment: &Environment,
        atomic_fact: &AtomicFact,
        all_objs_equal_to_arg: &Vec<String>,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(known_facts_map) = environment
            .known_atomic_facts_with_1_arg
            .get(&(atomic_fact.key(), atomic_fact.is_true()))
        {
            for obj in all_objs_equal_to_arg.iter() {
                if let Some(known_atomic_fact) = known_facts_map.get(obj) {
                    return Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
                        atomic_fact.clone().into(),
                        VerifiedByResult::cited_fact(
                            atomic_fact.clone().into(),
                            known_atomic_fact.clone().into(),
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

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params_with_facts_in_environment(
        environment: &Environment,
        atomic_fact: &AtomicFact,
        all_objs_equal_to_arg0: &Vec<String>,
        all_objs_equal_to_arg1: &Vec<String>,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(known_facts_map) = environment
            .known_atomic_facts_with_2_args
            .get(&(atomic_fact.key(), atomic_fact.is_true()))
        {
            for obj0 in all_objs_equal_to_arg0.iter() {
                for obj1 in all_objs_equal_to_arg1.iter() {
                    if let Some(known_atomic_fact) =
                        known_facts_map.get(&(obj0.clone(), obj1.clone()))
                    {
                        return Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
                            atomic_fact.clone().into(),
                            VerifiedByResult::cited_fact(
                                atomic_fact.clone().into(),
                                known_atomic_fact.clone().into(),
                                None,
                            ),
                            Vec::new(),
                        ))
                        .into());
                    }
                }
            }
        }

        // Order facts are stored under `<` vs `>` etc.; e.g. known `a > 0` must match goal `0 < a`.
        if let Some(alt) = atomic_fact.transposed_binary_order_equivalent() {
            if let Some(known_facts_map) = environment
                .known_atomic_facts_with_2_args
                .get(&(alt.key(), alt.is_true()))
            {
                for obj0 in all_objs_equal_to_arg1.iter() {
                    for obj1 in all_objs_equal_to_arg0.iter() {
                        if let Some(known_atomic_fact) =
                            known_facts_map.get(&(obj0.clone(), obj1.clone()))
                        {
                            return Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
                                atomic_fact.clone().into(),
                                VerifiedByResult::cited_fact(
                                    atomic_fact.clone().into(),
                                    known_atomic_fact.clone().into(),
                                    None,
                                ),
                                Vec::new(),
                            ))
                            .into());
                        }
                    }
                }
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params_with_facts_in_environment(
        environment: &Environment,
        atomic_fact: &AtomicFact,
        all_objs_equal_to_each_arg: &Vec<Vec<String>>,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(known_facts) = environment
            .known_atomic_facts_with_0_or_more_than_2_args
            .get(&(atomic_fact.key(), atomic_fact.is_true()))
        {
            for known_fact in known_facts.iter() {
                if known_fact.args().len() != atomic_fact.args().len() {
                    let message = format!(
                        "known atomic fact {} has different number of args than the given fact {}",
                        known_fact.to_string(),
                        atomic_fact.to_string()
                    );
                    return Err({
                        VerifyRuntimeError(RuntimeErrorStruct::new(
                            Some(Fact::from(atomic_fact.clone()).into_stmt()),
                            message.clone(),
                            atomic_fact.line_file(),
                            Some(
                                UnknownRuntimeError(RuntimeErrorStruct::new(
                                    Some(Fact::from(atomic_fact.clone()).into_stmt()),
                                    message,
                                    atomic_fact.line_file(),
                                    None,
                                    vec![],
                                ))
                                .into(),
                            ),
                            vec![],
                        ))
                        .into()
                    });
                }
                let mut all_args_match = true;
                for (index, known_arg) in known_fact.args().iter().enumerate() {
                    let known_arg_string = known_arg.to_string();
                    if !all_objs_equal_to_each_arg[index].contains(&known_arg_string) {
                        all_args_match = false;
                        break;
                    }
                }
                if all_args_match {
                    return Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
                        atomic_fact.clone().into(),
                        VerifiedByResult::cited_fact(
                            atomic_fact.clone().into(),
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
}

fn dedup_strings(values: &mut Vec<String>) {
    let mut deduped = Vec::with_capacity(values.len());
    for value in values.drain(..) {
        if !deduped.iter().any(|existing| existing == &value) {
            deduped.push(value);
        }
    }
    *values = deduped;
}
