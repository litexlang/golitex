use crate::prelude::*;

impl Runtime {
    pub fn verify_non_equational_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let mut result =
            self.verify_non_equational_atomic_fact_with_builtin_rules(atomic_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
            atomic_fact,
        )?;
        if result.is_true() {
            return Ok(result);
        }

        if verify_state.is_round_0() {
            let verify_state_add_one_round = verify_state.new_state_with_round_increased();

            if let AtomicFact::NormalAtomicFact(normal_atomic_fact) = atomic_fact {
                let maybe_verified_by_prop_definition = self
                    .verify_normal_atomic_fact_using_its_definition(
                        normal_atomic_fact,
                        verify_state,
                    )?;
                if let Some(verified_by_definition) = maybe_verified_by_prop_definition {
                    return Ok(verified_by_definition);
                }
            }

            result = self
                .verify_atomic_fact_with_known_forall(atomic_fact, &verify_state_add_one_round)?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    pub fn verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if atomic_fact.number_of_args() == 1 {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param(atomic_fact)
        } else if atomic_fact.number_of_args() == 2 {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params(atomic_fact)
        } else {
            self
                .verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params(atomic_fact)
        }
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let mut all_objs_equal_to_arg =
            self.get_all_objs_equal_to_arg(&atomic_fact.args()[0].to_string());

        // 得到它的 calculated obj
        if let Some(calculated_obj) = self.resolve_obj_to_number(&atomic_fact.args()[0]) {
            if calculated_obj.to_string() != atomic_fact.args()[0].to_string() {
                let equal_tos = self.get_all_objs_equal_to_arg(&calculated_obj.to_string());
                all_objs_equal_to_arg.extend(equal_tos);
            }
        }

        if all_objs_equal_to_arg.is_empty() {
            all_objs_equal_to_arg.push(atomic_fact.args()[0].to_string());
        }

        for environment in self.iter_environments_from_top() {
            let result = Self::verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param_with_facts_in_environment(environment, atomic_fact, &all_objs_equal_to_arg)?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let mut all_objs_equal_to_arg0 =
            self.get_all_objs_equal_to_arg(&atomic_fact.args()[0].to_string());
        if let Some(calculated_obj) = self.resolve_obj_to_number(&atomic_fact.args()[0]) {
            if calculated_obj.to_string() != atomic_fact.args()[0].to_string() {
                let equal_tos = self.get_all_objs_equal_to_arg(&calculated_obj.to_string());
                all_objs_equal_to_arg0.extend(equal_tos);
            }
        }
        if all_objs_equal_to_arg0.is_empty() {
            all_objs_equal_to_arg0.push(atomic_fact.args()[0].to_string());
        }
        let mut all_objs_equal_to_arg1 =
            self.get_all_objs_equal_to_arg(&atomic_fact.args()[1].to_string());
        if let Some(calculated_obj) = self.resolve_obj_to_number(&atomic_fact.args()[1]) {
            if calculated_obj.to_string() != atomic_fact.args()[1].to_string() {
                let equal_tos = self.get_all_objs_equal_to_arg(&calculated_obj.to_string());
                all_objs_equal_to_arg1.extend(equal_tos);
            }
        }
        if all_objs_equal_to_arg1.is_empty() {
            all_objs_equal_to_arg1.push(atomic_fact.args()[1].to_string());
        }

        for environment in self.iter_environments_from_top() {
            let result = Self::verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params_with_facts_in_environment(environment, atomic_fact, &all_objs_equal_to_arg0, &all_objs_equal_to_arg1)?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let mut all_objs_equal_to_each_arg: Vec<Vec<String>> = Vec::new();
        for arg in atomic_fact.args().iter() {
            let mut all_objs_equal_to_current_arg =
                self.get_all_objs_equal_to_arg(&arg.to_string());
            if all_objs_equal_to_current_arg.is_empty() {
                all_objs_equal_to_current_arg.push(arg.to_string());
            }
            all_objs_equal_to_each_arg.push(all_objs_equal_to_current_arg);
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

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param_with_facts_in_environment(
        environment: &Environment,
        atomic_fact: &AtomicFact,
        all_objs_equal_to_arg: &Vec<String>,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(known_facts_map) = environment
            .known_atomic_facts_with_1_arg
            .get(&(atomic_fact.key(), atomic_fact.is_true()))
        {
            for obj in all_objs_equal_to_arg.iter() {
                if let Some(known_atomic_fact) = known_facts_map.get(obj) {
                    return Ok(NonErrStmtExecResult::FactVerifiedByFact(
                        FactVerifiedByFact::new(
                            Fact::AtomicFact(atomic_fact.clone()),
                            known_atomic_fact.to_string(),
                            InferResult::new(),
                            known_atomic_fact.line_file(),
                        ),
                    ));
                }
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params_with_facts_in_environment(
        environment: &Environment,
        atomic_fact: &AtomicFact,
        all_objs_equal_to_arg0: &Vec<String>,
        all_objs_equal_to_arg1: &Vec<String>,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(known_facts_map) = environment
            .known_atomic_facts_with_2_args
            .get(&(atomic_fact.key(), atomic_fact.is_true()))
        {
            for obj0 in all_objs_equal_to_arg0.iter() {
                for obj1 in all_objs_equal_to_arg1.iter() {
                    if let Some(known_atomic_fact) =
                        known_facts_map.get(&(obj0.clone(), obj1.clone()))
                    {
                        return Ok(NonErrStmtExecResult::FactVerifiedByFact(
                            FactVerifiedByFact::new(
                                Fact::AtomicFact(atomic_fact.clone()),
                                known_atomic_fact.to_string(),
                                InferResult::new(),
                                known_atomic_fact.line_file(),
                            ),
                        ));
                    }
                }
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params_with_facts_in_environment(
        environment: &Environment,
        atomic_fact: &AtomicFact,
        all_objs_equal_to_each_arg: &Vec<Vec<String>>,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
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
                    return Err(VerifyError::new(
                        Fact::AtomicFact(atomic_fact.clone()),
                        message.clone(),
                        atomic_fact.line_file(),
                        Some(RuntimeError::UnknownError(UnknownError::new(
                            message,
                            atomic_fact.line_file(),
                            Some(Fact::AtomicFact(atomic_fact.clone())),
                            None,
                        ))),
                    ));
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
                    return Ok(NonErrStmtExecResult::FactVerifiedByFact(
                        FactVerifiedByFact::new(
                            Fact::AtomicFact(atomic_fact.clone()),
                            known_fact.to_string(),
                            InferResult::new(),
                            known_fact.line_file(),
                        ),
                    ));
                }
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    pub fn verify_restrict_fact_with_builtin_rules(
        &mut self,
        restrict_fact: &RestrictFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        _ = restrict_fact;
        _ = verify_state;
        return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
    }

    fn verify_fact(
        &mut self,
        fact: &Fact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.verify_atomic_fact(atomic_fact, verify_state),
            Fact::AndFact(and_fact) => self.verify_and_fact(and_fact, verify_state),
            Fact::ChainFact(chain_fact) => self.verify_chain_fact(chain_fact, verify_state),
            Fact::ForallFact(forall_fact) => self.verify_forall_fact(forall_fact, verify_state),
            Fact::ForallFactWithIff(forall_iff) => {
                self.verify_forall_fact_with_iff(forall_iff, verify_state)
            }
            Fact::ExistFact(exist_fact) => self.verify_exist_fact(exist_fact, verify_state),
            Fact::OrFact(or_fact) => self.verify_or_fact(or_fact, verify_state),
        }
    }

    fn verify_normal_atomic_fact_using_its_definition(
        &mut self,
        normal_atomic_fact: &NormalAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<NonErrStmtExecResult>, VerifyError> {
        let predicate_name = normal_atomic_fact.predicate.to_string();
        let definition = match self.get_predicate_with_meaning_definition_by_name(&predicate_name) {
            Some(definition_reference) => definition_reference.clone(),
            None => return Ok(None),
        };

        let param_constraint_atomic_facts =
            match ParamDefWithParamType::facts_for_args_satisfy_param_def_with_type_vec(
                &definition.params_def_with_type,
                &normal_atomic_fact.body,
            ) {
                Ok(atomic_facts) => atomic_facts,
                Err(_) => return Ok(None),
            };

        let verify_state_for_definition_clauses = verify_state;

        for param_constraint_atomic_fact in param_constraint_atomic_facts.iter() {
            let param_constraint_verify_result = self.verify_atomic_fact(
                param_constraint_atomic_fact,
                &verify_state_for_definition_clauses,
            )?;
            if !param_constraint_verify_result.is_true() {
                return Ok(None);
            }
        }

        if definition.iff_facts.is_empty() {
            return Ok(None);
        }

        let param_to_arg_map = ParamDefWithParamType::param_defs_and_args_to_param_to_arg_map(
            &definition.params_def_with_type,
            &normal_atomic_fact.body,
        );

        let mut infer_result = InferResult::new();
        let mut definition_clause_descriptions: Vec<String> = Vec::new();

        for iff_fact in definition.iff_facts.iter() {
            let instantiated_iff_fact = iff_fact
                .instantiate(&param_to_arg_map)
                .with_new_line_file(normal_atomic_fact.line_file);
            let iff_clause_verify_result =
                self.verify_fact(&instantiated_iff_fact, &verify_state_for_definition_clauses)?;
            if iff_clause_verify_result.is_unknown() {
                return Ok(None);
            }
            match &iff_clause_verify_result {
                NonErrStmtExecResult::FactVerifiedByFact(fact_verified_by_fact) => {
                    infer_result.new_infer_result_inside(fact_verified_by_fact.infers.clone());
                    definition_clause_descriptions.push(fact_verified_by_fact.verified_by.clone());
                }
                NonErrStmtExecResult::FactVerifiedByBuiltinRules(fact_verified_by_builtin) => {
                    infer_result.new_infer_result_inside(fact_verified_by_builtin.infers.clone());
                    definition_clause_descriptions
                        .push(fact_verified_by_builtin.verified_by.clone());
                }
                NonErrStmtExecResult::NonFactualStmtSuccess(non_factual_success) => {
                    infer_result.new_infer_result_inside(non_factual_success.infers.clone());
                }
                NonErrStmtExecResult::StmtUnknown(_) => return Ok(None),
            }
        }

        let verified_by_text = format!(
            "prop with meaning `{}` (param constraints and definition clauses): {}",
            predicate_name,
            definition_clause_descriptions.join("; ")
        );
        Ok(Some(NonErrStmtExecResult::FactVerifiedByFact(
            FactVerifiedByFact::new(
                Fact::AtomicFact(AtomicFact::NormalAtomicFact(normal_atomic_fact.clone())),
                verified_by_text,
                infer_result,
                normal_atomic_fact.line_file,
            ),
        )))
    }
}
