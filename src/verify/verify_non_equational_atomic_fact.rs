use crate::prelude::*;

impl Runtime {
    pub fn verify_non_equational_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
        post_process: bool,
    ) -> Result<StmtResult, RuntimeError> {
        let mut result =
            self.verify_non_equational_atomic_fact_with_builtin_rules(atomic_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(atomic_fact)?;
        if result.is_true() {
            return Ok(result);
        }

        if verify_state.is_round_0() {
            let verify_state_add_one_round = verify_state.new_state_with_round_increased();

            if let Some(verified_by_definition) =
                self.verify_atomic_fact_using_builtin_or_prop_definition(atomic_fact, verify_state)?
            {
                return Ok(verified_by_definition);
            }

            result = self
                .verify_atomic_fact_with_known_forall(atomic_fact, &verify_state_add_one_round)?;
            if result.is_true() {
                return Ok(result);
            }
        }

        if post_process {
            result =
                self.post_process_non_equational_atomic_fact(atomic_fact, verify_state, result)?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok((StmtUnknown::new()).into())
    }

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
        let mut all_objs_equal_to_arg =
            self.get_all_objs_equal_to_given(&atomic_fact.args()[0].to_string());

        if let Some(calculated_obj) = self.resolve_obj_to_number(&atomic_fact.args()[0]) {
            if calculated_obj.to_string() != atomic_fact.args()[0].to_string() {
                let equal_tos = self.get_all_objs_equal_to_given(&calculated_obj.to_string());
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
        let mut all_objs_equal_to_arg0 =
            self.get_all_objs_equal_to_given(&atomic_fact.args()[0].to_string());
        if let Some(calculated_obj) = self.resolve_obj_to_number(&atomic_fact.args()[0]) {
            if calculated_obj.to_string() != atomic_fact.args()[0].to_string() {
                let equal_tos = self.get_all_objs_equal_to_given(&calculated_obj.to_string());
                all_objs_equal_to_arg0.extend(equal_tos);
            }
        }
        if all_objs_equal_to_arg0.is_empty() {
            all_objs_equal_to_arg0.push(atomic_fact.args()[0].to_string());
        }
        let mut all_objs_equal_to_arg1 =
            self.get_all_objs_equal_to_given(&atomic_fact.args()[1].to_string());
        if let Some(calculated_obj) = self.resolve_obj_to_number(&atomic_fact.args()[1]) {
            if calculated_obj.to_string() != atomic_fact.args()[1].to_string() {
                let equal_tos = self.get_all_objs_equal_to_given(&calculated_obj.to_string());
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
        let mut all_objs_equal_to_each_arg: Vec<Vec<String>> = Vec::new();
        for arg in atomic_fact.args().iter() {
            let mut all_objs_equal_to_current_arg =
                self.get_all_objs_equal_to_given(&arg.to_string());
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
                    return Ok((FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
                            atomic_fact.clone().into(),
                            known_atomic_fact.to_string(),
                            Some(known_atomic_fact.clone().into()),
                            None,
                            Vec::new(),
                        )).into());
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
                        return Ok((FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
                                atomic_fact.clone().into(),
                                known_atomic_fact.to_string(),
                                Some(known_atomic_fact.clone().into()),
                                None,
                                Vec::new(),
                            )).into());
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
                            return Ok((FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
                                    atomic_fact.clone().into(),
                                    known_atomic_fact.to_string(),
                                    Some(known_atomic_fact.clone().into()),
                                    None,
                                    Vec::new(),
                                )).into());
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
                Some(UnknownRuntimeError(RuntimeErrorStruct::new(
                Some(Fact::from(atomic_fact.clone()).into_stmt()),
                message,
                atomic_fact.line_file(),
                None,
                vec![],
            ))
            .into()),
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
                    return Ok((FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
                            atomic_fact.clone().into(),
                            known_fact.to_string(),
                            Some(known_fact.clone().into()),
                            None,
                            Vec::new(),
                        )).into());
                }
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub fn verify_fact(
        &mut self,
        fact: &Fact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
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

    fn verify_subset_fact_by_membership_forall_definition(
        &mut self,
        subset_fact: &SubsetFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let bound_param_name = self.generate_random_unused_name();
        let membership_forall_fact = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![bound_param_name.clone()],
                ParamType::Obj(subset_fact.left.clone()),
            )]),
            vec![],
            vec![InFact::new(
                bound_param_name.into(),
                subset_fact.right.clone(),
                subset_fact.line_file.clone(),
            )
            .into()],
            subset_fact.line_file.clone(),
        )
        .into();
        let verify_forall_result = self.verify_fact(&membership_forall_fact, verify_state)?;
        if !verify_forall_result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                subset_fact.clone().into(),
                "subset by definition (forall x in left: x in right)".to_string(),
                Vec::new(),
            ))
            .into(),
        ))
    }

    fn verify_superset_fact_by_membership_forall_definition(
        &mut self,
        superset_fact: &SupersetFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let bound_param_name = self.generate_random_unused_name();
        let membership_forall_fact = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![bound_param_name.clone()],
                ParamType::Obj(superset_fact.right.clone()),
            )]),
            vec![],
            vec![InFact::new(
                bound_param_name.into(),
                superset_fact.left.clone(),
                superset_fact.line_file.clone(),
            )
            .into()],
            superset_fact.line_file.clone(),
        )
        .into();
        let verify_forall_result = self.verify_fact(&membership_forall_fact, verify_state)?;
        if !verify_forall_result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                superset_fact.clone().into(),
                "superset by definition (forall x in right: x in left)".to_string(),
                Vec::new(),
            ))
            .into(),
        ))
    }

    // Built-in subset/superset/restrict definitions first, then user `prop` iff-clauses.
    fn verify_atomic_fact_using_builtin_or_prop_definition(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(result) =
            self.verify_builtin_fact_with_their_definition(atomic_fact, verify_state)?
        {
            return Ok(Some(result));
        }
        if let AtomicFact::NormalAtomicFact(n) = atomic_fact {
            return self.verify_normal_atomic_fact_using_its_definition(n, verify_state);
        }
        Ok(None)
    }

    fn verify_normal_atomic_fact_using_its_definition(
        &mut self,
        normal_atomic_fact: &NormalAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(_) =
            self.get_abstract_prop_definition_by_name(&normal_atomic_fact.predicate.to_string())
        {
            return Ok(None);
        }

        let predicate_name = normal_atomic_fact.predicate.to_string();

        let definition = match self.get_prop_definition_by_name(&predicate_name) {
            Some(definition_reference) => definition_reference.clone(),
            None => {
                return Err(
                    {
                        VerifyRuntimeError(RuntimeErrorStruct::new(
                Some(Fact::from(normal_atomic_fact.clone()).into_stmt()),
                format!("prop definition not found for {}", predicate_name),
                normal_atomic_fact.line_file.clone(),
                None,
                vec![],
            ))
            .into()
        },
                )
            }
        };

        let verify_state_for_definition_clauses = verify_state;

        let args_param_types = match self.verify_args_satisfy_param_def_flat_types(
            &definition.params_def_with_type,
            &normal_atomic_fact.body,
            verify_state_for_definition_clauses,
            (FreeParamObjType::Def, FreeParamObjType::Def),
        ) {
            Ok(x) => x,
            Err(_) => {
                return Err(
                    {
                        VerifyRuntimeError(RuntimeErrorStruct::new(
                Some(Fact::from(normal_atomic_fact.clone()).into_stmt()),
                format!("failed to verify parameter types for {}", predicate_name),
                normal_atomic_fact.line_file.clone(),
                None,
                vec![],
            ))
            .into()
        },
                )
            }
        };
        if args_param_types.is_unknown() {
            return Ok(None);
        }

        if definition.iff_facts.is_empty() {
            return Ok(None);
        }

        let param_to_arg_map = definition
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(normal_atomic_fact.body.as_slice());

        let mut infer_result = InferResult::new();
        let mut definition_clause_descriptions: Vec<String> = Vec::new();

        for iff_fact in definition.iff_facts.iter() {
            let instantiated_iff_fact = self
                .inst_fact(iff_fact, &param_to_arg_map, (FreeParamObjType::Def, FreeParamObjType::Def))
                .map_err(|e| {
                    {
                        RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                Some(Fact::from(normal_atomic_fact.clone()).into_stmt()),
                String::new(),
                normal_atomic_fact.line_file.clone(),
                Some(e),
                vec![],
            )))
        }
                })?
                .with_new_line_file(normal_atomic_fact.line_file.clone());
            let iff_clause_verify_result =
                self.verify_fact(&instantiated_iff_fact, &verify_state_for_definition_clauses)?;
            if iff_clause_verify_result.is_unknown() {
                return Ok(None);
            }
            match &iff_clause_verify_result {
                StmtResult::FactualStmtSuccess(factual_success) => {
                    infer_result.new_infer_result_inside(factual_success.infers.clone());
                    definition_clause_descriptions.push(factual_success.msg.clone());
                }
                StmtResult::NonFactualStmtSuccess(non_factual_success) => {
                    infer_result.new_infer_result_inside(non_factual_success.infers.clone());
                }
                StmtResult::StmtUnknown(_) => return Ok(None),
            }
        }

        let verified_by_text = format!(
            "prop with meaning `{}` (param constraints and definition clauses): {}",
            predicate_name,
            definition_clause_descriptions.join("; ")
        );
        infer_result.new_fact(&normal_atomic_fact.clone().into());
        Ok(Some(
            (FactualStmtSuccess::new_with_verified_by_known_fact_source(
                normal_atomic_fact.clone().into(),
                infer_result,
                verified_by_text,
                None,
                Some(normal_atomic_fact.line_file.clone()),
                Vec::new(),
            ))
            .into(),
        ))
    }

    fn verify_builtin_fact_with_their_definition(
        &mut self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        match fact {
            AtomicFact::SubsetFact(subset_fact) => {
                if let Some(verified_by_subset_definition) = self
                    .verify_subset_fact_by_membership_forall_definition(subset_fact, verify_state)?
                {
                    return Ok(Some(verified_by_subset_definition));
                }
                return Ok(None);
            }
            AtomicFact::SupersetFact(superset_fact) => {
                if let Some(verified_by_superset_definition) = self
                    .verify_superset_fact_by_membership_forall_definition(
                        superset_fact,
                        verify_state,
                    )?
                {
                    return Ok(Some(verified_by_superset_definition));
                }
                return Ok(None);
            }
            AtomicFact::RestrictFact(restrict_fact) => {
                if let Some(verified_by_restrict_definition) =
                    self.verify_restrict_fact_using_its_definition(restrict_fact, verify_state)?
                {
                    return Ok(Some(verified_by_restrict_definition));
                }
                return Ok(None);
            }
            _ => {}
        }
        Ok(None)
    }

    // If direct verification failed, try the order-dual with swapped operands (e.g. a >= b via b <= a).
    fn post_process_non_equational_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
        result: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        let Some(transposed_fact) = atomic_fact.transposed_binary_order_equivalent() else {
            return Ok(result);
        };
        let transposed_result =
            self.verify_non_equational_atomic_fact(&transposed_fact, verify_state, false)?;
        match transposed_result {
            StmtResult::FactualStmtSuccess(inner_success) => Ok(
                (FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
                    atomic_fact.clone().into(),
                    inner_success.msg,
                    inner_success.verified_by_fact,
                    inner_success.verified_by_fact_known_line_file,
                    inner_success.inside_results,
                ))
                .into(),
            ),
            other if other.is_true() => Ok(other),
            _ => Ok(result),
        }
    }
}
