use super::*;

impl Runtime {
    // Family-union introduction: `x $in cup(F)` follows from a member set
    // containing `x`, either as a known existential or as concrete facts.
    // Example: `A $in F` and `x $in A` prove `x $in cup(F)`.
    pub(super) fn verify_in_fact_in_cup_by_member_witness(
        &mut self,
        in_fact: &InFact,
        cup: &Cup,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let exist_fact = self.cup_membership_exist_fact(in_fact, cup)?;
        let exist_result =
            self.verify_exist_fact_with_known_exist_fact(&exist_fact, &exist_fact)?;
        if exist_result.is_true() {
            return Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "cup membership: an element of a member set is in the family union".to_string(),
                    vec![exist_result],
                )
                .into(),
            );
        }

        for member_set in self.known_member_sets_for_cup_family(in_fact, cup.left.as_ref()) {
            let member_set_in_family: AtomicFact = InFact::new(
                member_set.clone(),
                cup.left.as_ref().clone(),
                in_fact.line_file.clone(),
            )
            .into();
            let member_set_result = self.verify_non_equational_known_then_builtin_rules_only(
                &member_set_in_family,
                verify_state,
            )?;
            if !member_set_result.is_true() {
                continue;
            }

            let element_in_member_set: AtomicFact = InFact::new(
                in_fact.element.clone(),
                member_set,
                in_fact.line_file.clone(),
            )
            .into();
            let element_result = self.verify_non_equational_known_then_builtin_rules_only(
                &element_in_member_set,
                verify_state,
            )?;
            if element_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        in_fact.clone().into(),
                        "cup membership: an element of a member set is in the family union"
                            .to_string(),
                        vec![member_set_result, element_result],
                    )
                    .into(),
                );
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub(super) fn cup_membership_exist_fact(
        &self,
        in_fact: &InFact,
        cup: &Cup,
    ) -> Result<ExistFactEnum, RuntimeError> {
        let member_name = "item".to_string();
        let member_obj = obj_for_bound_param_in_scope(member_name.clone(), ParamObjType::Exist);
        let element_in_member: AtomicFact = InFact::new(
            in_fact.element.clone(),
            member_obj,
            in_fact.line_file.clone(),
        )
        .into();
        let exist_body = ExistFactBody::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![member_name],
                ParamType::Obj(cup.left.as_ref().clone()),
            )]),
            vec![element_in_member.into()],
            in_fact.line_file.clone(),
        )?;
        Ok(ExistFactEnum::ExistFact(exist_body))
    }

    // Replacement introduction: `z $in replacement(P, A)` follows from a
    // relation witness in the source set.
    // Example: `x $in A` and `$P(x, z)` prove `z $in replacement(P, A)`.
    pub(super) fn verify_in_fact_in_replacement_by_relation_witness(
        &mut self,
        in_fact: &InFact,
        replacement: &Replacement,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let exist_fact = self.replacement_membership_exist_fact(in_fact, replacement)?;
        let exist_result =
            self.verify_exist_fact_with_known_exist_fact(&exist_fact, &exist_fact)?;
        if exist_result.is_true() {
            return Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "replacement membership: a relation witness is in the replacement set"
                        .to_string(),
                    vec![exist_result],
                )
                .into(),
            );
        }

        for preimage in self.known_preimages_for_replacement_target(in_fact, replacement) {
            let preimage_in_source: AtomicFact = InFact::new(
                preimage.clone(),
                replacement.source_set.as_ref().clone(),
                in_fact.line_file.clone(),
            )
            .into();
            let preimage_result = self.verify_non_equational_known_then_builtin_rules_only(
                &preimage_in_source,
                verify_state,
            )?;
            if !preimage_result.is_true() {
                continue;
            }

            let relation_fact: AtomicFact = NormalAtomicFact::new(
                replacement.prop_name.clone(),
                vec![preimage, in_fact.element.clone()],
                in_fact.line_file.clone(),
            )
            .into();
            let relation_result = self.verify_non_equational_known_then_builtin_rules_only(
                &relation_fact,
                verify_state,
            )?;
            if relation_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        in_fact.clone().into(),
                        "replacement membership: a relation witness is in the replacement set"
                            .to_string(),
                        vec![preimage_result, relation_result],
                    )
                    .into(),
                );
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub(super) fn replacement_membership_exist_fact(
        &self,
        in_fact: &InFact,
        replacement: &Replacement,
    ) -> Result<ExistFactEnum, RuntimeError> {
        let preimage_name = "x".to_string();
        let preimage_obj = obj_for_bound_param_in_scope(preimage_name.clone(), ParamObjType::Exist);
        let relation_fact: AtomicFact = NormalAtomicFact::new(
            replacement.prop_name.clone(),
            vec![preimage_obj, in_fact.element.clone()],
            in_fact.line_file.clone(),
        )
        .into();
        let exist_body = ExistFactBody::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![preimage_name],
                ParamType::Obj(replacement.source_set.as_ref().clone()),
            )]),
            vec![relation_fact.into()],
            in_fact.line_file.clone(),
        )?;
        Ok(ExistFactEnum::ExistFact(exist_body))
    }

    pub(super) fn known_preimages_for_replacement_target(
        &self,
        in_fact: &InFact,
        replacement: &Replacement,
    ) -> Vec<Obj> {
        let atomic_fact: AtomicFact = in_fact.clone().into();
        let module_names = self.atomic_fact_referenced_module_names(&atomic_fact);
        let target_keys =
            self.all_objs_equal_to_arg_for_known_atomic_fact(&in_fact.element, &module_names);
        let lookup_key = (replacement.prop_name.to_string(), true);
        let mut candidates = Vec::new();
        for environment in self.iter_environments_from_top() {
            Self::extend_known_preimages_for_replacement_target_from_environment(
                environment,
                &lookup_key,
                &target_keys,
                &mut candidates,
            );
        }
        for module_name in module_names.iter() {
            for environment in self.imported_module_environments(module_name) {
                Self::extend_known_preimages_for_replacement_target_from_environment(
                    environment,
                    &lookup_key,
                    &target_keys,
                    &mut candidates,
                );
            }
        }

        let mut seen = Vec::new();
        candidates.retain(|candidate: &Obj| {
            let key = candidate.to_string();
            if seen.contains(&key) {
                return false;
            }
            seen.push(key);
            true
        });
        candidates
    }

    pub(super) fn extend_known_preimages_for_replacement_target_from_environment(
        environment: &Environment,
        lookup_key: &(String, bool),
        target_keys: &[String],
        candidates: &mut Vec<Obj>,
    ) {
        let Some(known_relation_facts) = environment.known_atomic_facts_with_2_args.get(lookup_key)
        else {
            return;
        };
        for ((_, known_target_key), known_fact) in known_relation_facts.iter() {
            if !target_keys.contains(known_target_key) {
                continue;
            }
            let AtomicFact::NormalAtomicFact(known_relation) = known_fact else {
                continue;
            };
            let Some(preimage) = known_relation.body.first() else {
                continue;
            };
            candidates.push(preimage.clone());
        }
    }

    pub(super) fn known_member_sets_for_cup_family(
        &self,
        in_fact: &InFact,
        family: &Obj,
    ) -> Vec<Obj> {
        let atomic_fact: AtomicFact = in_fact.clone().into();
        let module_names = self.atomic_fact_referenced_module_names(&atomic_fact);
        let family_keys = self.all_objs_equal_to_arg_for_known_atomic_fact(family, &module_names);
        let mut candidates = Vec::new();
        for environment in self.iter_environments_from_top() {
            Self::extend_known_member_sets_for_cup_family_from_environment(
                environment,
                &family_keys,
                &mut candidates,
            );
        }
        for module_name in module_names.iter() {
            for environment in self.imported_module_environments(module_name) {
                Self::extend_known_member_sets_for_cup_family_from_environment(
                    environment,
                    &family_keys,
                    &mut candidates,
                );
            }
        }

        let mut seen = Vec::new();
        candidates.retain(|candidate: &Obj| {
            let key = candidate.to_string();
            if seen.contains(&key) {
                return false;
            }
            seen.push(key);
            true
        });
        candidates
    }

    pub(super) fn extend_known_member_sets_for_cup_family_from_environment(
        environment: &Environment,
        family_keys: &[String],
        candidates: &mut Vec<Obj>,
    ) {
        let lookup_key = (IN.to_string(), true);
        let Some(known_membership_facts) =
            environment.known_atomic_facts_with_2_args.get(&lookup_key)
        else {
            return;
        };
        for ((_, known_family_key), known_fact) in known_membership_facts.iter() {
            if !family_keys.contains(known_family_key) {
                continue;
            }
            let AtomicFact::InFact(known_in_fact) = known_fact else {
                continue;
            };
            candidates.push(known_in_fact.element.clone());
        }
    }

    // Function range introduction: if `f(a)` is well-defined, then it is in `fn_range(f)`.
    // Example: `have f fn(x R: x > 0) R`, `1 > 0` proves `f(1) $in fn_range(f)`.
    pub(super) fn verify_in_fact_fn_application_in_fn_range(
        &mut self,
        in_fact: &InFact,
        fn_obj: &FnObj,
        fn_range: &FnRange,
    ) -> Result<StmtResult, RuntimeError> {
        let head_obj: Obj = fn_obj.head.as_ref().clone().into();
        if head_obj.to_string() != fn_range.function.to_string() {
            return Ok((StmtUnknown::new()).into());
        }
        let Some(body) = self.get_fn_range_function_body(&fn_range.function) else {
            return Ok((StmtUnknown::new()).into());
        };
        if fn_obj.body.len() != 1
            || fn_obj.body[0].len() != body.params_def_with_set.number_of_params()
        {
            return Ok((StmtUnknown::new()).into());
        }
        if self
            .verify_obj_well_defined_and_store_cache(&in_fact.element, &VerifyState::new(0, false))
            .is_err()
        {
            return Ok((StmtUnknown::new()).into());
        }
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "fn_range membership: a well-defined function application is in the function range"
                    .to_string(),
                Vec::new(),
            )
            .into(),
        )
    }

    // The range of `f : ... -> T` is a subset of `T`; hence it is in `power_set(U)` when `T subset U`.
    // Example: `have f fn(x S) T` proves `fn_range(f) $in power_set(T)`.
    pub(super) fn verify_in_fact_fn_range_in_power_set(
        &mut self,
        in_fact: &InFact,
        fn_range: &FnRange,
        power_set: &PowerSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let Some(body) = self.get_fn_range_function_body(&fn_range.function) else {
            return Ok((StmtUnknown::new()).into());
        };
        let subset_fact: AtomicFact = SubsetFact::new(
            body.ret_set.as_ref().clone(),
            power_set.set.as_ref().clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let subset_result =
            self.verify_non_equational_known_then_builtin_rules_only(&subset_fact, verify_state)?;
        if !subset_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "fn_range power_set membership: function range is contained in the codomain"
                    .to_string(),
                vec![subset_result],
            )
            .into(),
        )
    }

    // Proves power-set membership from the subset definition.
    // Example: if `A $subset B`, then `A $in power_set(B)`.
    pub(super) fn verify_in_fact_in_power_set_via_subset(
        &mut self,
        in_fact: &InFact,
        power_set: &PowerSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let subset_fact: AtomicFact = SubsetFact::new(
            in_fact.element.clone(),
            power_set.set.as_ref().clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let subset_result =
            self.verify_non_equational_known_then_builtin_rules_only(&subset_fact, verify_state)?;
        if !subset_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "power_set membership: a subset of the base set is an element of the power set"
                    .to_string(),
                vec![subset_result],
            )
            .into(),
        )
    }

    // General Cartesian product membership: a member is a function on `I` into `cup(s)`
    // whose value at every index lies in the indexed factor.
    // Example: `f $in general_cart(I, s, g)` follows from
    // `f $in fn(t I)cup(s)` and `forall! t I => {f(t) $in g(t)}`.
    pub(super) fn verify_in_fact_in_general_cart_by_defining_facts(
        &mut self,
        in_fact: &InFact,
        general_cart: &GeneralCart,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let fn_set_fact: AtomicFact = InFact::new(
            in_fact.element.clone(),
            general_cart_member_fn_set(general_cart)?,
            in_fact.line_file.clone(),
        )
        .into();
        let fn_set_result =
            self.verify_non_equational_known_then_builtin_rules_only(&fn_set_fact, verify_state)?;
        if !fn_set_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        let Some(pointwise_fact) =
            general_cart_member_pointwise_fact(general_cart, &in_fact.element, &in_fact.line_file)?
        else {
            return Ok((StmtUnknown::new()).into());
        };
        let pointwise_result = self.verify_fact_full(&pointwise_fact, verify_state)?;
        if !pointwise_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            in_fact.clone().into(),
            "general_cart membership: function into cup(family) with pointwise factor membership"
                .to_string(),
            vec![fn_set_result, pointwise_result],
        )
        .into())
    }

    pub(super) fn verify_in_fact_in_set_builder_by_defining_facts(
        &mut self,
        in_fact: &InFact,
        set_builder: &SetBuilder,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let mut step_results = Vec::with_capacity(set_builder.facts.len() + 1);

        let element_in_param_set: AtomicFact = InFact::new(
            in_fact.element.clone(),
            *set_builder.param_set.clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let element_in_param_set_result = self.verify_atomic_fact_by_known_atomic_or_builtin_only(
            &element_in_param_set,
            verify_state,
        )?;
        if !element_in_param_set_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        step_results.push(element_in_param_set_result);

        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        param_to_arg_map.insert(set_builder.param.clone(), in_fact.element.clone());

        for fact_in_set_builder in set_builder.facts.iter() {
            let instantiated_fact = self
                .inst_exist_body_fact(
                    fact_in_set_builder,
                    &param_to_arg_map,
                    ParamObjType::SetBuilder,
                    Some(&in_fact.line_file),
                )
                .map_err(|e| {
                    let fact: Fact = in_fact.clone().into();
                    RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(fact.into_stmt()),
                        format!(
                            "failed to instantiate set builder fact while verifying `{}`",
                            in_fact
                        ),
                        in_fact.line_file.clone(),
                        Some(e),
                        vec![],
                    )))
                })?;

            let instantiated_fact_result =
                self.verify_fact_full(&instantiated_fact.to_fact(), verify_state)?;
            if !instantiated_fact_result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
            step_results.push(instantiated_fact_result);
        }

        Ok(FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            in_fact.clone().into(),
            "set builder membership: element is in the base set and satisfies all defining facts"
                .to_string(),
            step_results,
        )
        .into())
    }

    // Membership through a set-valued definition: if `S(a) = {x T: P(x)}`,
    // then `y $in S(a)` is checked by unfolding one layer and proving
    // `y $in T` plus `P(y)`. Example: `(3, 4) $in circle(5)`.
    pub(super) fn maybe_verify_in_fact_in_unfolded_user_defined_set(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(unfolded_set) =
            self.unfold_known_fn_application_once(&in_fact.set, verify_state)?
        else {
            return Ok(None);
        };
        let Obj::SetBuilder(set_builder) = unfolded_set else {
            return Ok(None);
        };

        let unfolded_fact = InFact::new(
            in_fact.element.clone(),
            set_builder.clone().into(),
            in_fact.line_file.clone(),
        );
        let unfolded_result = self.verify_in_fact_in_set_builder_by_defining_facts(
            &unfolded_fact,
            &set_builder,
            verify_state,
        )?;
        if !unfolded_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "membership in a set-valued user-defined function: unfold one function application to a set builder".to_string(),
                vec![unfolded_result],
            )
            .into(),
        ))
    }

    pub(super) fn verify_in_fact_by_struct_obj(
        &mut self,
        in_fact: &InFact,
        struct_obj: &StructObj,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(
            &Obj::StructObj(struct_obj.clone()),
            verify_state,
        )?;
        let (def, header_map) = self.struct_header_param_to_arg_map(struct_obj, verify_state)?;
        let field_types = self.instantiated_struct_field_types(struct_obj, verify_state)?;
        let cart_obj: Obj = Cart::new(field_types).into();
        let cart_membership: AtomicFact =
            InFact::new(in_fact.element.clone(), cart_obj, in_fact.line_file.clone()).into();
        let cart_result = self
            .verify_atomic_fact_by_known_atomic_or_builtin_only(&cart_membership, verify_state)?;
        if !cart_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        let mut step_results = vec![cart_result];
        let mut field_map = HashMap::new();
        for (index, (field_name, _)) in def.fields.iter().enumerate() {
            let field_obj = match &in_fact.element {
                Obj::Tuple(tuple) => (*tuple.args[index]).clone(),
                _ => ObjAtIndex::new(
                    in_fact.element.clone(),
                    Number::new((index + 1).to_string()).into(),
                )
                .into(),
            };
            field_map.insert(field_name.clone(), field_obj);
        }

        for fact in def.equivalent_facts.iter() {
            let after_header = self.inst_fact(
                fact,
                &header_map,
                ParamObjType::DefHeader,
                Some(in_fact.line_file.clone()),
            )?;
            let instantiated_fact = self.inst_fact(
                &after_header,
                &field_map,
                ParamObjType::DefStructField,
                Some(in_fact.line_file.clone()),
            )?;
            // A structure's equivalent facts are its membership obligations. They
            // may be universal laws, such as associativity, so use the ordinary
            // verifier rather than the restricted atomic builtin path.
            let fact_result = self.verify_fact_full(&instantiated_fact, verify_state)?;
            if !fact_result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
            step_results.push(fact_result);
        }

        Ok(FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            in_fact.clone().into(),
            "struct membership: element is in the named cart base and satisfies struct equivalent facts".to_string(),
            step_results,
        )
        .into())
    }

    // The cardinality of a finite set is a natural number, hence also an integer, rational, and real.
    // Example: if `A finite_set`, then `finite_set_size(A) $in N` and `finite_set_size(A) $in R`.
    pub(super) fn verify_finite_set_size_in_standard_number_set(
        &mut self,
        in_fact: &InFact,
        finite_set_size: &FiniteSetSize,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let finite_fact =
            IsFiniteSetFact::new((*finite_set_size.set).clone(), in_fact.line_file.clone());
        let finite_result = self.verify_non_equational_known_then_builtin_rules_only(
            &finite_fact.into(),
            verify_state,
        )?;
        if finite_result.is_true() {
            return Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "finite_set_size of a finite set is a natural number",
            ));
        }
        Ok((StmtUnknown::new()).into())
    }
}
