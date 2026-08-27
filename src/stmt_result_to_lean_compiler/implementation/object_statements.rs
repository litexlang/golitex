use super::*;

impl StmtResultToLeanCompiler {
    pub(super) fn compile_have_obj_in_nonempty_set_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveObjInNonemptySetStmtResult,
    ) -> Result<(), String> {
        let verification = result.verification.as_ref().ok_or_else(|| {
            "object choice has no structured nonemptiness-to-membership result".to_string()
        })?;
        let parameter_groups = &result.statement.param_def.groups;
        if parameter_groups.len() != verification.groups.len() {
            return Err("object choice changed its parameter-group mapping".into());
        }
        let expected_choice_count = parameter_groups
            .iter()
            .map(|group| group.params.len())
            .sum::<usize>();
        if result.common.infers.store_fact_outputs.len() != expected_choice_count {
            return Err("object choice store count does not match its selected objects".into());
        }

        for (parameter_group, verified_group) in
            parameter_groups.iter().zip(verification.groups.iter())
        {
            let carrier = parameter_set(&parameter_group.param_type)?;
            if parameter_group.params.len() != verified_group.selected_type_facts.len() {
                return Err("object choice changed its binding-to-membership mapping".into());
            }
            let nonempty_check = verified_group.nonempty_check.as_deref().ok_or_else(|| {
                "object-carrier choice retained no nonemptiness proof".to_string()
            })?;
            let nonempty_proof = compile_standard_set_nonempty_fact_proof_from_result(
                nonempty_check,
                carrier,
                &self.environment_stack,
            )?;
            let rendered_carrier = render_obj(carrier, &self.environment_stack)?;

            for (binding, selected_type_fact) in parameter_group
                .params
                .iter()
                .zip(verified_group.selected_type_facts.iter())
            {
                let source_name = binding.name();
                let lean_name = lean_identifier(source_name);
                let defined_object: Obj =
                    Identifier::new_bound(source_name.to_string(), binding.as_ref()).into();
                let expected_membership: Fact = InFact::new(
                    defined_object,
                    carrier.clone(),
                    result.statement.line_file.clone(),
                )
                .into();
                if selected_type_fact.to_string() != expected_membership.to_string() {
                    return Err(format!(
                        "object choice changed selected membership `{selected_type_fact}`"
                    ));
                }
                let matching_stores = result
                    .common
                    .infers
                    .store_fact_outputs
                    .iter()
                    .filter(|store| {
                        store.itself_and_why_itself_is_stored.0.to_string()
                            == selected_type_fact.to_string()
                    })
                    .collect::<Vec<_>>();
                let [store] = matching_stores.as_slice() else {
                    return Err(
                        "object choice membership does not have exactly one store effect".into(),
                    );
                };
                let fact_id = store
                    .fact_id
                    .ok_or_else(|| "object choice membership has no FactId".to_string())?;
                if self
                    .environment_stack
                    .symbol_names
                    .insert(binding.id(), lean_name.clone())
                    .is_some()
                {
                    return Err(format!(
                        "duplicate compiler symbol identity for `{source_name}`"
                    ));
                }
                self.declarations.push(format!(
                    "noncomputable def {lean_name} : {rendered_carrier}.Carrier :=\n  Classical.choice ({nonempty_proof})"
                ));

                let proposition = render_fact(selected_type_fact, &self.environment_stack)?;
                let theorem_name = format!("__fact{}", self.next_fact_name_index);
                self.declarations.push(format!(
                    "theorem {theorem_name} : {proposition} := by\n  exact Litex.In.own {rendered_carrier} {lean_name}"
                ));
                self.environment_stack
                    .fact_names
                    .insert(fact_id, theorem_name);
                self.environment_stack
                    .fact_propositions
                    .insert(fact_id, selected_type_fact.clone());
                self.next_fact_name_index += 1;

                if matches!(carrier, Obj::StandardSet(StandardSet::N)) {
                    self.compile_natural_membership_infer_result(
                        selected_type_fact,
                        fact_id,
                        &result.common.infers,
                    )?;
                } else if store.inferred_facts.is_empty() && store.inferred_fact_ids.is_empty() {
                    // No child inference layer is expected for the other
                    // currently supported object carriers.
                } else {
                    return Err(format!(
                        "object choice for `{carrier}` retained unsupported inferred consequences"
                    ));
                }
            }
        }
        Ok(())
    }

    pub(super) fn compile_have_obj_equal_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveObjEqualStmtResult,
    ) -> Result<(), String> {
        let verification = result.verification.as_ref().ok_or_else(|| {
            "have-object equality has no structured value type-check results".to_string()
        })?;
        let bindings_with_types = result
            .statement
            .param_def
            .collect_param_bindings_with_types();
        if bindings_with_types.len() != result.statement.objs_equal_to.len()
            || bindings_with_types.len() != verification.type_checks.len()
        {
            return Err(
                "have-object equality changed its binding, value, or type-check count".into(),
            );
        }
        if result
            .common
            .infers
            .store_fact_outputs
            .iter()
            .any(|output| !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty())
        {
            return Err("have-object equality retained unsupported inferred consequences".into());
        }

        let mut expected_stored_facts = Vec::with_capacity(bindings_with_types.len() * 2);
        for ((binding, param_type), value) in bindings_with_types
            .iter()
            .zip(result.statement.objs_equal_to.iter())
        {
            let defined_object: Obj =
                Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into();
            expected_stored_facts.push(object_type_fact_for_compiler_definition(
                defined_object.clone(),
                param_type,
                result.statement.line_file.clone(),
            ));
            expected_stored_facts.push(
                EqualFact::new(
                    defined_object,
                    value.clone(),
                    result.statement.line_file.clone(),
                )
                .into(),
            );
        }
        let stored_fact_ids = exact_ordered_fact_ids_from_store_results(
            &result.common.infers,
            &expected_stored_facts,
            "have-object equality",
        )?;

        for (index, ((binding, param_type), value)) in bindings_with_types
            .iter()
            .zip(result.statement.objs_equal_to.iter())
            .enumerate()
        {
            let expected_value_type = object_type_fact_for_compiler_definition(
                value.clone(),
                param_type,
                result.statement.line_file.clone(),
            );
            let type_check = verification.type_checks[index]
                .factual_success()
                .ok_or_else(|| {
                    format!(
                        "have-object value `{}` has no successful type-check child Result",
                        binding.name()
                    )
                })?;
            if type_check.fact().to_string() != expected_value_type.to_string() {
                return Err(format!(
                    "have-object value type-check changed `{expected_value_type}` to `{}`",
                    type_check.fact()
                ));
            }

            let lean_name = lean_identifier(binding.name());
            if matches!(param_type, ParamType::Set(_)) {
                let lowered_value = LeanTargetObjectRepresentation::lower(value)?;
                let rendered_value =
                    render_set_definition_value(&lowered_value, &self.environment_stack)?;
                if self
                    .environment_stack
                    .symbol_names
                    .insert(binding.id(), lean_name.clone())
                    .is_some()
                {
                    return Err(format!(
                        "duplicate compiler symbol identity for `{}`",
                        binding.name()
                    ));
                }
                self.declarations.push(format!(
                    "abbrev {lean_name} : Litex.Set := {rendered_value}"
                ));

                // A set alias is a real Result layer, not only a target-side
                // abbreviation. Publish both frozen store identities so a
                // recursive child may cite the set classification or the
                // defining equality from the current compiler environment.
                let stored_type_fact = expected_stored_facts[index * 2].clone();
                let stored_equality = expected_stored_facts[index * 2 + 1].clone();
                let stored_type_fact_id = stored_fact_ids[index * 2];
                let stored_equality_fact_id = stored_fact_ids[index * 2 + 1];
                let rendered_type_fact = render_fact(&stored_type_fact, &self.environment_stack)?;
                let rendered_equality = render_fact(&stored_equality, &self.environment_stack)?;

                let type_theorem_name = format!("__fact{}", self.next_fact_name_index);
                self.declarations.push(format!(
                    "theorem {type_theorem_name} : {rendered_type_fact} := by\n  exact True.intro"
                ));
                self.environment_stack
                    .fact_names
                    .insert(stored_type_fact_id, type_theorem_name);
                self.environment_stack
                    .fact_propositions
                    .insert(stored_type_fact_id, stored_type_fact);
                self.next_fact_name_index += 1;

                let equality_theorem_name = format!("__fact{}", self.next_fact_name_index);
                self.declarations.push(format!(
                    "theorem {equality_theorem_name} : {rendered_equality} := by\n  exact Litex.Same.refl {rendered_value}"
                ));
                self.environment_stack
                    .fact_names
                    .insert(stored_equality_fact_id, equality_theorem_name);
                self.environment_stack
                    .fact_propositions
                    .insert(stored_equality_fact_id, stored_equality);
                self.next_fact_name_index += 1;
                continue;
            }

            let ParamType::Obj(_) = param_type else {
                return Err(format!(
                    "have-object `{}` has an unsupported non-membership type",
                    binding.name()
                ));
            };
            if bindings_with_types.len() != 1 {
                return Err(
                    "native have-object definitions currently require exactly one object".into(),
                );
            }
            let lowered_value = LeanTargetObjectRepresentation::lower(value)?;
            let rendered_value = render_lean_source_for_native_target_object_representation(
                &lowered_value,
                &self.environment_stack,
            )?;
            if self
                .environment_stack
                .symbol_names
                .insert(binding.id(), lean_name.clone())
                .is_some()
            {
                return Err(format!(
                    "duplicate compiler symbol identity for `{}`",
                    binding.name()
                ));
            }
            self.declarations
                .push(format!("noncomputable def {lean_name} := {rendered_value}"));

            let type_check_proof = self.construct_lean_proof_from_fact_result_without_storing(
                &verification.type_checks[index],
                &expected_value_type,
                "have-object type check",
            )?;
            let stored_type_fact = expected_stored_facts[index * 2].clone();
            let stored_equality = expected_stored_facts[index * 2 + 1].clone();
            let stored_type_fact_id = stored_fact_ids[index * 2];
            let stored_equality_fact_id = stored_fact_ids[index * 2 + 1];
            let rendered_type_fact = render_fact(&stored_type_fact, &self.environment_stack)?;
            let rendered_equality = render_fact(&stored_equality, &self.environment_stack)?;

            let type_theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {type_theorem_name} : {rendered_type_fact} := by\n  unfold {lean_name}\n  exact {type_check_proof}"
            ));
            self.environment_stack
                .fact_names
                .insert(stored_type_fact_id, type_theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(stored_type_fact_id, stored_type_fact);
            self.next_fact_name_index += 1;

            let equality_theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {equality_theorem_name} : {rendered_equality} := by\n  unfold {lean_name}\n  exact Litex.Same.refl {rendered_value}"
            ));
            self.environment_stack
                .fact_names
                .insert(stored_equality_fact_id, equality_theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(stored_equality_fact_id, stored_equality);
            self.environment_stack
                .runtime_resolved_numeric_substitutions
                .insert(binding.substitution_key(), value.clone());
            self.environment_stack
                .runtime_resolved_numeric_definition_names
                .push(lean_name);
            self.next_fact_name_index += 1;
        }
        Ok(())
    }

    /// `Combine`: a named function Result first enters the anonymous
    /// function's binder environment, installs the exact temporary FactIds
    /// retained by `assumption_infers`, consumes the recursive return-check
    /// Result there, and only then returns to the parent environment to
    /// publish the membership/equality FactIds.
    ///
    /// Native-real codomains render their body directly. Every other codomain
    /// uses the recursive return-check proof to select the exact carrier
    /// representative with `Litex.In.rep`; both routes are driven by the same
    /// child compiler environment.
    pub(super) fn compile_have_fn_equal_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveFnEqualStmtResult,
    ) -> Result<bool, String> {
        let verification = result.verification.as_ref().ok_or_else(|| {
            "named function has no structured body-to-environment verification Result".to_string()
        })?;
        let statement = &result.statement;
        let function_set = FnSet::from_body(statement.equal_to_anonymous_fn.body.clone())
            .map_err(|error| error.to_string())?;
        let function = LeanTargetFunctionTypeRepresentation::lower(&function_set)?;
        let source_body = statement.equal_to_anonymous_fn.equal_to.as_ref().clone();
        let lowered_body = LeanTargetObjectRepresentation::lower(&source_body)?;
        let source_return_set = statement
            .equal_to_anonymous_fn
            .body
            .ret_set
            .as_ref()
            .clone();
        let expected_return_check: Fact = InFact::new(
            source_body.clone(),
            source_return_set,
            statement.line_file.clone(),
        )
        .into();

        let mut expected_parameter_facts = Vec::new();
        for group in statement
            .equal_to_anonymous_fn
            .body
            .set_bound_parameters
            .iter()
        {
            expected_parameter_facts.extend(group.facts());
        }
        let expected_domain_facts = statement
            .equal_to_anonymous_fn
            .body
            .dom_facts
            .iter()
            .cloned()
            .map(Fact::from)
            .collect::<Vec<_>>();
        if expected_parameter_facts.len() != function.parameters.len()
            || expected_domain_facts.len() != function.domain_facts.len()
        {
            return Err("named real function changed its parameter/domain Result mapping".into());
        }
        if !verification.assumption_infers.rule_applications.is_empty()
            || verification
                .assumption_infers
                .store_fact_outputs
                .iter()
                .any(|output| {
                    !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty()
                })
        {
            return Ok(false);
        }
        let mut expected_assumptions = expected_parameter_facts.clone();
        expected_assumptions.extend(expected_domain_facts.iter().cloned());
        let assumption_fact_ids = exact_ordered_fact_ids_from_store_results(
            &verification.assumption_infers,
            &expected_assumptions,
            "named real function local assumptions",
        )?;
        let (parameter_fact_ids, domain_fact_ids) =
            assumption_fact_ids.split_at(expected_parameter_facts.len());

        let function_object: Obj = Identifier::new_bound(
            statement.name().to_string(),
            statement.symbol_binding.as_ref(),
        )
        .into();
        let expected_membership: Fact = InFact::new(
            function_object.clone(),
            function_set.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        let expected_defining_equality: Fact = EqualFact::new(
            function_object,
            statement.equal_to_anonymous_fn.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        if verification.function_membership.to_string() != expected_membership.to_string()
            || verification.defining_equality.to_string() != expected_defining_equality.to_string()
        {
            return Err(
                "named real function verification changed its outer membership/equality".into(),
            );
        }
        if !result.common.infers.rule_applications.is_empty()
            || result
                .common
                .infers
                .store_fact_outputs
                .iter()
                .any(|output| {
                    !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty()
                })
        {
            return Ok(false);
        }
        let stored_fact_ids = exact_ordered_fact_ids_from_store_results(
            &result.common.infers,
            &[
                expected_membership.clone(),
                expected_defining_equality.clone(),
            ],
            "named real function outer effects",
        )?;

        self.environment_stack.push_inherited_environment();
        let compiled_body: Result<Option<CompiledNamedFunctionDefinitionBody>, String> = (|| {
            let mut parameter_premises = Vec::with_capacity(function.parameters.len());
            for (parameter_index, ((parameter, fact), fact_id)) in function
                .parameters
                .iter()
                .zip(expected_parameter_facts.iter())
                .zip(parameter_fact_ids.iter())
                .enumerate()
            {
                let suffix = if function_uses_telescope(&function) {
                    (parameter_index + 1).to_string()
                } else {
                    String::new()
                };
                let argument_name = format!("__arg{suffix}");
                let membership_name = format!("__arg{suffix}_in");
                if self
                    .environment_stack
                    .symbol_names
                    .insert(parameter.symbol_id, argument_name.clone())
                    .is_some()
                {
                    return Err("named real function reused one parameter SymbolId".into());
                }
                self.environment_stack
                    .fact_names
                    .insert(*fact_id, membership_name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(*fact_id, fact.clone());
                if let Some(real) =
                    membership_real_value(&parameter.set, &argument_name, &membership_name)
                {
                    self.environment_stack
                        .numeric_real_values
                        .insert(parameter.symbol_id, real);
                }
                if let Some(integer) =
                    membership_integer_value(&parameter.set, &argument_name, &membership_name)
                {
                    self.environment_stack
                        .numeric_integer_values
                        .insert(parameter.symbol_id, integer);
                }
                if let Some(rational) =
                    membership_rational_value(&parameter.set, &argument_name, &membership_name)
                {
                    self.environment_stack
                        .numeric_rational_values
                        .insert(parameter.symbol_id, rational);
                }
                if let Some(representation) =
                    membership_numeric_value(&parameter.set, &argument_name, &membership_name)
                {
                    self.environment_stack
                        .numeric_representations
                        .insert(parameter.symbol_id, representation);
                }
                if let Some(proof) =
                    membership_numeric_proof(&parameter.set, &argument_name, &membership_name)
                {
                    self.environment_stack
                        .numeric_representation_memberships
                        .insert(parameter.symbol_id, proof);
                }
                parameter_premises.push(LeanLocalFactPremise::new(*fact_id, fact.clone()));
            }

            let mut domain_premises = Vec::with_capacity(expected_domain_facts.len());
            for (domain_index, (fact, fact_id)) in expected_domain_facts
                .iter()
                .zip(domain_fact_ids.iter())
                .enumerate()
            {
                let selector = conjunction_selector(domain_index, expected_domain_facts.len())?;
                let proof_name = if expected_domain_facts.len() == 1 {
                    "__arg_domain".to_string()
                } else {
                    format!("__arg_domain{selector}")
                };
                self.environment_stack
                    .fact_names
                    .insert(*fact_id, proof_name);
                self.environment_stack
                    .fact_propositions
                    .insert(*fact_id, fact.clone());
                domain_premises.push(LeanLocalFactPremise::new(*fact_id, fact.clone()));
            }

            let return_check = verification
                .return_check
                .factual_success()
                .ok_or_else(|| "named real function return check is not factual".to_string())?;
            if return_check.fact().to_string() != expected_return_check.to_string()
                || return_check.store.fact.to_string() != expected_return_check.to_string()
                || !return_check.store.infers.is_empty()
            {
                return Err(
                    "named real function changed or published effects from its local return check"
                        .into(),
                );
            }
            let return_proof = self
                .construct_lean_proof_from_direct_fact_result(return_check)?
                .ok_or_else(|| {
                    "named function return check has no direct recursive Result proof adapter"
                        .to_string()
                })?;
            let (value, native_body_carrier) = render_named_function_value_from_result(
                &function,
                &lowered_body,
                &source_body,
                &return_proof,
                &self.environment_stack,
            )?;
            Ok(Some(CompiledNamedFunctionDefinitionBody {
                function: function.clone(),
                source_body: source_body.clone(),
                lowered_body: lowered_body.clone(),
                value,
                native_body_carrier,
                parameter_premises,
                domain_premises,
            }))
        })(
        );
        self.environment_stack.pop_local_environment();
        let Some(compiled_body) = compiled_body? else {
            return Ok(false);
        };

        let name = lean_identifier(statement.name());
        let function_value_name = if function_uses_telescope(&compiled_body.function) {
            format!("(@{name})")
        } else {
            name.clone()
        };
        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), function_value_name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for `{}`",
                statement.name()
            ));
        }
        let function_type = render_function_type(&compiled_body.function, &self.environment_stack)?;
        let function_set = render_function_set(&compiled_body.function, &self.environment_stack)?;
        self.declarations.push(format!(
            "noncomputable def {name} : {function_type} :=\n  {}",
            compiled_body.value
        ));

        let membership_name = format!("__fact{}", self.next_fact_name_index);
        let membership_proposition = render_fact(&expected_membership, &self.environment_stack)?;
        self.declarations.push(format!(
            "theorem {membership_name} : {membership_proposition} := by\n  exact Litex.In.own {function_set} {function_value_name}"
        ));
        self.environment_stack
            .fact_names
            .insert(stored_fact_ids[0], membership_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(stored_fact_ids[0], expected_membership);
        self.environment_stack.function_bindings.insert(
            stored_fact_ids[0],
            FunctionBinding {
                symbol_id: statement.symbol_binding.id(),
                function: compiled_body.function.clone(),
                membership_proof_name: membership_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let equality_name = format!("__fact{}", self.next_fact_name_index);
        let equality_proposition = format!(
            "Litex.Same {function_value_name} ({} : {function_type})",
            compiled_body.value
        );
        self.declarations.push(format!(
            "theorem {equality_name} : {equality_proposition} := by\n  unfold {name}\n  exact Litex.Same.refl ({} : {function_type})",
            compiled_body.value
        ));
        self.environment_stack
            .fact_names
            .insert(stored_fact_ids[1], equality_name);
        self.environment_stack
            .fact_propositions
            .insert(stored_fact_ids[1], expected_defining_equality);
        self.environment_stack.named_function_definitions.insert(
            stored_fact_ids[1],
            NamedFunctionDefinitionBinding {
                symbol_id: statement.symbol_binding.id(),
                name,
                function: compiled_body.function,
                source_body: compiled_body.source_body,
                body: compiled_body.lowered_body,
                native_body_carrier: compiled_body.native_body_carrier,
                parameter_premises: compiled_body.parameter_premises,
                domain_premises: compiled_body.domain_premises,
                well_definedness: StmtResultWellDefinednessToLeanCompilationContext::default(),
            },
        );
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: compile the two retained dimension checks in the ambient
    /// environment, compile the coordinate value under its exact index
    /// binder, pop that child environment, then publish the three ordered
    /// tuple-definition store effects.
    pub(super) fn compile_have_tuple_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveTupleStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let statement = &result.statement;
        let lowered_dimension = LeanTargetObjectRepresentation::lower(&statement.dimension)?;
        let LeanTargetObjectRepresentation::Number {
            normalized_value: normalized_dimension,
        } = &lowered_dimension
        else {
            return Ok(false);
        };
        let dimension = normalized_dimension
            .parse::<usize>()
            .map_err(|_| "indexed tuple dimension is not a machine natural".to_string())?;
        if dimension < 2 {
            return Err("indexed tuple dimension is smaller than two".into());
        }

        let expected_positive_dimension: Fact = InFact::new(
            statement.dimension.clone(),
            StandardSet::NPos.into(),
            statement.line_file.clone(),
        )
        .into();
        let expected_at_least_two: Fact = LessEqualFact::new(
            Number::new("2".to_string()).into(),
            statement.dimension.clone(),
            statement.line_file.clone(),
        )
        .into();
        let positive_dimension = verification
            .dimension
            .positive_check
            .factual_success()
            .ok_or_else(|| "indexed tuple positive-dimension check is not factual".to_string())?;
        let at_least_two = verification
            .dimension
            .at_least_two_check
            .factual_success()
            .ok_or_else(|| "indexed tuple at-least-two check is not factual".to_string())?;
        for (check, expected, role) in [
            (
                positive_dimension,
                &expected_positive_dimension,
                "positive-dimension",
            ),
            (at_least_two, &expected_at_least_two, "at-least-two"),
        ] {
            if check.fact().to_string() != expected.to_string()
                || check.store.fact.to_string() != expected.to_string()
                || !check.store.infers.is_empty()
            {
                return Err(format!(
                    "indexed tuple {role} Result changed its target or published effects"
                ));
            }
        }
        let Some(positive_dimension_proof) =
            self.construct_lean_proof_from_direct_fact_result(positive_dimension)?
        else {
            return Ok(false);
        };
        let Some(at_least_two_dimension_proof) =
            self.construct_lean_proof_from_direct_fact_result(at_least_two)?
        else {
            return Ok(false);
        };

        let lowered_value = LeanTargetObjectRepresentation::lower(&statement.value)?;
        if !indexed_tuple_value_is_complex(&lowered_value, statement.index_binding.id()) {
            return Ok(false);
        }
        let mut visited = HashSet::new();
        validate_success_obj_well_defined_result(
            verification.value_well_definedness.as_ref(),
            &statement.value,
            &mut visited,
        )?;

        self.environment_stack.push_inherited_environment();
        let compiled_body = (|| {
            self.environment_stack
                .symbol_names
                .insert(statement.index_binding.id(), "__index".into());
            self.environment_stack.numeric_representations.insert(
                statement.index_binding.id(),
                "(((__index.val : ℤ) : ℂ))".into(),
            );
            self.environment_stack
                .numeric_integer_values
                .insert(statement.index_binding.id(), "(__index.val : ℤ)".into());
            self.environment_stack
                .numeric_rational_values
                .insert(statement.index_binding.id(), "(__index.val : ℚ)".into());
            let mut installed_well_definedness_nodes = HashSet::new();
            install_object_well_definedness_store_results(
                verification.value_well_definedness.as_ref(),
                &mut self.environment_stack,
                &mut installed_well_definedness_nodes,
            )?;
            let value = render_lean_source_for_numeric_target_object_representation(
                &lowered_value,
                &self.environment_stack,
            )?;
            Ok::<_, String>(CompiledIndexedTupleDefinitionBody {
                dimension,
                value,
                positive_dimension_proof,
                at_least_two_dimension_proof,
            })
        })();
        self.environment_stack.pop_local_environment();
        let compiled_body = compiled_body?;

        if !result.common.infers.rule_applications.is_empty() {
            return Err("indexed tuple stores retained unexpected typed infer rules".into());
        }
        let [is_tuple_output, dimension_output, coordinate_output] =
            result.common.infers.store_fact_outputs.as_slice()
        else {
            return Err("indexed tuple requires exactly three ordered store outputs".into());
        };
        for output in [is_tuple_output, dimension_output, coordinate_output] {
            if output.fact_id.is_none()
                || !output.inferred_facts.is_empty()
                || !output.inferred_fact_ids.is_empty()
            {
                return Err(
                    "indexed tuple store output lost its FactId or gained inferred children".into(),
                );
            }
        }

        let name = lean_identifier(statement.name());
        let positive_dimension_proposition =
            render_fact(&expected_positive_dimension, &self.environment_stack)?;
        let at_least_two_proposition =
            render_fact(&expected_at_least_two, &self.environment_stack)?;
        self.declarations.push(format!(
            "theorem __{name}_dimension_check1 : {positive_dimension_proposition} := by\n  exact {}",
            compiled_body.positive_dimension_proof
        ));
        self.declarations.push(format!(
            "theorem __{name}_dimension_check2 : {at_least_two_proposition} := by\n  exact {}",
            compiled_body.at_least_two_dimension_proof
        ));
        self.declarations.push(format!(
            "noncomputable def {name} : Litex.IndexedTuple {} ℂ :=\n  ⟨fun __index => {}⟩",
            compiled_body.dimension, compiled_body.value
        ));
        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for indexed tuple `{}`",
                statement.name()
            ));
        }
        self.environment_stack.indexed_tuple_bindings.insert(
            statement.symbol_binding.id(),
            IndexedTupleBinding {
                dimension: compiled_body.dimension,
            },
        );

        let target: Obj = Identifier::new_bound(
            statement.name().to_string(),
            statement.symbol_binding.as_ref(),
        )
        .into();
        let expected_is_tuple: Fact =
            IsTupleFact::new(target.clone(), statement.line_file.clone()).into();
        if is_tuple_output
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_is_tuple.to_string()
        {
            return Err("indexed tuple first store is not its exact IsTuple fact".into());
        }
        let is_tuple_fact_id = is_tuple_output
            .fact_id
            .expect("stored tuple output FactId validated above");
        let is_tuple_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {is_tuple_theorem_name} : {} := by\n  exact ⟨inferInstance⟩",
            render_fact(&expected_is_tuple, &self.environment_stack)?
        ));
        self.environment_stack
            .fact_names
            .insert(is_tuple_fact_id, is_tuple_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(is_tuple_fact_id, expected_is_tuple);
        self.next_fact_name_index += 1;

        let expected_dimension: Fact = EqualFact::new(
            TupleDim::new(target.clone()).into(),
            statement.dimension.clone(),
            statement.line_file.clone(),
        )
        .into();
        if dimension_output
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_dimension.to_string()
        {
            return Err("indexed tuple second store is not its exact dimension fact".into());
        }
        let dimension_fact_id = dimension_output
            .fact_id
            .expect("stored tuple output FactId validated above");
        let dimension_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {dimension_theorem_name} : {} := by\n  exact Litex.Same.ofEq (by rfl)",
            render_fact(&expected_dimension, &self.environment_stack)?
        ));
        self.environment_stack
            .fact_names
            .insert(dimension_fact_id, dimension_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(dimension_fact_id, expected_dimension);
        self.next_fact_name_index += 1;

        self.compile_indexed_tuple_coordinate_store_result_to_lean_source(
            statement,
            compiled_body.dimension,
            coordinate_output,
        )?;
        Ok(true)
    }

    pub(super) fn compile_indexed_tuple_coordinate_store_result_to_lean_source(
        &mut self,
        statement: &HaveTupleStmt,
        dimension: usize,
        coordinate_output: &SuccessStoreFactOutput,
    ) -> Result<(), String> {
        let coordinate_fact_id = coordinate_output
            .fact_id
            .ok_or_else(|| "indexed tuple coordinate store has no FactId".to_string())?;
        let Fact::ForallFact(forall) = &coordinate_output.itself_and_why_itself_is_stored.0 else {
            return Err("indexed tuple coordinate store is not a forall fact".into());
        };
        let parameters = forall.typed_parameters.collect_param_bindings_with_types();
        let [(binding, param_type)] = parameters.as_slice() else {
            return Err("indexed tuple coordinate store changed its one-index binder".into());
        };
        if !forall.dom_facts.is_empty() || forall.then_facts.len() != 1 {
            return Err(
                "indexed tuple coordinate store changed its domain or conclusion arity".into(),
            );
        }
        let Obj::ClosedRange(range) = parameter_set(param_type)? else {
            return Err("indexed tuple coordinate binder is not a closed range".into());
        };
        let lowered_start = LeanTargetObjectRepresentation::lower(range.start.as_ref())?;
        let lowered_end = LeanTargetObjectRepresentation::lower(range.end.as_ref())?;
        if lowered_start
            != (LeanTargetObjectRepresentation::Number {
                normalized_value: "1".into(),
            })
            || lowered_end != LeanTargetObjectRepresentation::lower(&statement.dimension)?
        {
            return Err("indexed tuple coordinate range changed its one-based dimension".into());
        }
        let conclusion = forall.then_facts[0].clone().to_fact();
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &conclusion else {
            return Err("indexed tuple coordinate conclusion is not an equality".into());
        };
        let Obj::ObjAtIndex(access) = &equality.left else {
            return Err("indexed tuple coordinate conclusion lost indexed access".into());
        };
        if !object_is_symbol(&access.obj, statement.symbol_binding.id())
            || !object_is_symbol(&access.index, binding.id())
        {
            return Err("indexed tuple coordinate conclusion changed its tuple or index".into());
        }

        let index = "__tuple_index";
        let membership = "__tuple_index_in";
        let exact_index = format!("(Litex.In.rep {index} {membership})");
        let numeric_index = format!("((({exact_index}).val : ℤ) : ℂ)");
        let mut nested = self.environment_stack.clone();
        nested.symbol_names.insert(binding.id(), index.into());
        nested
            .exact_tuple_indices
            .insert(binding.id(), exact_index.clone());
        nested
            .numeric_representations
            .insert(binding.id(), numeric_index.clone());

        let mut source_value_context = self.environment_stack.clone();
        source_value_context
            .symbol_names
            .insert(statement.index_binding.id(), index.into());
        source_value_context
            .numeric_representations
            .insert(statement.index_binding.id(), numeric_index);
        let expected_value = render_lean_source_for_numeric_target_object_representation(
            &LeanTargetObjectRepresentation::lower(&statement.value)?,
            &source_value_context,
        )?;
        let retained_value = render_lean_source_for_numeric_target_object_representation(
            &LeanTargetObjectRepresentation::lower(&equality.right)?,
            &nested,
        )?;
        if retained_value != expected_value {
            return Err("indexed tuple coordinate store changed its value expression".into());
        }

        let rendered_conclusion = render_fact(&conclusion, &nested)?;
        let range = format!("(Litex.closedRange (1 : ℤ) ({dimension} : ℤ))");
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} :\n    ∀ {{__tuple_index_carrier : Type}} ({index} : __tuple_index_carrier) ({membership} : Litex.In {index} {range}),\n      {rendered_conclusion} := by\n  intro __tuple_index_carrier {index} {membership}\n  exact Litex.Same.ofEq (by rfl)"
        ));
        self.environment_stack
            .fact_names
            .insert(coordinate_fact_id, theorem_name);
        self.environment_stack.fact_propositions.insert(
            coordinate_fact_id,
            coordinate_output.itself_and_why_itself_is_stored.0.clone(),
        );
        self.next_fact_name_index += 1;
        Ok(())
    }

    /// `Combine`: validate the three named WD children, enter the retained
    /// positive-natural index scope, install its exact parameter FactId,
    /// consume the recursive return-check proof there, and pop the local
    /// compiler environment before publishing the sequence's three outer
    /// facts. No compiler scope is reconstructed from Runtime state.
    pub(super) fn compile_have_sequence_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveSeqStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        if !verification.bound_checks.is_empty() {
            return Err("unbounded sequence retained unexpected bound checks".into());
        }
        let statement = &result.statement;
        let parameter_group = SetBoundParameterGroup::new(
            vec![statement.index_binding.clone()],
            StandardSet::NPos.into(),
        );
        let anonymous_function = AnonymousFn::new(
            vec![parameter_group.clone()],
            Vec::new(),
            statement.seq_set.set.as_ref().clone(),
            statement.value.clone(),
        )
        .map_err(|error| error.to_string())?;
        let function_set =
            FnSet::from_body(anonymous_function.body.clone()).map_err(|error| error.to_string())?;
        let function = LeanTargetFunctionTypeRepresentation::lower(&function_set)?;
        if function.parameters.len() != 1
            || function.parameters[0].symbol_id != statement.index_binding.id()
            || function.parameters[0].set
                != LeanTargetObjectRepresentation::StandardSet(
                    LeanTargetStandardSet::PositiveNatural,
                )
            || !function.domain_facts.is_empty()
            || function.return_set.as_ref()
                != &LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real)
        {
            return Ok(false);
        }

        let mut visited_well_definedness_results = HashSet::new();
        validate_success_obj_well_defined_result(
            verification.well_definedness.surface_set.as_ref(),
            &statement.seq_set.clone().into(),
            &mut visited_well_definedness_results,
        )?;
        validate_success_obj_well_defined_result(
            verification.well_definedness.anonymous_function.as_ref(),
            &anonymous_function.clone().into(),
            &mut visited_well_definedness_results,
        )?;
        validate_success_obj_well_defined_result(
            verification.well_definedness.function_set.as_ref(),
            &function_set.clone().into(),
            &mut visited_well_definedness_results,
        )?;

        let expected_parameter_facts = parameter_group.facts();
        let [expected_parameter_fact] = expected_parameter_facts.as_slice() else {
            return Err("sequence index scope did not produce one parameter fact".into());
        };
        if verification
            .assumption_infers
            .rule_applications
            .iter()
            .any(|application| {
                !infer_rule_has_direct_compiler_environment_consumer(&application.rule)
            })
            || !infer_result_effects_are_fully_owned_by_direct_compiler_rules(
                &verification.assumption_infers,
            )
        {
            return Err("sequence index assumptions retained unsupported typed infer rules".into());
        }
        let [parameter_store] = verification.assumption_infers.store_fact_outputs.as_slice() else {
            return Err("sequence index scope requires exactly one parameter store".into());
        };
        if parameter_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_parameter_fact.to_string()
        {
            return Err("sequence index scope changed its parameter membership".into());
        }
        let parameter_fact_id = parameter_store
            .fact_id
            .ok_or_else(|| "sequence index parameter store has no FactId".to_string())?;
        if parameter_store.inferred_facts.len() != parameter_store.inferred_fact_ids.len()
            || parameter_store
                .inferred_fact_ids
                .iter()
                .any(Option::is_none)
        {
            return Err("sequence index inference lost an inferred FactId".into());
        }
        let expected_positive_index: Fact = LessFact::new(
            Number::new("0".to_string()).into(),
            obj_for_bound_param_in_scope(&statement.index_binding),
            statement.line_file.clone(),
        )
        .into();
        if parameter_store.inferred_facts.len() != 1
            || parameter_store.inferred_facts[0].to_string() != expected_positive_index.to_string()
        {
            return Err("sequence index scope changed its positive-index inference".into());
        }

        let source_body = statement.value.clone();
        let lowered_body = LeanTargetObjectRepresentation::lower(&source_body)?;
        let expected_return_check: Fact = InFact::new(
            source_body.clone(),
            statement.seq_set.set.as_ref().clone(),
            statement.line_file.clone(),
        )
        .into();
        self.environment_stack.push_inherited_environment();
        let compiled_body: Result<CompiledIndexedFunctionDefinitionBody, String> = (|| {
            self.environment_stack
                .symbol_names
                .insert(statement.index_binding.id(), "__arg".into());
            self.environment_stack
                .fact_names
                .insert(parameter_fact_id, "__arg_in".into());
            self.environment_stack
                .fact_propositions
                .insert(parameter_fact_id, expected_parameter_fact.clone());
            self.install_standard_numeric_membership_inference_results_in_current_environment(
                &verification.assumption_infers,
                &[(parameter_fact_id, expected_parameter_fact.clone())],
                "sequence index inference",
            )?;
            self.environment_stack.numeric_representations.insert(
                statement.index_binding.id(),
                "((((Litex.In.rep __arg __arg_in).val : ℕ) : ℂ))".into(),
            );
            self.environment_stack.numeric_integer_values.insert(
                statement.index_binding.id(),
                "(((Litex.In.rep __arg __arg_in).val : ℕ) : ℤ)".into(),
            );
            self.environment_stack.numeric_rational_values.insert(
                statement.index_binding.id(),
                "(((Litex.In.rep __arg __arg_in).val : ℕ) : ℚ)".into(),
            );
            self.environment_stack.numeric_real_values.insert(
                statement.index_binding.id(),
                "((((Litex.In.rep __arg __arg_in).val : ℕ) : ℝ))".into(),
            );

            let mut installed_well_definedness_nodes = HashSet::new();
            for well_definedness in [
                verification.well_definedness.surface_set.as_ref(),
                verification.well_definedness.anonymous_function.as_ref(),
                verification.well_definedness.function_set.as_ref(),
            ] {
                install_object_well_definedness_store_results(
                    well_definedness,
                    &mut self.environment_stack,
                    &mut installed_well_definedness_nodes,
                )?;
            }

            let return_check = verification
                .return_check
                .factual_success()
                .ok_or_else(|| "sequence return check is not factual".to_string())?;
            if return_check.fact().to_string() != expected_return_check.to_string()
                || return_check.store.fact.to_string() != expected_return_check.to_string()
                || !return_check.store.infers.is_empty()
            {
                return Err(
                    "sequence return check changed its target or published local effects".into(),
                );
            }
            if self
                .construct_lean_proof_from_direct_fact_result(return_check)?
                .is_none()
            {
                return Err(
                    "sequence return check has no direct recursive Result proof adapter".into(),
                );
            }

            let parameter_real_value = "((((Litex.In.rep __arg __arg_in).val : ℕ) : ℝ))";
            let rendered_body = render_real_function_body(
                &lowered_body,
                statement.index_binding.id(),
                parameter_real_value,
                &self.environment_stack,
            )?;
            Ok(CompiledIndexedFunctionDefinitionBody {
                function: function.clone(),
                source_body: source_body.clone(),
                lowered_body: lowered_body.clone(),
                value: format!(
                    "{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in => {rendered_body} }}"
                ),
                parameter_premises: vec![LeanLocalFactPremise::new(
                    parameter_fact_id,
                    expected_parameter_fact.clone(),
                )],
                domain_premises: Vec::new(),
            })
        })();
        self.environment_stack.pop_local_environment();
        let compiled_body = compiled_body?;

        if !result.common.infers.rule_applications.is_empty() {
            return Err("sequence definition retained unexpected outer typed infer rules".into());
        }
        let [surface_membership_store, defining_equality_store] =
            result.common.infers.store_fact_outputs.as_slice()
        else {
            return Err("sequence definition requires two ordered outer store outputs".into());
        };
        let function_object: Obj = Identifier::new_bound(
            statement.name().to_string(),
            statement.symbol_binding.as_ref(),
        )
        .into();
        let expected_surface_membership: Fact = InFact::new(
            function_object.clone(),
            statement.seq_set.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        let expected_defining_equality: Fact = EqualFact::new(
            function_object.clone(),
            anonymous_function.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        if surface_membership_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_surface_membership.to_string()
        {
            return Err("sequence first outer store changed its surface membership".into());
        }
        let surface_membership_fact_id = surface_membership_store
            .fact_id
            .ok_or_else(|| "sequence surface membership store has no FactId".to_string())?;
        let [inferred_function_membership] = surface_membership_store.inferred_facts.as_slice()
        else {
            return Err("sequence surface membership must infer one function membership".into());
        };
        let [Some(function_membership_fact_id)] =
            surface_membership_store.inferred_fact_ids.as_slice()
        else {
            return Err("sequence inferred function membership has no FactId".into());
        };
        let (inferred_function_object, inferred_function_set) =
            membership_parts(inferred_function_membership)?;
        if !object_is_symbol(inferred_function_object, statement.symbol_binding.id()) {
            return Err("sequence inferred function membership changed its function".into());
        }
        let Obj::FnSet(inferred_function_set) = inferred_function_set else {
            return Err("sequence inferred membership does not retain a function set".into());
        };
        let inferred_function = LeanTargetFunctionTypeRepresentation::lower(inferred_function_set)?;
        if inferred_function.parameters.len() != 1
            || inferred_function.parameters[0].set != compiled_body.function.parameters[0].set
            || !inferred_function.domain_facts.is_empty()
            || inferred_function.return_set != compiled_body.function.return_set
        {
            return Err("sequence inferred function membership changed its signature".into());
        }
        if defining_equality_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_defining_equality.to_string()
            || !defining_equality_store.inferred_facts.is_empty()
            || !defining_equality_store.inferred_fact_ids.is_empty()
        {
            return Err("sequence second outer store changed its defining equality".into());
        }
        let defining_equality_fact_id = defining_equality_store
            .fact_id
            .ok_or_else(|| "sequence defining equality store has no FactId".to_string())?;
        if [
            surface_membership_fact_id,
            *function_membership_fact_id,
            defining_equality_fact_id,
        ]
        .into_iter()
        .collect::<HashSet<_>>()
        .len()
            != 3
        {
            return Err("sequence outer stores reused a FactId across semantic roles".into());
        }

        let name = lean_identifier(statement.name());
        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for sequence `{}`",
                statement.name()
            ));
        }
        let function_type = render_function_type(&compiled_body.function, &self.environment_stack)?;
        let rendered_function_set =
            render_function_set(&compiled_body.function, &self.environment_stack)?;
        self.declarations.push(format!(
            "noncomputable def {name} : {function_type} :=\n  {}",
            compiled_body.value
        ));

        let surface_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {surface_theorem_name} : {} := by\n  exact Litex.In.own {} {name}",
            render_fact(&expected_surface_membership, &self.environment_stack)?,
            render_obj(&statement.seq_set.clone().into(), &self.environment_stack)?,
        ));
        self.environment_stack
            .fact_names
            .insert(surface_membership_fact_id, surface_theorem_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(surface_membership_fact_id, expected_surface_membership);
        // Runtime selects the surface membership FactId as the callable
        // contract. `sequenceSet` is definitionally this exact function set,
        // so preserve that identity instead of substituting the separately
        // inferred function-membership FactId.
        self.environment_stack.function_bindings.insert(
            surface_membership_fact_id,
            FunctionBinding {
                symbol_id: statement.symbol_binding.id(),
                function: compiled_body.function.clone(),
                membership_proof_name: surface_theorem_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let function_membership_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {function_membership_theorem_name} : {} := by\n  exact Litex.In.own {rendered_function_set} {name}",
            render_fact(inferred_function_membership, &self.environment_stack)?,
        ));
        self.environment_stack.fact_names.insert(
            *function_membership_fact_id,
            function_membership_theorem_name.clone(),
        );
        self.environment_stack.fact_propositions.insert(
            *function_membership_fact_id,
            inferred_function_membership.clone(),
        );
        self.environment_stack.function_bindings.insert(
            *function_membership_fact_id,
            FunctionBinding {
                symbol_id: statement.symbol_binding.id(),
                function: compiled_body.function.clone(),
                membership_proof_name: function_membership_theorem_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let equality_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {equality_theorem_name} : Litex.Same {name} ({} : {function_type}) := by\n  unfold {name}\n  exact Litex.Same.refl ({} : {function_type})",
            compiled_body.value, compiled_body.value
        ));
        self.environment_stack
            .fact_names
            .insert(defining_equality_fact_id, equality_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(defining_equality_fact_id, expected_defining_equality);
        self.environment_stack.named_function_definitions.insert(
            defining_equality_fact_id,
            NamedFunctionDefinitionBinding {
                symbol_id: statement.symbol_binding.id(),
                name,
                function: compiled_body.function,
                source_body: compiled_body.source_body,
                body: compiled_body.lowered_body,
                native_body_carrier: NativeFunctionBodyCarrier::Real,
                parameter_premises: compiled_body.parameter_premises,
                domain_premises: compiled_body.domain_premises,
                well_definedness: StmtResultWellDefinednessToLeanCompilationContext::default(),
            },
        );
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: consume the two outer bound checks, validate the three
    /// named WD children, then enter the retained positive-natural parameter
    /// and domain-premise scope. The local parameter/domain FactIds are
    /// available while compiling the recursive return check and disappear
    /// when that Result field closes. Only then are the three persistent
    /// definition facts published in the parent compiler environment.
    pub(super) fn compile_have_finite_sequence_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveFiniteSeqStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let statement = &result.statement;
        let [positive_bound_check, matching_length_check] = verification.bound_checks.as_slice()
        else {
            return Err("finite-sequence verification requires two ordered bound checks".into());
        };
        let expected_positive_bound: Fact = InFact::new(
            statement.bound.clone(),
            StandardSet::NPos.into(),
            statement.line_file.clone(),
        )
        .into();
        let expected_matching_length: Fact = EqualFact::new(
            statement.bound.clone(),
            statement.finite_seq_set.n.as_ref().clone(),
            statement.line_file.clone(),
        )
        .into();
        for (label, checked_result, expected_fact) in [
            (
                "positive bound",
                positive_bound_check,
                &expected_positive_bound,
            ),
            (
                "matching length",
                matching_length_check,
                &expected_matching_length,
            ),
        ] {
            let checked_fact = checked_result
                .factual_success()
                .ok_or_else(|| format!("finite-sequence {label} check is not factual"))?;
            if checked_fact.fact().to_string() != expected_fact.to_string()
                || checked_fact.store.fact.to_string() != expected_fact.to_string()
                || !checked_fact.store.infers.is_empty()
            {
                return Err(format!(
                    "finite-sequence {label} check changed its target or published effects"
                ));
            }
            if self
                .construct_lean_proof_from_direct_fact_result(checked_fact)?
                .is_none()
            {
                return Err(format!(
                    "finite-sequence {label} check has no direct recursive Result proof adapter"
                ));
            }
        }

        let index_object = obj_for_bound_param_in_scope(&statement.index_binding);
        let expected_domain_atomic_fact: AtomicFact = LessEqualFact::new(
            index_object,
            statement.bound.clone(),
            statement.line_file.clone(),
        )
        .into();
        let expected_domain_fact: Fact = expected_domain_atomic_fact.clone().into();
        let parameter_group = SetBoundParameterGroup::new(
            vec![statement.index_binding.clone()],
            StandardSet::NPos.into(),
        );
        let anonymous_function = AnonymousFn::new(
            vec![parameter_group.clone()],
            vec![expected_domain_atomic_fact.into()],
            statement.finite_seq_set.set.as_ref().clone(),
            statement.value.clone(),
        )
        .map_err(|error| error.to_string())?;
        let function_set =
            FnSet::from_body(anonymous_function.body.clone()).map_err(|error| error.to_string())?;
        let function = LeanTargetFunctionTypeRepresentation::lower(&function_set)?;
        if function.parameters.len() != 1
            || function.parameters[0].symbol_id != statement.index_binding.id()
            || function.parameters[0].set
                != LeanTargetObjectRepresentation::StandardSet(
                    LeanTargetStandardSet::PositiveNatural,
                )
            || function.domain_facts.len() != 1
            || function.return_set.as_ref()
                != &LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real)
            || !function_uses_telescope(&function)
        {
            return Ok(false);
        }
        // The target `finiteSequenceSet` ABI currently requires a closed
        // natural length. Validate this support boundary before mutating any
        // compiler environment.
        let lowered_length =
            LeanTargetObjectRepresentation::lower(statement.finite_seq_set.n.as_ref())?;
        render_natural_endpoint(&lowered_length)?;

        let mut visited_well_definedness_results = HashSet::new();
        validate_success_obj_well_defined_result(
            verification.well_definedness.surface_set.as_ref(),
            &statement.finite_seq_set.clone().into(),
            &mut visited_well_definedness_results,
        )?;
        validate_success_obj_well_defined_result(
            verification.well_definedness.anonymous_function.as_ref(),
            &anonymous_function.clone().into(),
            &mut visited_well_definedness_results,
        )?;
        validate_success_obj_well_defined_result(
            verification.well_definedness.function_set.as_ref(),
            &function_set.clone().into(),
            &mut visited_well_definedness_results,
        )?;

        let expected_parameter_facts = parameter_group.facts();
        let [expected_parameter_fact] = expected_parameter_facts.as_slice() else {
            return Err("finite-sequence index scope did not produce one parameter fact".into());
        };
        if verification
            .assumption_infers
            .rule_applications
            .iter()
            .any(|application| {
                !infer_rule_has_direct_compiler_environment_consumer(&application.rule)
            })
            || !infer_result_effects_are_fully_owned_by_direct_compiler_rules(
                &verification.assumption_infers,
            )
        {
            return Err(
                "finite-sequence index assumptions retained unsupported typed infer rules".into(),
            );
        }
        let [parameter_store, domain_store] =
            verification.assumption_infers.store_fact_outputs.as_slice()
        else {
            return Err(
                "finite-sequence index scope requires one parameter store and one domain store"
                    .into(),
            );
        };
        if parameter_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_parameter_fact.to_string()
        {
            return Err("finite-sequence index scope changed its parameter membership".into());
        }
        let parameter_fact_id = parameter_store
            .fact_id
            .ok_or_else(|| "finite-sequence index parameter store has no FactId".to_string())?;
        if parameter_store.inferred_facts.len() != parameter_store.inferred_fact_ids.len()
            || parameter_store
                .inferred_fact_ids
                .iter()
                .any(Option::is_none)
        {
            return Err("finite-sequence index inference lost an inferred FactId".into());
        }
        let expected_positive_index: Fact = LessFact::new(
            Number::new("0".to_string()).into(),
            obj_for_bound_param_in_scope(&statement.index_binding),
            statement.line_file.clone(),
        )
        .into();
        if parameter_store.inferred_facts.len() != 1
            || parameter_store.inferred_facts[0].to_string() != expected_positive_index.to_string()
        {
            return Err("finite-sequence index scope changed its positive-index inference".into());
        }
        if domain_store.itself_and_why_itself_is_stored.0.to_string()
            != expected_domain_fact.to_string()
            || !domain_store.inferred_facts.is_empty()
            || !domain_store.inferred_fact_ids.is_empty()
        {
            return Err("finite-sequence index scope changed its domain premise".into());
        }
        let domain_fact_id = domain_store
            .fact_id
            .ok_or_else(|| "finite-sequence domain store has no FactId".to_string())?;
        if parameter_fact_id == domain_fact_id {
            return Err("finite-sequence local parameter and domain stores reused a FactId".into());
        }

        let source_body = statement.value.clone();
        let lowered_body = LeanTargetObjectRepresentation::lower(&source_body)?;
        let expected_return_check: Fact = InFact::new(
            source_body.clone(),
            statement.finite_seq_set.set.as_ref().clone(),
            statement.line_file.clone(),
        )
        .into();
        self.environment_stack.push_inherited_environment();
        let compiled_body: Result<CompiledIndexedFunctionDefinitionBody, String> = (|| {
            self.environment_stack
                .symbol_names
                .insert(statement.index_binding.id(), "__arg1".into());
            self.environment_stack
                .fact_names
                .insert(parameter_fact_id, "__arg1_in".into());
            self.environment_stack
                .fact_propositions
                .insert(parameter_fact_id, expected_parameter_fact.clone());
            self.environment_stack
                .fact_names
                .insert(domain_fact_id, "__arg_domain".into());
            self.environment_stack
                .fact_propositions
                .insert(domain_fact_id, expected_domain_fact.clone());
            self.install_standard_numeric_membership_inference_results_in_current_environment(
                &verification.assumption_infers,
                &[
                    (parameter_fact_id, expected_parameter_fact.clone()),
                    (domain_fact_id, expected_domain_fact.clone()),
                ],
                "finite-sequence index inference",
            )?;
            self.environment_stack.numeric_representations.insert(
                statement.index_binding.id(),
                "((((Litex.In.rep __arg1 __arg1_in).val : ℕ) : ℂ))".into(),
            );
            self.environment_stack.numeric_integer_values.insert(
                statement.index_binding.id(),
                "(((Litex.In.rep __arg1 __arg1_in).val : ℕ) : ℤ)".into(),
            );
            self.environment_stack.numeric_rational_values.insert(
                statement.index_binding.id(),
                "(((Litex.In.rep __arg1 __arg1_in).val : ℕ) : ℚ)".into(),
            );
            self.environment_stack.numeric_real_values.insert(
                statement.index_binding.id(),
                "((((Litex.In.rep __arg1 __arg1_in).val : ℕ) : ℝ))".into(),
            );

            let mut installed_well_definedness_nodes = HashSet::new();
            for well_definedness in [
                verification.well_definedness.surface_set.as_ref(),
                verification.well_definedness.anonymous_function.as_ref(),
                verification.well_definedness.function_set.as_ref(),
            ] {
                install_object_well_definedness_store_results(
                    well_definedness,
                    &mut self.environment_stack,
                    &mut installed_well_definedness_nodes,
                )?;
            }

            let return_check = verification
                .return_check
                .factual_success()
                .ok_or_else(|| "finite-sequence return check is not factual".to_string())?;
            if return_check.fact().to_string() != expected_return_check.to_string()
                || return_check.store.fact.to_string() != expected_return_check.to_string()
                || !return_check.store.infers.is_empty()
            {
                return Err(
                    "finite-sequence return check changed its target or published local effects"
                        .into(),
                );
            }
            if self
                .construct_lean_proof_from_direct_fact_result(return_check)?
                .is_none()
            {
                return Err(
                    "finite-sequence return check has no direct recursive Result proof adapter"
                        .into(),
                );
            }

            let rendered_body = render_real_function_body(
                &lowered_body,
                statement.index_binding.id(),
                "((((Litex.In.rep __arg1 __arg1_in).val : ℕ) : ℝ))",
                &self.environment_stack,
            )?;
            Ok(CompiledIndexedFunctionDefinitionBody {
                function: function.clone(),
                source_body: source_body.clone(),
                lowered_body: lowered_body.clone(),
                value: format!(
                    "fun {{__alpha1 : Type}} (__arg1 : __alpha1) (__arg1_in : Litex.In __arg1 Litex.NPos) => fun __arg_domain => ULift.up ({rendered_body})"
                ),
                parameter_premises: vec![LeanLocalFactPremise::new(
                    parameter_fact_id,
                    expected_parameter_fact.clone(),
                )],
                domain_premises: vec![LeanLocalFactPremise::new(
                    domain_fact_id,
                    expected_domain_fact.clone(),
                )],
            })
        })();
        self.environment_stack.pop_local_environment();
        let compiled_body = compiled_body?;

        if !result.common.infers.rule_applications.is_empty() {
            return Err(
                "finite-sequence definition retained unexpected outer typed infer rules".into(),
            );
        }
        let [surface_membership_store, defining_equality_store] =
            result.common.infers.store_fact_outputs.as_slice()
        else {
            return Err(
                "finite-sequence definition requires two ordered outer store outputs".into(),
            );
        };
        let function_object: Obj = Identifier::new_bound(
            statement.name().to_string(),
            statement.symbol_binding.as_ref(),
        )
        .into();
        let expected_surface_membership: Fact = InFact::new(
            function_object.clone(),
            statement.finite_seq_set.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        let expected_defining_equality: Fact = EqualFact::new(
            function_object.clone(),
            anonymous_function.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        if surface_membership_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_surface_membership.to_string()
        {
            return Err("finite-sequence first outer store changed its surface membership".into());
        }
        let surface_membership_fact_id = surface_membership_store
            .fact_id
            .ok_or_else(|| "finite-sequence surface membership store has no FactId".to_string())?;
        let [inferred_function_membership] = surface_membership_store.inferred_facts.as_slice()
        else {
            return Err(
                "finite-sequence surface membership must infer one function membership".into(),
            );
        };
        let [Some(function_membership_fact_id)] =
            surface_membership_store.inferred_fact_ids.as_slice()
        else {
            return Err("finite-sequence inferred function membership has no FactId".into());
        };
        let (inferred_function_object, inferred_function_set) =
            membership_parts(inferred_function_membership)?;
        if !object_is_symbol(inferred_function_object, statement.symbol_binding.id()) {
            return Err("finite-sequence inferred function membership changed its function".into());
        }
        let Obj::FnSet(inferred_function_set) = inferred_function_set else {
            return Err(
                "finite-sequence inferred membership does not retain a function set".into(),
            );
        };
        let inferred_function = LeanTargetFunctionTypeRepresentation::lower(inferred_function_set)?;
        if inferred_function.parameters.len() != 1
            || inferred_function.parameters[0].set != compiled_body.function.parameters[0].set
            || inferred_function.domain_facts.len() != 1
            || inferred_function.return_set != compiled_body.function.return_set
        {
            return Err(
                "finite-sequence inferred function membership changed its signature".into(),
            );
        }
        let mut expected_domain_environment = self.environment_stack.clone();
        expected_domain_environment.symbol_names.insert(
            compiled_body.function.parameters[0].symbol_id,
            "__finite_sequence_index".into(),
        );
        expected_domain_environment.numeric_representations.insert(
            compiled_body.function.parameters[0].symbol_id,
            "__finite_sequence_index_complex".into(),
        );
        let mut inferred_domain_environment = self.environment_stack.clone();
        inferred_domain_environment.symbol_names.insert(
            inferred_function.parameters[0].symbol_id,
            "__finite_sequence_index".into(),
        );
        inferred_domain_environment.numeric_representations.insert(
            inferred_function.parameters[0].symbol_id,
            "__finite_sequence_index_complex".into(),
        );
        if render_fact(
            &compiled_body.function.domain_facts[0],
            &expected_domain_environment,
        )? != render_fact(
            &inferred_function.domain_facts[0],
            &inferred_domain_environment,
        )? {
            return Err(
                "finite-sequence inferred function membership changed its bound clause".into(),
            );
        }
        if defining_equality_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_defining_equality.to_string()
            || !defining_equality_store.inferred_facts.is_empty()
            || !defining_equality_store.inferred_fact_ids.is_empty()
        {
            return Err("finite-sequence second outer store changed its defining equality".into());
        }
        let defining_equality_fact_id = defining_equality_store
            .fact_id
            .ok_or_else(|| "finite-sequence defining equality store has no FactId".to_string())?;
        if [
            surface_membership_fact_id,
            *function_membership_fact_id,
            defining_equality_fact_id,
        ]
        .into_iter()
        .collect::<HashSet<_>>()
        .len()
            != 3
        {
            return Err(
                "finite-sequence outer stores reused a FactId across semantic roles".into(),
            );
        }

        let name = lean_identifier(statement.name());
        let function_value_name = format!("(@{name})");
        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), function_value_name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for finite sequence `{}`",
                statement.name()
            ));
        }
        let function_type = render_function_type(&compiled_body.function, &self.environment_stack)?;
        let rendered_function_set =
            render_function_set(&compiled_body.function, &self.environment_stack)?;
        self.declarations.push(format!(
            "noncomputable def {name} : {function_type} :=\n  {}",
            compiled_body.value
        ));

        let surface_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {surface_theorem_name} : {} := by\n  exact Litex.In.own {} {function_value_name}",
            render_fact(&expected_surface_membership, &self.environment_stack)?,
            render_obj(
                &statement.finite_seq_set.clone().into(),
                &self.environment_stack,
            )?,
        ));
        self.environment_stack
            .fact_names
            .insert(surface_membership_fact_id, surface_theorem_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(surface_membership_fact_id, expected_surface_membership);
        self.environment_stack.function_bindings.insert(
            surface_membership_fact_id,
            FunctionBinding {
                symbol_id: statement.symbol_binding.id(),
                function: compiled_body.function.clone(),
                membership_proof_name: surface_theorem_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let function_membership_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {function_membership_theorem_name} : {} := by\n  exact Litex.In.own {rendered_function_set} {function_value_name}",
            render_fact(inferred_function_membership, &self.environment_stack)?,
        ));
        self.environment_stack.fact_names.insert(
            *function_membership_fact_id,
            function_membership_theorem_name.clone(),
        );
        self.environment_stack.fact_propositions.insert(
            *function_membership_fact_id,
            inferred_function_membership.clone(),
        );
        self.environment_stack.function_bindings.insert(
            *function_membership_fact_id,
            FunctionBinding {
                symbol_id: statement.symbol_binding.id(),
                function: compiled_body.function.clone(),
                membership_proof_name: function_membership_theorem_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let equality_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {equality_theorem_name} : Litex.Same {function_value_name} ({} : {function_type}) := by\n  unfold {name}\n  exact Litex.Same.refl ({} : {function_type})",
            compiled_body.value, compiled_body.value
        ));
        self.environment_stack
            .fact_names
            .insert(defining_equality_fact_id, equality_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(defining_equality_fact_id, expected_defining_equality);
        self.environment_stack.named_function_definitions.insert(
            defining_equality_fact_id,
            NamedFunctionDefinitionBinding {
                symbol_id: statement.symbol_binding.id(),
                name,
                function: compiled_body.function,
                source_body: compiled_body.source_body,
                body: compiled_body.lowered_body,
                native_body_carrier: NativeFunctionBodyCarrier::Real,
                parameter_premises: compiled_body.parameter_premises,
                domain_premises: compiled_body.domain_premises,
                well_definedness: StmtResultWellDefinednessToLeanCompilationContext::default(),
            },
        );
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: consume four outer row/column bound checks, enter one local
    /// Result layer containing two parameter stores, two domain-premise
    /// stores, and the recursive return check, then publish only the matrix's
    /// persistent facts after that compiler environment has been popped.
    pub(super) fn compile_have_matrix_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveMatrixStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let statement = &result.statement;
        let expected_bound_checks: [Fact; 4] = [
            InFact::new(
                statement.row_bound.clone(),
                StandardSet::NPos.into(),
                statement.line_file.clone(),
            )
            .into(),
            EqualFact::new(
                statement.row_bound.clone(),
                statement.matrix_set.row_len.as_ref().clone(),
                statement.line_file.clone(),
            )
            .into(),
            InFact::new(
                statement.col_bound.clone(),
                StandardSet::NPos.into(),
                statement.line_file.clone(),
            )
            .into(),
            EqualFact::new(
                statement.col_bound.clone(),
                statement.matrix_set.col_len.as_ref().clone(),
                statement.line_file.clone(),
            )
            .into(),
        ];
        if verification.bound_checks.len() != expected_bound_checks.len() {
            return Err("matrix verification requires four ordered bound checks".into());
        }
        for (check_index, (checked_result, expected_fact)) in verification
            .bound_checks
            .iter()
            .zip(expected_bound_checks.iter())
            .enumerate()
        {
            let checked_fact = checked_result
                .factual_success()
                .ok_or_else(|| format!("matrix bound check {check_index} is not factual"))?;
            if checked_fact.fact().to_string() != expected_fact.to_string()
                || checked_fact.store.fact.to_string() != expected_fact.to_string()
                || !checked_fact.store.infers.is_empty()
            {
                return Err(format!(
                    "matrix bound check {check_index} changed its target or published effects"
                ));
            }
            if self
                .construct_lean_proof_from_direct_fact_result(checked_fact)?
                .is_none()
            {
                return Err(format!(
                    "matrix bound check {check_index} has no direct recursive Result proof adapter"
                ));
            }
        }

        let parameter_groups = [
            SetBoundParameterGroup::new(
                vec![statement.row_index_binding.clone()],
                StandardSet::NPos.into(),
            ),
            SetBoundParameterGroup::new(
                vec![statement.col_index_binding.clone()],
                StandardSet::NPos.into(),
            ),
        ];
        let domain_atomic_facts = [
            AtomicFact::from(LessEqualFact::new(
                obj_for_bound_param_in_scope(&statement.row_index_binding),
                statement.row_bound.clone(),
                statement.line_file.clone(),
            )),
            AtomicFact::from(LessEqualFact::new(
                obj_for_bound_param_in_scope(&statement.col_index_binding),
                statement.col_bound.clone(),
                statement.line_file.clone(),
            )),
        ];
        let expected_domain_facts = domain_atomic_facts
            .iter()
            .cloned()
            .map(Fact::from)
            .collect::<Vec<_>>();
        let anonymous_function = AnonymousFn::new(
            parameter_groups.to_vec(),
            domain_atomic_facts
                .iter()
                .cloned()
                .map(QuantifierFreeFact::from)
                .collect(),
            statement.matrix_set.set.as_ref().clone(),
            statement.value.clone(),
        )
        .map_err(|error| error.to_string())?;
        let function_set =
            FnSet::from_body(anonymous_function.body.clone()).map_err(|error| error.to_string())?;
        let function = LeanTargetFunctionTypeRepresentation::lower(&function_set)?;
        if function.parameters.len() != 2
            || function.parameters[0].symbol_id != statement.row_index_binding.id()
            || function.parameters[1].symbol_id != statement.col_index_binding.id()
            || function.parameters.iter().any(|parameter| {
                parameter.set
                    != LeanTargetObjectRepresentation::StandardSet(
                        LeanTargetStandardSet::PositiveNatural,
                    )
            })
            || function.domain_facts.len() != 2
            || function.return_set.as_ref()
                != &LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real)
            || !function_uses_telescope(&function)
        {
            return Ok(false);
        }
        for count in [
            statement.matrix_set.row_len.as_ref(),
            statement.matrix_set.col_len.as_ref(),
        ] {
            render_natural_endpoint(&LeanTargetObjectRepresentation::lower(count)?)?;
        }

        let mut visited_well_definedness_results = HashSet::new();
        validate_success_obj_well_defined_result(
            verification.well_definedness.surface_set.as_ref(),
            &statement.matrix_set.clone().into(),
            &mut visited_well_definedness_results,
        )?;
        validate_success_obj_well_defined_result(
            verification.well_definedness.anonymous_function.as_ref(),
            &anonymous_function.clone().into(),
            &mut visited_well_definedness_results,
        )?;
        validate_success_obj_well_defined_result(
            verification.well_definedness.function_set.as_ref(),
            &function_set.clone().into(),
            &mut visited_well_definedness_results,
        )?;

        let expected_parameter_facts = parameter_groups
            .iter()
            .flat_map(|group| group.facts())
            .collect::<Vec<_>>();
        if expected_parameter_facts.len() != 2 {
            return Err("matrix index scope did not produce two parameter facts".into());
        }
        if verification
            .assumption_infers
            .rule_applications
            .iter()
            .any(|application| {
                !infer_rule_has_direct_compiler_environment_consumer(&application.rule)
            })
            || !infer_result_effects_are_fully_owned_by_direct_compiler_rules(
                &verification.assumption_infers,
            )
        {
            return Err("matrix index assumptions retained unsupported typed infer rules".into());
        }
        let assumption_stores = &verification.assumption_infers.store_fact_outputs;
        if assumption_stores.len() != 4 {
            return Err(
                "matrix index scope requires two parameter stores and two domain stores".into(),
            );
        }
        let mut parameter_fact_ids = Vec::with_capacity(2);
        let parameter_bindings = [&statement.row_index_binding, &statement.col_index_binding];
        for parameter_index in 0..2 {
            let store = &assumption_stores[parameter_index];
            let expected_fact = &expected_parameter_facts[parameter_index];
            if store.itself_and_why_itself_is_stored.0.to_string() != expected_fact.to_string() {
                return Err(format!(
                    "matrix parameter store {parameter_index} changed its membership"
                ));
            }
            let fact_id = store
                .fact_id
                .ok_or_else(|| format!("matrix parameter store {parameter_index} has no FactId"))?;
            let expected_positive: Fact = LessFact::new(
                Number::new("0".to_string()).into(),
                obj_for_bound_param_in_scope(parameter_bindings[parameter_index]),
                statement.line_file.clone(),
            )
            .into();
            if store.inferred_facts.len() != 1
                || store.inferred_fact_ids.len() != 1
                || store.inferred_fact_ids[0].is_none()
                || store.inferred_facts[0].to_string() != expected_positive.to_string()
            {
                return Err(format!(
                    "matrix parameter store {parameter_index} changed its positive-index inference"
                ));
            }
            parameter_fact_ids.push(fact_id);
        }
        let mut domain_fact_ids = Vec::with_capacity(2);
        for domain_index in 0..2 {
            let store = &assumption_stores[domain_index + 2];
            if store.itself_and_why_itself_is_stored.0.to_string()
                != expected_domain_facts[domain_index].to_string()
                || !store.inferred_facts.is_empty()
                || !store.inferred_fact_ids.is_empty()
            {
                return Err(format!(
                    "matrix domain store {domain_index} changed its premise"
                ));
            }
            domain_fact_ids.push(
                store
                    .fact_id
                    .ok_or_else(|| format!("matrix domain store {domain_index} has no FactId"))?,
            );
        }
        if parameter_fact_ids
            .iter()
            .chain(domain_fact_ids.iter())
            .copied()
            .collect::<HashSet<_>>()
            .len()
            != 4
        {
            return Err("matrix local stores reused a FactId across semantic roles".into());
        }

        let source_body = statement.value.clone();
        let lowered_body = LeanTargetObjectRepresentation::lower(&source_body)?;
        let expected_return_check: Fact = InFact::new(
            source_body.clone(),
            statement.matrix_set.set.as_ref().clone(),
            statement.line_file.clone(),
        )
        .into();
        self.environment_stack.push_inherited_environment();
        let compiled_body: Result<CompiledIndexedFunctionDefinitionBody, String> = (|| {
            let mut parameter_premises = Vec::with_capacity(2);
            let mut parameter_real_representations = HashMap::new();
            for parameter_index in 0..2 {
                let suffix = parameter_index + 1;
                let argument_name = format!("__arg{suffix}");
                let membership_name = format!("__arg{suffix}_in");
                let binding = parameter_bindings[parameter_index];
                let fact_id = parameter_fact_ids[parameter_index];
                self.environment_stack
                    .symbol_names
                    .insert(binding.id(), argument_name.clone());
                self.environment_stack
                    .fact_names
                    .insert(fact_id, membership_name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(fact_id, expected_parameter_facts[parameter_index].clone());
                let representative = format!("Litex.In.rep {argument_name} {membership_name}");
                let numeric_complex = format!("((((({representative}).val : ℕ)) : ℂ))");
                let numeric_real = format!("((((({representative}).val : ℕ)) : ℝ))");
                self.environment_stack
                    .numeric_representations
                    .insert(binding.id(), numeric_complex);
                self.environment_stack.numeric_integer_values.insert(
                    binding.id(),
                    format!("(((({representative}).val : ℕ)) : ℤ)"),
                );
                self.environment_stack.numeric_rational_values.insert(
                    binding.id(),
                    format!("(((({representative}).val : ℕ)) : ℚ)"),
                );
                self.environment_stack
                    .numeric_real_values
                    .insert(binding.id(), numeric_real.clone());
                parameter_real_representations.insert(binding.id(), numeric_real);
                parameter_premises.push(LeanLocalFactPremise::new(
                    fact_id,
                    expected_parameter_facts[parameter_index].clone(),
                ));
            }
            let mut domain_premises = Vec::with_capacity(2);
            for domain_index in 0..2 {
                let fact_id = domain_fact_ids[domain_index];
                let proof_name = if domain_index == 0 {
                    "__arg_domain.1"
                } else {
                    "__arg_domain.2"
                };
                self.environment_stack
                    .fact_names
                    .insert(fact_id, proof_name.into());
                self.environment_stack
                    .fact_propositions
                    .insert(fact_id, expected_domain_facts[domain_index].clone());
                domain_premises.push(LeanLocalFactPremise::new(
                    fact_id,
                    expected_domain_facts[domain_index].clone(),
                ));
            }
            let allowed_inference_sources = parameter_fact_ids
                .iter()
                .copied()
                .zip(expected_parameter_facts.iter().cloned())
                .chain(
                    domain_fact_ids
                        .iter()
                        .copied()
                        .zip(expected_domain_facts.iter().cloned()),
                )
                .collect::<Vec<_>>();
            self.install_standard_numeric_membership_inference_results_in_current_environment(
                &verification.assumption_infers,
                &allowed_inference_sources,
                "matrix index inference",
            )?;

            let mut installed_well_definedness_nodes = HashSet::new();
            for well_definedness in [
                verification.well_definedness.surface_set.as_ref(),
                verification.well_definedness.anonymous_function.as_ref(),
                verification.well_definedness.function_set.as_ref(),
            ] {
                install_object_well_definedness_store_results(
                    well_definedness,
                    &mut self.environment_stack,
                    &mut installed_well_definedness_nodes,
                )?;
            }

            let return_check = verification
                .return_check
                .factual_success()
                .ok_or_else(|| "matrix return check is not factual".to_string())?;
            if return_check.fact().to_string() != expected_return_check.to_string()
                || return_check.store.fact.to_string() != expected_return_check.to_string()
                || !return_check.store.infers.is_empty()
            {
                return Err("matrix return check changed its target or published effects".into());
            }
            if self
                .construct_lean_proof_from_direct_fact_result(return_check)?
                .is_none()
            {
                return Err(
                    "matrix return check has no direct recursive Result proof adapter".into(),
                );
            }
            let rendered_body = render_real_function_body_with_parameters(
                &lowered_body,
                &parameter_real_representations,
                &self.environment_stack,
            )?;
            Ok(CompiledIndexedFunctionDefinitionBody {
                function: function.clone(),
                source_body: source_body.clone(),
                lowered_body: lowered_body.clone(),
                value: format!(
                    "fun {{__alpha1 : Type}} (__arg1 : __alpha1) (__arg1_in : Litex.In __arg1 Litex.NPos) => fun {{__alpha2 : Type}} (__arg2 : __alpha2) (__arg2_in : Litex.In __arg2 Litex.NPos) => fun __arg_domain => ULift.up ({rendered_body})"
                ),
                parameter_premises,
                domain_premises,
            })
        })();
        self.environment_stack.pop_local_environment();
        let compiled_body = compiled_body?;

        if !result.common.infers.rule_applications.is_empty() {
            return Err("matrix definition retained unexpected outer typed infer rules".into());
        }
        let [surface_membership_store, defining_equality_store] =
            result.common.infers.store_fact_outputs.as_slice()
        else {
            return Err("matrix definition requires two ordered outer store outputs".into());
        };
        let function_object: Obj = Identifier::new_bound(
            statement.name().to_string(),
            statement.symbol_binding.as_ref(),
        )
        .into();
        let expected_surface_membership: Fact = InFact::new(
            function_object.clone(),
            statement.matrix_set.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        let expected_defining_equality: Fact = EqualFact::new(
            function_object.clone(),
            anonymous_function.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        if surface_membership_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_surface_membership.to_string()
        {
            return Err("matrix first outer store changed its surface membership".into());
        }
        let surface_membership_fact_id = surface_membership_store
            .fact_id
            .ok_or_else(|| "matrix surface membership store has no FactId".to_string())?;
        let [inferred_function_membership] = surface_membership_store.inferred_facts.as_slice()
        else {
            return Err("matrix surface membership must infer one function membership".into());
        };
        let [Some(function_membership_fact_id)] =
            surface_membership_store.inferred_fact_ids.as_slice()
        else {
            return Err("matrix inferred function membership has no FactId".into());
        };
        let (inferred_function_object, inferred_function_set) =
            membership_parts(inferred_function_membership)?;
        if !object_is_symbol(inferred_function_object, statement.symbol_binding.id()) {
            return Err("matrix inferred function membership changed its function".into());
        }
        let Obj::FnSet(inferred_function_set) = inferred_function_set else {
            return Err("matrix inferred membership does not retain a function set".into());
        };
        let inferred_function = LeanTargetFunctionTypeRepresentation::lower(inferred_function_set)?;
        if inferred_function.parameters.len() != 2
            || inferred_function.domain_facts.len() != 2
            || inferred_function.return_set != compiled_body.function.return_set
            || inferred_function
                .parameters
                .iter()
                .zip(compiled_body.function.parameters.iter())
                .any(|(inferred, expected)| inferred.set != expected.set)
        {
            return Err("matrix inferred function membership changed its signature".into());
        }
        let mut expected_domain_environment = self.environment_stack.clone();
        let mut inferred_domain_environment = self.environment_stack.clone();
        for parameter_index in 0..2 {
            let common_name = format!("__matrix_parameter{}", parameter_index + 1);
            let common_numeric = format!("__matrix_parameter{}_complex", parameter_index + 1);
            expected_domain_environment.symbol_names.insert(
                compiled_body.function.parameters[parameter_index].symbol_id,
                common_name.clone(),
            );
            expected_domain_environment.numeric_representations.insert(
                compiled_body.function.parameters[parameter_index].symbol_id,
                common_numeric.clone(),
            );
            inferred_domain_environment.symbol_names.insert(
                inferred_function.parameters[parameter_index].symbol_id,
                common_name,
            );
            inferred_domain_environment.numeric_representations.insert(
                inferred_function.parameters[parameter_index].symbol_id,
                common_numeric,
            );
        }
        for domain_index in 0..2 {
            if render_fact(
                &compiled_body.function.domain_facts[domain_index],
                &expected_domain_environment,
            )? != render_fact(
                &inferred_function.domain_facts[domain_index],
                &inferred_domain_environment,
            )? {
                return Err(format!(
                    "matrix inferred function membership changed bound clause {domain_index}"
                ));
            }
        }
        if defining_equality_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_defining_equality.to_string()
            || !defining_equality_store.inferred_facts.is_empty()
            || !defining_equality_store.inferred_fact_ids.is_empty()
        {
            return Err("matrix second outer store changed its defining equality".into());
        }
        let defining_equality_fact_id = defining_equality_store
            .fact_id
            .ok_or_else(|| "matrix defining equality store has no FactId".to_string())?;
        if [
            surface_membership_fact_id,
            *function_membership_fact_id,
            defining_equality_fact_id,
        ]
        .into_iter()
        .collect::<HashSet<_>>()
        .len()
            != 3
        {
            return Err("matrix outer stores reused a FactId across semantic roles".into());
        }

        let name = lean_identifier(statement.name());
        let function_value_name = format!("(@{name})");
        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), function_value_name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for matrix `{}`",
                statement.name()
            ));
        }
        let function_type = render_function_type(&compiled_body.function, &self.environment_stack)?;
        let rendered_function_set =
            render_function_set(&compiled_body.function, &self.environment_stack)?;
        self.declarations.push(format!(
            "noncomputable def {name} : {function_type} :=\n  {}",
            compiled_body.value
        ));

        let surface_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {surface_theorem_name} : {} := by\n  exact Litex.In.own {} {function_value_name}",
            render_fact(&expected_surface_membership, &self.environment_stack)?,
            render_obj(&statement.matrix_set.clone().into(), &self.environment_stack)?,
        ));
        self.environment_stack
            .fact_names
            .insert(surface_membership_fact_id, surface_theorem_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(surface_membership_fact_id, expected_surface_membership);
        self.environment_stack.function_bindings.insert(
            surface_membership_fact_id,
            FunctionBinding {
                symbol_id: statement.symbol_binding.id(),
                function: compiled_body.function.clone(),
                membership_proof_name: surface_theorem_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let function_membership_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {function_membership_theorem_name} : {} := by\n  exact Litex.In.own {rendered_function_set} {function_value_name}",
            render_fact(inferred_function_membership, &self.environment_stack)?,
        ));
        self.environment_stack.fact_names.insert(
            *function_membership_fact_id,
            function_membership_theorem_name.clone(),
        );
        self.environment_stack.fact_propositions.insert(
            *function_membership_fact_id,
            inferred_function_membership.clone(),
        );
        self.environment_stack.function_bindings.insert(
            *function_membership_fact_id,
            FunctionBinding {
                symbol_id: statement.symbol_binding.id(),
                function: compiled_body.function.clone(),
                membership_proof_name: function_membership_theorem_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let equality_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {equality_theorem_name} : Litex.Same {function_value_name} ({} : {function_type}) := by\n  unfold {name}\n  exact Litex.Same.refl ({} : {function_type})",
            compiled_body.value, compiled_body.value
        ));
        self.environment_stack
            .fact_names
            .insert(defining_equality_fact_id, equality_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(defining_equality_fact_id, expected_defining_equality);
        self.environment_stack.named_function_definitions.insert(
            defining_equality_fact_id,
            NamedFunctionDefinitionBinding {
                symbol_id: statement.symbol_binding.id(),
                name,
                function: compiled_body.function,
                source_body: compiled_body.source_body,
                body: compiled_body.lowered_body,
                native_body_carrier: NativeFunctionBodyCarrier::Real,
                parameter_premises: compiled_body.parameter_premises,
                domain_premises: compiled_body.domain_premises,
                well_definedness: StmtResultWellDefinednessToLeanCompilationContext::default(),
            },
        );
        self.next_fact_name_index += 1;
        Ok(true)
    }

    pub(super) fn compile_def_prop_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDefPropStmtResult,
    ) -> Result<(), String> {
        if !result.common.infers.is_empty() {
            return Err("concrete predicate definition unexpectedly retained fact effects".into());
        }
        let definition = &result.statement;
        if definition.iff_facts.is_empty() {
            return Err("compiler rejects a bodyless concrete `prop`".into());
        }
        if self
            .environment_stack
            .predicate_bindings
            .contains_key(&definition.name)
        {
            return Err(format!(
                "duplicate compiler predicate definition `{}`",
                definition.name
            ));
        }
        let local = result.run_in_local_env.as_ref().ok_or_else(|| {
            "compiler rejects a concrete `prop` Result without verified local evidence".to_string()
        })?;
        if local.body.len() != definition.iff_facts.len()
            || local.binder.parameter_groups.len() != definition.typed_parameters.groups.len()
        {
            return Err("concrete predicate Result changed its binder or body arity".into());
        }
        for (retained, source) in local.body.iter().zip(definition.iff_facts.iter()) {
            if retained.proposition.to_string() != source.to_string()
                || retained.store.fact.to_string() != source.to_string()
                || retained.store.fact_id.is_none()
            {
                return Err(
                    "concrete predicate Result changed a verified body clause or its local FactId"
                        .into(),
                );
            }
        }
        if let Some(kind) = checked_real_sequence_definition_kind(definition) {
            // The semantic shortcut is allowed only after the compiler has
            // validated and indexed the complete verifier-owned binder/body
            // WD tree. Proof slots below local binders remain deferred to
            // their lexical consumers; the exact source contract selects the
            // Mathlib lowering but never replaces Result evidence.
            self.collect_def_prop_well_definedness_to_lean_compilation_context(local)?;
            return self.compile_checked_real_sequence_definition(definition, kind);
        }

        let mut definition_environment = self.environment_stack.clone();
        definition_environment.push_inherited_environment();
        definition_environment.well_definedness =
            Some(self.construct_def_prop_well_definedness_to_lean_compilation_context(local)?);
        let mut binders = Vec::new();
        let mut requirements = Vec::new();
        let mut parameter_count = 0;
        let dependent_parameter_evidence = definition.typed_parameters.groups.iter().any(|group| {
            matches!(
                &group.param_type,
                ParamType::Obj(Obj::FnSet(_) | Obj::FiniteSeqSet(_) | Obj::SeqSet(_))
            )
        });
        for (group, retained_group) in definition
            .typed_parameters
            .groups
            .iter()
            .zip(local.binder.parameter_groups.iter())
        {
            if group.param_type.to_string() != retained_group.parameter_type.to_string()
                || group.params.len() != retained_group.parameters.len()
            {
                return Err("concrete predicate Result changed a typed parameter group".into());
            }
            for (binding, retained_parameter) in
                group.params.iter().zip(retained_group.parameters.iter())
            {
                parameter_count += 1;
                let parameter_name = lean_identifier(binding.name());
                match &group.param_type {
                    ParamType::Set(_) => {
                        binders.push(format!("({parameter_name} : Litex.Set)"));
                        definition_environment
                            .symbol_names
                            .insert(binding.id(), parameter_name);
                        // The source Result still owns and validates
                        // `$is_set(parameter)`. In Lean this obligation is
                        // already discharged by the binder's `Litex.Set`
                        // type, so its proposition/proof bridge is `True`.
                        requirements.push("True".to_string());
                    }
                    ParamType::Obj(set) => {
                        let carrier_name = format!("__carrier{parameter_count}");
                        let rendered_set = render_obj(set, &definition_environment)?;
                        binders.push(format!("{{{carrier_name} : Type}}"));
                        binders.push(format!("({parameter_name} : {carrier_name})"));
                        definition_environment
                            .symbol_names
                            .insert(binding.id(), parameter_name.clone());
                        let requirement = format!("Litex.In {parameter_name} {rendered_set}");
                        requirements.push(requirement);
                        if dependent_parameter_evidence {
                            let proof_name = format!("__type{parameter_count}");
                            install_parameter_fact_aliases(
                                binding.id(),
                                &retained_parameter.proposition,
                                &proof_name,
                                set,
                                &mut definition_environment,
                            )?;
                        }
                    }
                    unsupported => {
                        return Err(format!(
                            "concrete predicate compiler does not support parameter type `{unsupported}`"
                        ));
                    }
                }
            }
        }
        let clauses = definition
            .iff_facts
            .iter()
            .map(|fact| render_fact(fact, &definition_environment))
            .collect::<Result<Vec<_>, _>>()?;
        let body = if dependent_parameter_evidence {
            let evidence_binders = requirements
                .iter()
                .enumerate()
                .map(|(index, requirement)| format!("(__type{} : {requirement})", index + 1))
                .collect::<Vec<_>>()
                .join(" ");
            format!("\u{2203} {evidence_binders}, {}", conjunction(&clauses))
        } else {
            let mut components = requirements;
            components.extend(clauses);
            conjunction(&components)
        };
        let lean_name = lean_identifier(&definition.name);
        self.declarations.push(format!(
            "def {lean_name} {} : Prop :=\n  {}",
            binders.join(" "),
            body
        ));
        self.environment_stack.predicate_bindings.insert(
            definition.name.clone(),
            PredicateBinding {
                lean_name,
                parameter_count,
                requirement_count: parameter_count,
                clause_count: definition.iff_facts.len(),
                dependent_parameter_evidence,
                definition: Some(definition.clone()),
            },
        );
        Ok(())
    }

    fn compile_checked_real_sequence_definition(
        &mut self,
        definition: &DefPropStmt,
        kind: CheckedRealSequenceDefinitionKind,
    ) -> Result<(), String> {
        let mut binders = Vec::new();
        let mut arguments = Vec::new();
        let mut requirements = Vec::new();
        for (index, (binding, param_type)) in definition
            .typed_parameters
            .collect_param_bindings_with_types()
            .iter()
            .enumerate()
        {
            let suffix = index + 1;
            let name = lean_identifier(binding.name());
            let ParamType::Obj(set) = param_type else {
                return Err("checked real-sequence definitions require object parameters".into());
            };
            let universe = if matches!(set, Obj::SeqSet(_) | Obj::FnSet(_)) {
                "Type 1"
            } else {
                "Type"
            };
            binders.push(format!("{{__carrier{suffix} : {universe}}}"));
            binders.push(format!("({name} : __carrier{suffix})"));
            arguments.push(name.clone());
            requirements.push(format!(
                "(__type{suffix} : Litex.In {name} {})",
                render_obj(set, &self.environment_stack)?
            ));
        }

        let representative =
            |index: usize| format!("(Litex.In.rep {} __type{})", arguments[index], index + 1);
        let semantic_body = match kind {
            CheckedRealSequenceDefinitionKind::TailClose => format!(
                "Litex.Rules.RealSequenceTailClose {} {} (Litex.Rules.positiveRealValue {}) (Litex.Rules.positiveNaturalZeroIndex {})",
                representative(0),
                representative(1),
                representative(2),
                representative(3),
            ),
            CheckedRealSequenceDefinitionKind::ConvergesTo => format!(
                "Litex.Rules.RealSequenceConvergesTo {} {}",
                representative(0),
                representative(1),
            ),
            CheckedRealSequenceDefinitionKind::Convergent => format!(
                "Litex.Rules.RealSequenceConvergent {}",
                representative(0),
            ),
            CheckedRealSequenceDefinitionKind::CauchyTail => format!(
                "Litex.Rules.RealSequenceCauchyTail {} (Litex.Rules.positiveRealValue {}) (Litex.Rules.positiveNaturalZeroIndex {})",
                representative(0),
                representative(1),
                representative(2),
            ),
            CheckedRealSequenceDefinitionKind::Cauchy => format!(
                "Litex.Rules.RealSequenceCauchy {}",
                representative(0),
            ),
        };
        let lean_name = lean_identifier(&definition.name);
        self.declarations.push(format!(
            "def {lean_name} {} : Prop :=\n  \u{2203} {}, {semantic_body}",
            binders.join(" "),
            requirements.join(" "),
        ));
        self.environment_stack.predicate_bindings.insert(
            definition.name.clone(),
            PredicateBinding {
                lean_name,
                parameter_count: arguments.len(),
                requirement_count: arguments.len(),
                clause_count: definition.iff_facts.len(),
                dependent_parameter_evidence: true,
                definition: Some(definition.clone()),
            },
        );
        Ok(())
    }

    pub(super) fn compile_def_abstract_prop_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDefAbstractPropStmtResult,
    ) -> Result<(), String> {
        if !result.common.infers.is_empty() {
            return Err("abstract predicate definition unexpectedly retained fact effects".into());
        }
        construct_lean_source_parts_for_abstract_predicate_definition(
            &result.statement.name,
            &result.statement.params,
            &mut self.declarations,
            &mut self.environment_stack,
        )
    }

    pub(super) fn compile_by_definition_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByDefStmtResult,
    ) -> Result<bool, String> {
        let Some(proof) = self.construct_lean_proof_from_by_definition_stmt_result(result)? else {
            return Ok(false);
        };
        if result
            .common
            .infers
            .rule_applications
            .iter()
            .any(|application| !defined_predicate_infer_rule(&application.rule))
        {
            return Ok(false);
        }
        if result.common.infers.store_fact_outputs.is_empty() {
            let target_was_already_visible = self
                .environment_stack
                .fact_propositions
                .values()
                .any(|visible| visible.to_string() == proof.target.fact.to_string());
            if !target_was_already_visible {
                return Err(
                    "by-definition target was neither stored nor already compiler-visible".into(),
                );
            }
            return Ok(true);
        }
        let [output] = result.common.infers.store_fact_outputs.as_slice() else {
            return Err("by-definition target retained more than one direct store output".into());
        };
        if output.itself_and_why_itself_is_stored.0.to_string() != proof.target.fact.to_string()
            || output.inferred_facts.len() != output.inferred_fact_ids.len()
        {
            return Err("by-definition target changed its direct or inferred effects".into());
        }
        let fact_id = output
            .fact_id
            .ok_or_else(|| "by-definition target store has no FactId".to_string())?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {} := by\n  exact {}",
            proof.target.proposition, proof.target.proof_expression
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, proof.target.fact);
        self.next_fact_name_index += 1;

        if !result.common.infers.rule_applications.is_empty() {
            self.compile_defined_predicate_inference_results_in_current_environment(
                &result.common.infers,
                DefinedPredicateInferenceConclusionPublication::PersistentLeanTheorem,
            )?;
            validate_flattened_inferred_fact_ids_are_visible(
                &result.common.infers,
                &self.environment_stack,
                "by-definition Result",
            )?;
            return Ok(true);
        }

        for (inferred_fact, inferred_fact_id) in output
            .inferred_facts
            .iter()
            .zip(output.inferred_fact_ids.iter())
        {
            let inferred_fact_id = inferred_fact_id.ok_or_else(|| {
                format!("by-definition inferred fact `{inferred_fact}` has no retained FactId")
            })?;
            if self
                .environment_stack
                .fact_propositions
                .contains_key(&inferred_fact_id)
            {
                resolve_fact_citation(&inferred_fact_id, inferred_fact, &self.environment_stack)?;
                continue;
            }
            let component = proof
                .components
                .iter()
                .find(|component| {
                    component.retained_fact_id == Some(inferred_fact_id)
                        && component.fact.to_string() == inferred_fact.to_string()
                })
                .ok_or_else(|| {
                    format!(
                        "by-definition inferred fact `{inferred_fact}` has no matching recursive child proof"
                    )
                })?;
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {theorem_name} : {} := by\n  exact {}",
                component.proposition, component.proof_expression
            ));
            self.environment_stack
                .fact_names
                .insert(inferred_fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(inferred_fact_id, component.fact.clone());
            self.next_fact_name_index += 1;
        }
        Ok(true)
    }

    /// `Combine`: validate each parameter and definition-clause child in
    /// source order, then fold those exact proofs into the predicate.
    pub(super) fn construct_lean_proof_from_by_definition_stmt_result(
        &mut self,
        result: &SuccessByDefStmtResult,
    ) -> Result<Option<CompiledByDefinitionProofBody>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        if !verification.concrete_user_prop {
            return Ok(None);
        }
        let Some(definition) = &verification.definition else {
            return Err("by-definition Result lost its concrete predicate definition".into());
        };
        if definition.iff_facts.is_empty() {
            return Err("by-definition Result retained a bodyless concrete predicate".into());
        }
        let target: Fact = result.statement.fact.clone().into();
        let Fact::AtomicFact(AtomicFact::NormalAtomicFact(target_predicate)) = &target else {
            return Err("concrete by-definition target is not a predicate application".into());
        };
        if verification.prop != target_predicate.predicate.to_string()
            || verification.stored_fact != target.to_string()
            || verification.arguments
                != target_predicate
                    .body
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
            || verification.definition_clauses
                != verification
                    .definition_clause_facts
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
        {
            return Err("by-definition Result changed its target, arguments, or clauses".into());
        }
        let binding = self
            .environment_stack
            .predicate_bindings
            .get(&definition.name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "by-definition references unavailable predicate `{}`",
                    definition.name
                )
            })?;
        let Some(active_definition) = &binding.definition else {
            return Err("by-definition selected an abstract predicate binding".into());
        };
        if active_definition.to_string() != definition.to_string()
            || target_predicate.predicate.to_string() != definition.name
        {
            return Err(
                "by-definition Result does not match the active predicate definition".into(),
            );
        }
        let Some(argument_verification) = &verification.argument_verification else {
            return Err("by-definition Result has no parameter-check children".into());
        };
        if !argument_verification.infers.is_empty() {
            return Ok(None);
        }
        if argument_verification.checks.len() != binding.requirement_count
            || verification.definition_clause_facts.len() != binding.clause_count
            || verification.clause_checks.len() != binding.clause_count
        {
            return Err("by-definition Result changed its component arity".into());
        }

        let expected_components =
            instantiated_predicate_components(&target, &binding, &self.environment_stack)?;
        if expected_components.len() != binding.requirement_count + binding.clause_count {
            return Err("active predicate definition produced an invalid component arity".into());
        }
        let mut components = Vec::with_capacity(expected_components.len());
        for (component_index, check) in argument_verification.checks.iter().enumerate() {
            let check = check
                .factual_success()
                .ok_or_else(|| "by-definition parameter child is not factual".to_string())?;
            validate_scoped_fact_check_result(
                check,
                &check.fact(),
                &format!("by-definition parameter check {component_index}"),
            )?;
            if render_fact(&check.fact(), &self.environment_stack)?
                != expected_components[component_index]
            {
                return Err(format!(
                    "by-definition parameter check {component_index} changed its expected fact"
                ));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(check)? else {
                return Ok(None);
            };
            components.push(CompiledByDefinitionComponentProofBody {
                fact: check.fact(),
                retained_fact_id: check.store.fact_id,
                proposition: expected_components[component_index].clone(),
                proof_expression: proof,
            });
        }
        for (clause_index, (retained_clause, check)) in verification
            .definition_clause_facts
            .iter()
            .zip(verification.clause_checks.iter())
            .enumerate()
        {
            let check = check
                .factual_success()
                .ok_or_else(|| "by-definition clause child is not factual".to_string())?;
            if check.fact().to_string() != retained_clause.to_string() {
                return Err(format!(
                    "by-definition clause check {clause_index} changed its retained fact"
                ));
            }
            validate_scoped_fact_check_result(
                check,
                retained_clause,
                &format!("by-definition clause check {clause_index}"),
            )?;
            let component_index = binding.requirement_count + clause_index;
            if render_fact(retained_clause, &self.environment_stack)?
                != expected_components[component_index]
            {
                return Err(format!(
                    "by-definition clause check {clause_index} changed its expected fact"
                ));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(check)? else {
                return Ok(None);
            };
            components.push(CompiledByDefinitionComponentProofBody {
                fact: retained_clause.clone(),
                retained_fact_id: check.store.fact_id,
                proposition: expected_components[component_index].clone(),
                proof_expression: proof,
            });
        }
        if components.is_empty() {
            return Err("by-definition Result retained no proof components".into());
        }
        let target_proof_expression = format!(
            "(by\n  unfold {}\n  exact ⟨{}⟩)",
            binding.lean_name,
            components
                .iter()
                .map(|component| component.proof_expression.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        );
        Ok(Some(CompiledByDefinitionProofBody {
            target: CompiledFactProofBody {
                fact: target.clone(),
                proposition: render_fact(&target, &self.environment_stack)?,
                proof_expression: target_proof_expression,
            },
            components,
        }))
    }

    pub(super) fn compile_trust_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessTrustStmtResult,
    ) -> Result<bool, String> {
        if result.statement.facts.is_empty() {
            return Err("explicit source `trust` retained no propositions".into());
        }
        if result.common.infers.store_fact_outputs.len() != result.statement.facts.len()
            || result
                .common
                .infers
                .rule_applications
                .iter()
                .any(|application| !defined_predicate_infer_rule(&application.rule))
            || result
                .common
                .infers
                .store_fact_outputs
                .iter()
                .any(|store| store.inferred_facts.len() != store.inferred_fact_ids.len())
        {
            return Ok(false);
        }
        for (fact, store) in result
            .statement
            .facts
            .iter()
            .zip(result.common.infers.store_fact_outputs.iter())
        {
            if store.itself_and_why_itself_is_stored.0.to_string() != fact.to_string() {
                return Err("trusted fact order changed between statement and store Result".into());
            }
            let fact_id = store
                .fact_id
                .ok_or_else(|| "trusted source fact has no FactId".to_string())?;
            let proposition = match fact {
                Fact::ForallFact(forall) => {
                    render_forall_fact_type(forall, &self.environment_stack)?
                }
                _ => render_fact(fact, &self.environment_stack)?,
            };
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations
                .push(format!("axiom {theorem_name} : {proposition}"));
            self.environment_stack
                .fact_names
                .insert(fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, fact.clone());
            self.next_fact_name_index += 1;
        }
        self.compile_defined_predicate_inference_results_in_current_environment(
            &result.common.infers,
            DefinedPredicateInferenceConclusionPublication::PersistentLeanTheorem,
        )?;
        validate_flattened_inferred_fact_ids_are_visible(
            &result.common.infers,
            &self.environment_stack,
            "explicit source trust",
        )?;
        Ok(true)
    }

    /// `Combine`: declare each explicitly trusted object in source order,
    /// publish its exact parameter-membership FactId, then publish the
    /// statement's attached trusted facts. This direct slice accepts ordinary
    /// object carriers whose stores have no inferred siblings. Refined/set
    /// bindings and typed infer children remain separate migration routes.
    pub(super) fn compile_trust_have_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessTrustHaveStmtResult,
    ) -> Result<bool, String> {
        if !result.common.infers.rule_applications.is_empty()
            || result.common.infers.store_fact_outputs.iter().any(|store| {
                !store.inferred_facts.is_empty() || !store.inferred_fact_ids.is_empty()
            })
        {
            return Ok(false);
        }

        let mut parameters = Vec::new();
        for group in &result.statement.param_def.groups {
            let ParamType::Obj(carrier) = &group.param_type else {
                return Ok(false);
            };
            if matches!(
                carrier,
                Obj::FiniteSeqSet(_) | Obj::SeqSet(_) | Obj::MatrixSet(_) | Obj::StructObj(_)
            ) {
                return Ok(false);
            }
            for binding in &group.params {
                let object: Obj =
                    Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into();
                let membership: Fact =
                    InFact::new(object, carrier.clone(), result.statement.line_file.clone()).into();
                parameters.push((binding, carrier, membership));
            }
        }

        let expected_store_count = parameters.len() + result.statement.facts.len();
        if result.common.infers.store_fact_outputs.len() != expected_store_count {
            return Err(format!(
                "trust-have retained {} store outputs for {expected_store_count} parameter/fact effects",
                result.common.infers.store_fact_outputs.len()
            ));
        }
        for (index, ((_, _, expected), store)) in parameters
            .iter()
            .zip(result.common.infers.store_fact_outputs.iter())
            .enumerate()
        {
            if store.itself_and_why_itself_is_stored.0.to_string() != expected.to_string() {
                return Err(format!(
                    "trust-have parameter store {index} changed `{expected}` to `{}`",
                    store.itself_and_why_itself_is_stored.0
                ));
            }
            if store.fact_id.is_none() {
                return Err(format!("trust-have parameter store {index} has no FactId"));
            }
        }
        for (index, (expected, store)) in result
            .statement
            .facts
            .iter()
            .zip(
                result
                    .common
                    .infers
                    .store_fact_outputs
                    .iter()
                    .skip(parameters.len()),
            )
            .enumerate()
        {
            if store.itself_and_why_itself_is_stored.0.to_string() != expected.to_string() {
                return Err(format!(
                    "trust-have attached fact store {index} changed `{expected}` to `{}`",
                    store.itself_and_why_itself_is_stored.0
                ));
            }
            if store.fact_id.is_none() {
                return Err(format!(
                    "trust-have attached fact store {index} has no FactId"
                ));
            }
        }

        for (index, (binding, carrier, membership)) in parameters.iter().enumerate() {
            let store = &result.common.infers.store_fact_outputs[index];
            let fact_id = store.fact_id.expect("validated trust-have FactId");
            let name = lean_identifier(binding.name());
            let rendered_carrier = render_obj(carrier, &self.environment_stack)?;
            let function = match carrier {
                Obj::FnSet(function_set) => {
                    Some(LeanTargetFunctionTypeRepresentation::lower(function_set)?)
                }
                _ => None,
            };
            let declared_type = if let Some(function) = &function {
                render_function_type(function, &self.environment_stack)?
            } else {
                format!("{rendered_carrier}.Carrier")
            };
            let rendered_value = if function.is_some() {
                format!("(@{name})")
            } else {
                name.clone()
            };
            if self
                .environment_stack
                .symbol_names
                .insert(binding.id(), rendered_value.clone())
                .is_some()
            {
                return Err(format!(
                    "trust-have reused compiler SymbolId for `{}`",
                    binding.name()
                ));
            }
            self.declarations
                .push(format!("axiom {name} : {declared_type}"));

            let proposition = render_fact(membership, &self.environment_stack)?;
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {theorem_name} : {proposition} := by\n  exact Litex.In.own {rendered_carrier} {rendered_value}"
            ));
            self.environment_stack
                .fact_names
                .insert(fact_id, theorem_name.clone());
            self.environment_stack
                .fact_propositions
                .insert(fact_id, membership.clone());
            if let Some(function) = function {
                self.environment_stack.function_bindings.insert(
                    fact_id,
                    FunctionBinding {
                        symbol_id: binding.id(),
                        function,
                        membership_proof_name: theorem_name,
                        direct: true,
                    },
                );
            }
            self.next_fact_name_index += 1;
        }

        for (fact, store) in result.statement.facts.iter().zip(
            result
                .common
                .infers
                .store_fact_outputs
                .iter()
                .skip(parameters.len()),
        ) {
            let fact_id = store.fact_id.expect("validated trust-have FactId");
            let proposition = match fact {
                Fact::ForallFact(forall) => {
                    render_forall_fact_type(forall, &self.environment_stack)?
                }
                _ => render_fact(fact, &self.environment_stack)?,
            };
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations
                .push(format!("axiom {theorem_name} : {proposition}"));
            self.environment_stack
                .fact_names
                .insert(fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, fact.clone());
            self.next_fact_name_index += 1;
        }
        Ok(true)
    }

    /// `Leaf`: preserve an explicit Litex source axiom as an explicit Lean
    /// axiom and register the exact stored forall FactId. This is a source
    /// trust boundary, not a compiler-invented escape hatch.
    pub(super) fn compile_source_axiom_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessAxiomStmtResult,
    ) -> Result<(), String> {
        let axiom_fact: Fact = result.statement.forall_fact.clone().into();
        let well_definedness = result
            .well_definedness
            .as_ref()
            .ok_or_else(|| "source axiom retained no well-definedness Result".to_string())?;
        let Some(SuccessVerifyFactWellDefinedProofResult::ForallFact(recursive)) =
            well_definedness.recursive.as_deref()
        else {
            return Err("source axiom retained no recursive forall well-definedness".into());
        };
        if recursive.statement.to_string() != result.statement.forall_fact.to_string() {
            return Err("source axiom well-definedness changed its forall proposition".into());
        }
        if !result.common.infers.rule_applications.is_empty() {
            return Err("source axiom retained unexpected typed inference rules".into());
        }
        let [store] = result.common.infers.store_fact_outputs.as_slice() else {
            return Err("source axiom must retain exactly one store effect".into());
        };
        if store.itself_and_why_itself_is_stored.0.to_string() != axiom_fact.to_string()
            || !store.inferred_facts.is_empty()
            || !store.inferred_fact_ids.is_empty()
        {
            return Err(
                "source axiom changed its stored proposition or inferred consequences".into(),
            );
        }
        let fact_id = store
            .fact_id
            .ok_or_else(|| "source axiom store has no FactId".to_string())?;
        let proposition =
            render_forall_fact_type(&result.statement.forall_fact, &self.environment_stack)?;
        let axiom_name = lean_identifier(&result.statement.name);
        self.declarations
            .push(format!("axiom {axiom_name} : {proposition}"));
        self.environment_stack
            .fact_names
            .insert(fact_id, axiom_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, axiom_fact);
        Ok(())
    }

    pub(super) fn compile_let_obj_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessLetObjStmtResult,
    ) -> Result<(), String> {
        let statement = &result.statement;
        let source_name = statement.symbol_binding.name();
        let lean_name = lean_identifier(source_name);
        let rendered_value = render_obj(&statement.value, &self.environment_stack)?;
        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), lean_name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for `{source_name}`"
            ));
        }
        self.declarations
            .push(format!("noncomputable def {lean_name} := {rendered_value}"));

        if !result.common.infers.rule_applications.is_empty() {
            return Err("let-object definition retained unexpected typed inference rules".into());
        }
        let [store] = result.common.infers.store_fact_outputs.as_slice() else {
            return Err("let-object definition must retain exactly one defining store".into());
        };
        if !store.inferred_facts.is_empty() || !store.inferred_fact_ids.is_empty() {
            return Err("let-object defining store retained unexpected inferred facts".into());
        }
        let defined_object: Obj =
            Identifier::new_bound(source_name.to_string(), statement.symbol_binding.as_ref())
                .into();
        let defining_equality: Fact = EqualFact::new(
            defined_object,
            statement.value.clone(),
            statement.line_file.clone(),
        )
        .into();
        if store.itself_and_why_itself_is_stored.0.to_string() != defining_equality.to_string() {
            return Err("let-object result changed its defining equality".into());
        }
        let defining_equality_fact_id = store
            .fact_id
            .ok_or_else(|| "let-object defining equality has no FactId".to_string())?;
        let rendered_equality = render_fact(&defining_equality, &self.environment_stack)?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {rendered_equality} := by\n  unfold {lean_name}\n  exact Litex.Same.refl {rendered_value}"
        ));
        self.environment_stack
            .fact_names
            .insert(defining_equality_fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(defining_equality_fact_id, defining_equality.clone());
        self.environment_stack
            .transparent_object_definitions
            .insert(
                statement.symbol_binding.id(),
                CompilerTransparentObjectDefinition {
                    value: statement.value.clone(),
                    defining_equality,
                    defining_equality_fact_id,
                },
            );
        self.environment_stack
            .runtime_resolved_numeric_substitutions
            .insert(
                statement.symbol_binding.substitution_key(),
                statement.value.clone(),
            );
        self.environment_stack
            .runtime_resolved_numeric_definition_names
            .push(lean_name);
        self.next_fact_name_index += 1;
        Ok(())
    }

    pub(super) fn compile_try_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessTryStmtResult,
    ) -> Result<(), String> {
        let proof = result
            .proof
            .as_ref()
            .ok_or_else(|| "successful `try` retained no child results".to_string())?;
        if proof.proof_steps.len() != result.statement.proof.len() {
            return Err("successful `try` changed its source statement order".into());
        }
        for child in &proof.proof_steps {
            self.compile_stmt_result(child)?;
        }
        Ok(())
    }

    /// `Wrap`: a checked numeric `eval` publishes the evaluator-owned
    /// equality under the exact FactId assigned by its store layer. Runtime
    /// algorithms without a recursive computation Result remain fail-closed.
    pub(super) fn compile_eval_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessEvalStmtResult,
    ) -> Result<(), String> {
        match &result.execution {
            SuccessEvalStmtExecutionResult::SkippedByTrustedExecution => {
                if !result.common.infers.is_empty() {
                    return Err("trusted `eval` unexpectedly published effects".into());
                }
                return Ok(());
            }
            SuccessEvalStmtExecutionResult::Evaluated(execution) => {
                if obj_equality_key(&execution.source_object)
                    != obj_equality_key(&result.statement.obj_to_eval)
                {
                    return Err("eval execution changed its source object".into());
                }
                let evaluation = execution
                    .recursive_numeric_evaluation
                    .as_ref()
                    .ok_or_else(|| {
                        "StmtResultToLeanCompiler cannot compile an eval runtime algorithm without a recursive computation Result"
                            .to_string()
                    })?;
                validate_success_evaluate_obj_result(evaluation)?;
                if obj_equality_key(&evaluation.expression)
                    != obj_equality_key(&execution.source_object)
                    || obj_equality_key(&Obj::Number(evaluation.value.clone()))
                        != obj_equality_key(&execution.evaluated_object)
                {
                    return Err("eval recursive computation changed its input or output".into());
                }
            }
        }

        if !result.common.infers.rule_applications.is_empty() {
            return Err("numeric eval retained unexpected typed inference applications".into());
        }
        let [store] = result.common.infers.store_fact_outputs.as_slice() else {
            return Err("numeric eval must retain exactly one equality store".into());
        };
        if !store.inferred_facts.is_empty() || !store.inferred_fact_ids.is_empty() {
            return Err("numeric eval equality retained unexpected inferred consequences".into());
        }
        let SuccessEvalStmtExecutionResult::Evaluated(execution) = &result.execution else {
            unreachable!("trusted eval returned before store validation")
        };
        let expected_equality: Fact = EqualFact::new(
            execution.source_object.clone(),
            execution.evaluated_object.clone(),
            result.statement.line_file.clone(),
        )
        .into();
        if store.itself_and_why_itself_is_stored.0.to_string() != expected_equality.to_string() {
            return Err("numeric eval store changed its evaluated equality".into());
        }
        let fact_id = store
            .fact_id
            .ok_or_else(|| "numeric eval equality store has no FactId".to_string())?;
        let proposition = render_fact(&expected_equality, &self.environment_stack)?;
        render_obj(&execution.source_object, &self.environment_stack)?;
        render_obj(&execution.evaluated_object, &self.environment_stack)?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {proposition} := by\n  exact Litex.Same.ofEq (by norm_num [Litex.tupleDim, Litex.TupleShape.dimension])"
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, expected_equality);
        self.next_fact_name_index += 1;
        Ok(())
    }
}

#[derive(Clone, Copy)]
pub(super) enum CheckedRealSequenceDefinitionKind {
    TailClose,
    ConvergesTo,
    Convergent,
    CauchyTail,
    Cauchy,
}

pub(super) fn checked_real_sequence_definition_kind(
    definition: &DefPropStmt,
) -> Option<CheckedRealSequenceDefinitionKind> {
    let mut statement = without_bound_symbol_display_ids(&definition.to_string());
    for local_name in [
        "is_sequence_tail_close_to_limit",
        "converges_to",
        "is_cauchy_tail",
    ] {
        let qualified_suffix = format!("::{local_name}");
        while let Some(suffix_start) = statement.find(&qualified_suffix) {
            let dollar = statement[..suffix_start].rfind('$')?;
            statement.replace_range(dollar..suffix_start + 2, "$ ");
            statement = statement.replace("$ ", "$");
        }
    }
    let expected = match definition.name.as_str() {
        "is_sequence_tail_close_to_limit" => (
            CheckedRealSequenceDefinitionKind::TailClose,
            "prop is_sequence_tail_close_to_limit(a seq(R), L R, epsilon R+, n0 N+):\n    forall n N+:\n        n >= n0\n        =>:\n            abs (a(n) - L) < epsilon",
        ),
        "converges_to" => (
            CheckedRealSequenceDefinitionKind::ConvergesTo,
            "prop converges_to(a seq(R), L R):\n    forall epsilon R+:\n        exist n0 N+ st {$is_sequence_tail_close_to_limit(a, L, epsilon, n0)}",
        ),
        "is_convergent_sequence" => (
            CheckedRealSequenceDefinitionKind::Convergent,
            "prop is_convergent_sequence(a seq(R)):\n    exist L R st {$converges_to(a, L)}",
        ),
        "is_cauchy_tail" => (
            CheckedRealSequenceDefinitionKind::CauchyTail,
            "prop is_cauchy_tail(a seq(R), epsilon R+, n0 N+):\n    forall m, n N+:\n        m >= n0\n        n >= n0\n        =>:\n            abs (a(m) - a(n)) < epsilon",
        ),
        "is_cauchy_sequence" => (
            CheckedRealSequenceDefinitionKind::Cauchy,
            "prop is_cauchy_sequence(a seq(R)):\n    forall epsilon R+:\n        exist n0 N+ st {$is_cauchy_tail(a, epsilon, n0)}",
        ),
        _ => return None,
    };
    (statement == expected.1).then_some(expected.0)
}
