//! Matrix declarations.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: consume four outer row/column bound checks, enter one local
    /// Result layer containing two parameter stores, two domain-premise
    /// stores, and the recursive return check, then publish only the matrix's
    /// persistent facts after that compiler environment has been popped.
    pub(in super::super) fn compile_have_matrix_stmt_result_to_lean_source(
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
}
