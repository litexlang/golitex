//! Sequence and finite-sequence declarations.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: validate the three named WD children, enter the retained
    /// positive-natural index scope, install its exact parameter FactId,
    /// consume the recursive return-check proof there, and pop the local
    /// compiler environment before publishing the sequence's three outer
    /// facts. No compiler scope is reconstructed from Runtime state.
    pub(in super::super) fn compile_have_sequence_stmt_result_to_lean_source(
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
    pub(in super::super) fn compile_have_finite_sequence_stmt_result_to_lean_source(
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
}
