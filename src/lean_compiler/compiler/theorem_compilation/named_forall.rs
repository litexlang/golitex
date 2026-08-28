//! Named universal statement compilation.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_named_forall_statement_result_to_lean_source(
        &mut self,
        verification: NamedForallStatementResultCompilationInput<'_>,
    ) -> Result<bool, String> {
        let parameters = verification
            .forall_fact
            .typed_parameters
            .collect_param_bindings_with_types();
        if parameters.iter().any(|(_, parameter_type)| {
            !matches!(parameter_type, ParamType::Set(_) | ParamType::Obj(_))
        }) || verification
            .forall_fact
            .then_facts
            .iter()
            .any(|conclusion| {
                !fact_is_supported_by_direct_named_theorem(&conclusion.clone().to_fact())
            })
        {
            return Ok(false);
        }
        if verification.conclusion_checks.len() != verification.forall_fact.then_facts.len() {
            return Err("named forall Result changed its conclusion child order".into());
        }
        if verification.forall_fact.then_facts.is_empty() {
            return Err("named forall Result retained no conclusions".into());
        }
        if !verification.proof_scope_assumption_components.is_empty() {
            return Ok(false);
        }
        let Some(SuccessVerifyFactWellDefinedProofResult::ForallFact(well_definedness)) =
            verification.well_definedness.recursive.as_deref()
        else {
            return Err("named forall Result has no recursive forall well-definedness".into());
        };
        let well_defined_parameters = well_definedness
            .binder
            .parameter_groups
            .iter()
            .flat_map(|group| {
                group
                    .parameters
                    .iter()
                    .map(move |parameter| (group, parameter))
            })
            .collect::<Vec<_>>();
        if well_definedness.statement.to_string() != verification.forall_fact.to_string()
            || well_definedness.premises.len() != verification.forall_fact.dom_facts.len()
            || well_defined_parameters.len() != parameters.len()
            || well_definedness.conclusions.len() != verification.forall_fact.then_facts.len()
        {
            return Err("named forall well-definedness changed its forall structure".into());
        }
        for (parameter_index, ((binding, parameter_type), (group, parameter))) in parameters
            .iter()
            .zip(well_defined_parameters.iter())
            .enumerate()
        {
            if group.group_index >= well_definedness.binder.parameter_groups.len()
                || group.parameter_type.to_string() != parameter_type.to_string()
                || parameter.symbol_id != Some(binding.id())
            {
                return Err(format!(
                    "named forall binder parameter {parameter_index} changed its type or SymbolId"
                ));
            }
            match parameter_type {
                ParamType::Set(_) => {
                    validate_set_parameter_premise(binding.id(), &parameter.proposition)?;
                }
                ParamType::Obj(expected_set) => {
                    validate_object_parameter_premise(
                        binding.id(),
                        expected_set,
                        &parameter.proposition,
                    )?;
                }
                ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {
                    unreachable!("refined set parameters were excluded above")
                }
            }
            validate_atomic_fact_well_definedness_result(
                parameter.well_definedness.as_ref(),
                &parameter.proposition,
            )?;
            validate_single_fact_store_output_allowing_supported_typed_inferences(
                &parameter.infers,
                &parameter.proposition,
                "named forall binder WD",
            )?;
        }
        for (conclusion_index, (conclusion, expected)) in well_definedness
            .conclusions
            .iter()
            .zip(verification.forall_fact.then_facts.iter())
            .enumerate()
        {
            let expected = expected.clone().to_fact();
            if conclusion.proposition.to_string() != expected.to_string() {
                return Err(format!(
                    "named forall WD conclusion {conclusion_index} changed its proposition"
                ));
            }
            validate_direct_named_theorem_conclusion_well_definedness(
                conclusion.well_definedness.as_ref(),
                &conclusion.proposition,
            )?;
            validate_success_store_fact_result_allowing_well_definedness_inferred_children(
                &conclusion.store,
                &conclusion.proposition,
                "named forall conclusion WD",
            )?;
        }
        for (premise_index, (premise, expected)) in well_definedness
            .premises
            .iter()
            .zip(verification.forall_fact.dom_facts.iter())
            .enumerate()
        {
            if premise.proposition.to_string() != expected.to_string() {
                return Err(format!(
                    "named forall WD premise {premise_index} changed its proposition"
                ));
            }
            validate_direct_named_theorem_conclusion_well_definedness(
                premise.well_definedness.as_ref(),
                &premise.proposition,
            )?;
            validate_success_store_fact_result_allowing_well_definedness_inferred_children(
                &premise.store,
                &premise.proposition,
                "named forall premise WD",
            )?;
        }

        let theorem_fact: Fact = (*verification.forall_fact).clone().into();
        let theorem_fact_id =
            if let Some(outer_statement_common) = verification.outer_statement_common {
                if !outer_statement_common.infers.rule_applications.is_empty()
                    || outer_statement_common.infers.store_fact_outputs.len() > 1
                {
                    return Ok(false);
                }
                let [stored] = outer_statement_common.infers.store_fact_outputs.as_slice() else {
                    return Err("named forall Result has no outer store effect".into());
                };
                if stored.itself_and_why_itself_is_stored.0.to_string() != theorem_fact.to_string()
                    || !stored.inferred_facts.is_empty()
                    || !stored.inferred_fact_ids.is_empty()
                {
                    return Ok(false);
                }
                Some(
                    stored
                        .fact_id
                        .ok_or_else(|| "named forall outer store has no FactId".to_string())?,
                )
            } else {
                None
            };

        let proof_scope_has_defined_predicate_inference = verification
            .proof_scope_assumption_infers
            .rule_applications
            .iter()
            .any(|application| defined_predicate_infer_rule(&application.rule));
        let proof_scope_has_direct_inference = verification
            .proof_scope_assumption_infers
            .rule_applications
            .iter()
            .any(|application| {
                infer_rule_has_direct_compiler_environment_consumer(&application.rule)
            });
        if proof_scope_has_defined_predicate_inference && proof_scope_has_direct_inference {
            return Ok(false);
        }
        if verification
            .proof_scope_assumption_infers
            .rule_applications
            .iter()
            .any(|application| {
                !defined_predicate_infer_rule(&application.rule)
                    && !infer_rule_has_direct_compiler_environment_consumer(&application.rule)
            })
        {
            return Ok(false);
        }
        let parameter_facts = well_defined_parameters
            .iter()
            .map(|(_, parameter)| parameter.proposition.clone())
            .collect::<Vec<_>>();
        let mut assumption_facts = parameter_facts.clone();
        assumption_facts.extend(verification.forall_fact.dom_facts.iter().cloned());
        let assumption_fact_ids = exact_ordered_fact_ids_from_store_results(
            verification.proof_scope_assumption_infers,
            &assumption_facts,
            "named forall proof-scope assumptions",
        )?;
        let (parameter_fact_ids, premise_fact_ids) =
            assumption_fact_ids.split_at(parameter_facts.len());
        if verification
            .proof_scope_assumption_infers
            .store_fact_outputs
            .iter()
            .take(parameter_facts.len())
            .any(|output| output.inferred_facts.len() != output.inferred_fact_ids.len())
        {
            return Err(
                "named forall parameter inference lost one or more inferred FactIds".into(),
            );
        }

        let theorem_well_definedness = self
            .collect_well_definedness_to_lean_compilation_context(verification.well_definedness)?;
        self.environment_stack.push_inherited_environment();
        self.environment_stack.well_definedness = Some(theorem_well_definedness.clone());
        let compilation: Result<Option<CompiledNamedForallStatementProofBody>, String> = (|| {
            let mut binder_declarations = Vec::new();
            let mut binder_intro_names = Vec::new();
            for (parameter_index, (((binding, parameter_type), parameter), fact_id)) in parameters
                .iter()
                .zip(parameter_facts.iter())
                .zip(parameter_fact_ids.iter())
                .enumerate()
            {
                let parameter_name = lean_identifier(binding.name());
                if self
                    .environment_stack
                    .symbol_names
                    .insert(binding.id(), parameter_name.clone())
                    .is_some()
                {
                    return Err(format!(
                        "named forall binder reused SymbolId `{:?}`",
                        binding.id()
                    ));
                }
                if matches!(parameter_type, ParamType::Set(_)) {
                    validate_set_parameter_premise(binding.id(), parameter)?;
                    binder_declarations.push(format!("({parameter_name} : Litex.Set)"));
                    binder_intro_names.push(parameter_name);
                    self.environment_stack
                        .fact_names
                        .insert(*fact_id, "True.intro".to_string());
                    self.environment_stack
                        .fact_propositions
                        .insert(*fact_id, parameter.clone());
                    continue;
                }

                let parameter_set = parameter_set(parameter_type)
                    .map_err(|error| format!("named forall binder {parameter_index}: {error}"))?;
                if matches!(parameter_set, Obj::StandardSet(StandardSet::Z)) {
                    validate_object_parameter_premise(binding.id(), parameter_set, parameter)?;
                    binder_declarations.push(format!("({parameter_name} : ℤ)"));
                    binder_intro_names.push(parameter_name.clone());
                    let parameter_proof = format!("(Litex.In.own Litex.Z {parameter_name})");
                    self.environment_stack
                        .fact_names
                        .insert(*fact_id, parameter_proof.clone());
                    self.environment_stack
                        .fact_propositions
                        .insert(*fact_id, parameter.clone());
                    install_parameter_fact_aliases(
                        binding.id(),
                        *fact_id,
                        parameter,
                        &parameter_proof,
                        parameter_set,
                        &mut self.environment_stack,
                    )?;
                    install_structured_induction_native_integer_symbol(
                        binding.id(),
                        &parameter_name,
                        &mut self.environment_stack,
                    );
                    continue;
                }
                let (_, retained_parameter_set) = membership_parts(parameter)?;
                let rendered_parameter_set =
                    render_obj(retained_parameter_set, &self.environment_stack)?;
                let carrier_name = format!(
                    "__carrier{}_{}",
                    self.next_fact_name_index,
                    parameter_index + 1
                );
                match parameter_set {
                    set if forall_parameter_uses_exact_refined_numeric_carrier(set) => {
                        binder_declarations.push(format!(
                            "({parameter_name} : ({rendered_parameter_set}).Carrier)"
                        ));
                    }
                    Obj::FnSet(_) | Obj::FiniteSeqSet(_) | Obj::SeqSet(_) => {
                        binder_declarations.push(format!("{{{carrier_name} : Type 1}}"));
                        binder_intro_names.push(carrier_name.clone());
                        binder_declarations.push(format!("({parameter_name} : {carrier_name})"));
                    }
                    _ => {
                        binder_declarations.push(format!("{{{carrier_name} : Type}}"));
                        binder_intro_names.push(carrier_name.clone());
                        binder_declarations.push(format!("({parameter_name} : {carrier_name})"));
                    }
                }
                binder_intro_names.push(parameter_name.clone());
                let rendered_parameter_fact = render_fact(parameter, &self.environment_stack)?;
                let expected_parameter_fact =
                    format!("Litex.In {parameter_name} {rendered_parameter_set}");
                if rendered_parameter_fact != expected_parameter_fact {
                    return Err(format!(
                        "named forall parameter evidence mismatch: expected `{expected_parameter_fact}`, found `{rendered_parameter_fact}`"
                    ));
                }
                let hypothesis_name = format!("__h{}", fact_id.value());
                binder_declarations
                    .push(format!("({hypothesis_name} : {rendered_parameter_fact})"));
                binder_intro_names.push(hypothesis_name.clone());
                self.environment_stack
                    .fact_names
                    .insert(*fact_id, hypothesis_name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(*fact_id, parameter.clone());
                install_parameter_fact_aliases(
                    binding.id(),
                    *fact_id,
                    parameter,
                    &hypothesis_name,
                    parameter_set,
                    &mut self.environment_stack,
                )?;
                if forall_parameter_uses_exact_refined_numeric_carrier(parameter_set) {
                    let lowered_set = LeanTargetObjectRepresentation::lower(parameter_set)?;
                    self.environment_stack
                        .exact_carrier_values
                        .insert(binding.id(), parameter_name.clone());
                    self.environment_stack
                        .exact_positive_real_carriers
                        .insert(binding.id(), parameter_name.clone());
                    if let Some(real) = exact_set_real_value(&lowered_set, &parameter_name) {
                        self.environment_stack
                            .numeric_real_values
                            .insert(binding.id(), real);
                    }
                    if let Some(integer) = exact_set_integer_value(&lowered_set, &parameter_name) {
                        self.environment_stack
                            .numeric_integer_values
                            .insert(binding.id(), integer);
                    }
                    if let Some(rational) = exact_set_rational_value(&lowered_set, &parameter_name)
                    {
                        self.environment_stack
                            .numeric_rational_values
                            .insert(binding.id(), rational);
                    }
                    if let Some(numeric) = exact_set_numeric_value(&lowered_set, &parameter_name) {
                        self.environment_stack
                            .numeric_representations
                            .insert(binding.id(), numeric);
                    }
                    if let Some(equality) =
                        exact_set_numeric_equality(&lowered_set, &parameter_name)
                    {
                        self.environment_stack
                            .numeric_representation_equalities
                            .insert(binding.id(), equality);
                    }
                    if let Some(proof) = exact_set_numeric_proof(&lowered_set, &parameter_name) {
                        self.environment_stack
                            .numeric_representation_memberships
                            .insert(binding.id(), proof);
                    }
                }
            }

            let recursive_well_definedness = verification
                .well_definedness
                .recursive
                .as_deref()
                .ok_or_else(|| {
                    "named forall Result has no recursive well-definedness root".to_string()
                })?;
            let compiled_well_definedness = self.compile_precollected_well_definedness_context(
                theorem_well_definedness.clone(),
                &[recursive_well_definedness],
            )?;
            self.environment_stack.well_definedness = Some(compiled_well_definedness);

            for (premise_index, (((premise, premise_fact_id), premise_output), premise_wd)) in
                verification
                    .forall_fact
                    .dom_facts
                    .iter()
                    .zip(premise_fact_ids.iter())
                    .zip(
                        verification
                            .proof_scope_assumption_infers
                            .store_fact_outputs
                            .iter()
                            .skip(parameter_facts.len()),
                    )
                    .zip(well_definedness.premises.iter())
                    .enumerate()
            {
                let proposition = render_fact(premise, &self.environment_stack)?;
                let premise_name = format!("__domain{}", premise_index + 1);
                binder_declarations.push(format!("({premise_name} : {proposition})"));
                binder_intro_names.push(premise_name.clone());
                self.environment_stack
                    .fact_names
                    .insert(*premise_fact_id, premise_name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(*premise_fact_id, premise.clone());

                let premise_well_definedness_fact_id =
                    premise_wd.store.fact_id.ok_or_else(|| {
                        format!("named forall WD premise {premise_index} has no frozen FactId")
                    })?;
                self.environment_stack
                    .fact_names
                    .insert(premise_well_definedness_fact_id, premise_name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(premise_well_definedness_fact_id, premise.clone());

                if premise_output.inferred_facts.len() != premise_output.inferred_fact_ids.len() {
                    return Err(format!(
                        "named forall premise {premise_index} lost an inferred FactId"
                    ));
                }
            }

            if proof_scope_has_defined_predicate_inference {
                self.compile_defined_predicate_inference_results_in_current_environment(
                    verification.proof_scope_assumption_infers,
                    DefinedPredicateInferenceConclusionPublication::LocalProofExpression,
                )?;
            } else if proof_scope_has_direct_inference {
                let allowed_sources = assumption_fact_ids
                    .iter()
                    .copied()
                    .zip(assumption_facts.iter().cloned())
                    .collect::<Vec<_>>();
                self.compile_typed_inference_results_in_current_compiler_environment(
                    verification.proof_scope_assumption_infers,
                    &allowed_sources,
                    CompiledInferenceFactAvailabilityInLeanEnvironment::InlineProofExpression,
                    "named forall proof-scope assumptions",
                    None,
                )?;
            }
            validate_flattened_inferred_fact_ids_are_visible(
                verification.proof_scope_assumption_infers,
                &self.environment_stack,
                "named forall proof-scope assumptions",
            )?;

            // Runtime completes theorem well-definedness before executing any
            // proof step, so every intrinsic store produced by the named
            // premise/conclusion WD children is already visible here.
            for premise in &well_definedness.premises {
                install_fact_well_definedness_proof_store_results_in_active_environment(
                    premise.well_definedness.as_ref(),
                    &mut self.environment_stack,
                )?;
            }
            for conclusion in &well_definedness.conclusions {
                install_fact_well_definedness_proof_store_results_in_active_environment(
                    conclusion.well_definedness.as_ref(),
                    &mut self.environment_stack,
                )?;
            }

            let mut proof_lines = Vec::with_capacity(
                verification.proof_steps.len() + verification.conclusion_checks.len() + 1,
            );
            for (proof_step_index, proof_step) in verification.proof_steps.iter().enumerate() {
                let Some(lines) = self
                    .compile_stmt_result_as_local_proof_steps(proof_step, proof_step_index + 1)?
                else {
                    return Err(format!(
                        "named forall proof step {} has no local compiler consumer: {:?}",
                        proof_step_index + 1,
                        proof_step,
                    ));
                };
                proof_lines.extend(lines);
            }

            let mut conclusion_names = Vec::new();
            let mut conclusion_types = Vec::new();
            for (conclusion_index, (conclusion, expected_conclusion)) in verification
                .conclusion_checks
                .iter()
                .zip(verification.forall_fact.then_facts.iter())
                .enumerate()
            {
                let conclusion = conclusion
                    .factual_success()
                    .ok_or_else(|| "named forall conclusion is not factual".to_string())?;
                let expected_conclusion = expected_conclusion.clone().to_fact();
                if conclusion.fact().to_string() != expected_conclusion.to_string() {
                    return Err("named forall conclusion changed its target".into());
                }
                if !conclusion.store.infers.is_empty() {
                    validate_flattened_inferred_fact_ids_are_visible(
                        &conclusion.store.infers,
                        &self.environment_stack,
                        &format!("named forall conclusion {conclusion_index}"),
                    )?;
                }
                let Some(conclusion_proof) =
                    self.construct_lean_proof_from_direct_fact_result(conclusion)?
                else {
                    return Err(format!(
                        "named forall conclusion {} has no direct proof consumer",
                        conclusion_index + 1
                    ));
                };
                let proposition = render_fact(&expected_conclusion, &self.environment_stack)?;
                let conclusion_name =
                    format!("__c{}_{}", self.next_fact_name_index, conclusion_index);
                proof_lines.push(format!(
                    "have {conclusion_name} : {proposition} := {conclusion_proof}"
                ));
                conclusion_names.push(conclusion_name);
                conclusion_types.push(proposition);
            }
            if conclusion_names.len() == 1 {
                proof_lines.push(format!("exact {}", conclusion_names[0]));
            } else {
                proof_lines.push(format!("exact ⟨{}⟩", conclusion_names.join(", ")));
            }
            Ok(Some(CompiledNamedForallStatementProofBody {
                binder_declarations,
                binder_intro_names,
                proof_lines,
                conclusion_type: if conclusion_types.len() == 1 {
                    conclusion_types[0].clone()
                } else {
                    conjunction(
                        &conclusion_types
                            .iter()
                            .map(|conclusion| format!("({conclusion})"))
                            .collect::<Vec<_>>(),
                    )
                },
            }))
        })(
        );
        self.environment_stack.pop_local_environment();
        let Some(body) = compilation? else {
            return Ok(false);
        };

        let theorem_name = lean_identifier(&verification.name);
        let theorem_type = if body.binder_declarations.is_empty() {
            body.conclusion_type
        } else {
            format!(
                "∀ {},\n      {}",
                body.binder_declarations.join(" "),
                body.conclusion_type
            )
        };
        let intro = if body.binder_intro_names.is_empty() {
            String::new()
        } else {
            format!("intro {}\n", body.binder_intro_names.join(" "))
        };
        self.declarations.push(format!(
            "theorem {theorem_name} :\n    {theorem_type} := by\n{}",
            indent_lines(&format!("{intro}{}", body.proof_lines.join("\n")), 2)
        ));
        if let Some(theorem_fact_id) = theorem_fact_id {
            self.environment_stack
                .fact_names
                .insert(theorem_fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(theorem_fact_id, theorem_fact);
            self.environment_stack
                .fact_well_definedness
                .insert(theorem_fact_id, theorem_well_definedness);
        }
        self.next_fact_name_index += 1;
        Ok(true)
    }
}
