//! By-definition compilation, bindings, and proofs.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Recreate the lexical environment in which a concrete predicate's
    /// retained definition clauses are meaningful for one exact application.
    /// Definition-owned occurrence IDs and parameter FactIds are stable, but
    /// their values and proofs must be rebound for every invocation.
    pub(in super::super) fn by_definition_clause_application_environment(
        &self,
        result: &SuccessByDefStmtResult,
    ) -> Result<StmtResultToLeanCompilerEnvironmentStack, String> {
        let verification = result
            .verification
            .as_ref()
            .ok_or_else(|| "by-definition Result has no verification payload".to_string())?;
        let definition = verification.definition.as_ref().ok_or_else(|| {
            "by-definition Result lost its concrete predicate definition".to_string()
        })?;
        let target: Fact = result.statement.fact.clone().into();
        let Fact::AtomicFact(AtomicFact::NormalAtomicFact(target_predicate)) = &target else {
            return Err("concrete by-definition target is not a predicate application".into());
        };
        let binding = self
            .environment_stack
            .predicate_bindings
            .get(&definition.name)
            .ok_or_else(|| {
                format!(
                    "by-definition references unavailable predicate `{}`",
                    definition.name
                )
            })?;
        let parameter_types = definition
            .typed_parameters
            .collect_param_bindings_with_types();
        if parameter_types.len() != target_predicate.body.len()
            || binding.exact_parameters.len() != parameter_types.len()
        {
            return Err("by-definition application changed its parameter arity".into());
        }

        let mut context = self.environment_stack.clone();
        let definition_well_definedness =
            binding
                .definition_well_definedness
                .as_ref()
                .ok_or_else(|| {
                    "concrete predicate binding has no retained definition WD context".to_string()
                })?;
        let mut combined_well_definedness = context.well_definedness.clone().unwrap_or_default();
        if let Some(target_well_definedness) = &verification.target_well_definedness {
            if let Some(recursive) = target_well_definedness.recursive.as_deref() {
                let mut target_context =
                    StmtResultWellDefinednessToLeanCompilationContext::default();
                collect_well_definedness_to_lean_context_from_fact_result(
                    recursive,
                    &mut target_context,
                )?;
                combined_well_definedness.merge_from(&target_context)?;
            }
        }
        if let Some(argument_verification) = verification.argument_verification.as_deref() {
            let mut argument_well_definedness =
                StmtResultWellDefinednessToLeanCompilationContext::default();
            for check in &argument_verification.checks {
                let Some(check) = check.factual_success() else {
                    continue;
                };
                let Some(recursive) = check.well_definedness.recursive.as_deref() else {
                    continue;
                };
                collect_well_definedness_to_lean_context_from_fact_result(
                    recursive,
                    &mut argument_well_definedness,
                )?;
            }
            combined_well_definedness.merge_from(&argument_well_definedness)?;
        }
        combined_well_definedness.merge_from(definition_well_definedness)?;
        context.well_definedness = Some(combined_well_definedness);
        for ((definition_parameter, _), argument) in
            parameter_types.iter().zip(target_predicate.body.iter())
        {
            let rendered_argument = render_obj(argument, &context)?;
            context
                .symbol_names
                .insert(definition_parameter.id(), rendered_argument);
        }
        for (parameter_index, ((definition_parameter, parameter_type), argument)) in parameter_types
            .iter()
            .zip(target_predicate.body.iter())
            .enumerate()
        {
            let ParamType::Obj(set) = parameter_type else {
                continue;
            };
            if !matches!(set, Obj::FnSet(_) | Obj::FiniteSeqSet(_) | Obj::SeqSet(_)) {
                continue;
            }
            if !binding.exact_parameters[parameter_index] {
                return Err(format!(
                    "by-definition function parameter {parameter_index} has no exact target carrier"
                ));
            }
            let alias = definition_well_definedness
                .parameter_fact_aliases
                .iter()
                .find(|alias| alias.symbol_id == definition_parameter.id())
                .ok_or_else(|| {
                    format!(
                        "by-definition function parameter {parameter_index} has no definition FactId alias"
                    )
                })?;
            let rendered_set = render_obj(set, &self.environment_stack)?;
            let exact_argument =
                render_exact_predicate_argument(argument, set, &self.environment_stack)?;
            let parameter_proof = format!("Litex.In.own {rendered_set} {exact_argument}");
            install_parameter_fact_aliases(
                definition_parameter.id(),
                alias.fact_id,
                &alias.proposition,
                &parameter_proof,
                set,
                &mut context,
            )?;
        }
        Ok(context)
    }

    pub(in super::super) fn compile_by_definition_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByDefStmtResult,
    ) -> Result<bool, String> {
        if let Some(verification) = &result.verification {
            for (clause_index, check) in verification.clause_checks.iter().enumerate() {
                let check = check.factual_success().ok_or_else(|| {
                    format!("by-definition clause check {clause_index} is not factual")
                })?;
                if matches!(check.proof(), SuccessFactProofResult::ForallProof(_))
                    && !self.compile_direct_forall_fact_result(check)?
                {
                    return Err(format!(
                        "by-definition forall clause {clause_index} has no binder compiler"
                    ));
                }
            }
        }
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

        self.install_compiled_by_definition_component_bindings(&proof.components)?;

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

    pub(in super::super) fn install_compiled_by_definition_component_bindings(
        &mut self,
        components: &[CompiledByDefinitionComponentProofBody],
    ) -> Result<(), String> {
        for component in components {
            let Some(fact_id) = component.retained_fact_id else {
                continue;
            };
            if self
                .environment_stack
                .fact_propositions
                .contains_key(&fact_id)
            {
                resolve_fact_citation(&fact_id, &component.fact, &self.environment_stack)?;
                continue;
            }
            self.environment_stack
                .fact_names
                .insert(fact_id, component.proof_expression.clone());
            self.environment_stack
                .fact_propositions
                .insert(fact_id, component.fact.clone());
        }
        Ok(())
    }

    /// `Combine`: validate each parameter and definition-clause child in
    /// source order, then fold those exact proofs into the predicate.
    pub(in super::super) fn construct_lean_proof_from_by_definition_stmt_result(
        &mut self,
        result: &SuccessByDefStmtResult,
    ) -> Result<Option<CompiledByDefinitionProofBody>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        let mut context = StmtResultWellDefinednessToLeanCompilationContext::default();
        let mut roots = Vec::new();
        if let Some(target_well_definedness) = &verification.target_well_definedness {
            if let Some(recursive) = target_well_definedness.recursive.as_deref() {
                collect_well_definedness_to_lean_context_from_fact_result(recursive, &mut context)?;
                roots.push(recursive);
            }
        }
        if let Some(arguments) = verification.argument_verification.as_deref() {
            for check in &arguments.checks {
                let Some(check) = check.factual_success() else {
                    continue;
                };
                let Some(recursive) = check.well_definedness.recursive.as_deref() else {
                    continue;
                };
                collect_well_definedness_to_lean_context_from_fact_result(recursive, &mut context)?;
                roots.push(recursive);
            }
        }
        if roots.is_empty() {
            return self
                .construct_lean_proof_from_by_definition_stmt_result_in_active_wd_context(result);
        }
        let context = self.compile_precollected_well_definedness_context(context, &roots)?;
        let parent_context = self.environment_stack.well_definedness.replace(context);
        let compiled =
            self.construct_lean_proof_from_by_definition_stmt_result_in_active_wd_context(result);
        self.environment_stack.well_definedness = parent_context;
        compiled
    }

    fn construct_lean_proof_from_by_definition_stmt_result_in_active_wd_context(
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
            return Err(
                "by-definition argument verification unexpectedly published inference effects"
                    .into(),
            );
        }
        if argument_verification.checks.len() != binding.requirement_count
            || verification.definition_clause_facts.len() != binding.clause_count
            || verification.clause_checks.len() != binding.clause_count
        {
            return Err("by-definition Result changed its component arity".into());
        }

        self.install_fact_anonymous_function_occurrence_aliases(&target, "by-definition target")?;
        for (component_index, check) in argument_verification.checks.iter().enumerate() {
            let check = check
                .factual_success()
                .ok_or_else(|| "by-definition parameter child is not factual".to_string())?;
            self.install_fact_anonymous_function_occurrence_aliases(
                &check.fact(),
                &format!("by-definition parameter check {component_index}"),
            )?;
        }
        for (clause_index, retained_clause) in
            verification.definition_clause_facts.iter().enumerate()
        {
            self.install_fact_anonymous_function_occurrence_aliases(
                retained_clause,
                &format!("by-definition clause {clause_index}"),
            )?;
        }

        let substitutions = definition
            .typed_parameters
            .param_defs_and_args_to_param_to_arg_map(target_predicate.body.as_slice());
        let mut substitution_runtime = Runtime::default();
        substitution_runtime.ensure_execution_frame_for_parse();
        for (clause_index, (source_clause, retained_clause)) in definition
            .iff_facts
            .iter()
            .zip(verification.definition_clause_facts.iter())
            .enumerate()
        {
            let replayed = substitution_runtime
                .inst_fact(
                    source_clause,
                    &substitutions,
                    SubstitutionMode::ResultProjection,
                    None,
                )
                .map_err(|error| {
                    format!(
                        "by-definition clause {clause_index} substitution replay failed: {}",
                        error.trace_message()
                    )
                })?;
            let replayed_key = substitution_runtime
                .equivalent_proposition_lookup_key_for_fact(&replayed)
                .map_err(|error| {
                    format!(
                        "by-definition clause {clause_index} replay key failed: {}",
                        error.trace_message()
                    )
                })?;
            let retained_key = substitution_runtime
                .equivalent_proposition_lookup_key_for_fact(retained_clause)
                .map_err(|error| {
                    format!(
                        "by-definition clause {clause_index} retained key failed: {}",
                        error.trace_message()
                    )
                })?;
            if replayed_key != retained_key {
                return Err(format!(
                    "by-definition clause {clause_index} changed its exact parameter substitution:\n  replayed: {}\n  retained: {}\n  replayed key: {}\n  retained key: {}",
                    replayed,
                    retained_clause,
                    replayed_key,
                    retained_key,
                ));
            }
        }

        // Definition instantiation renders every clause with the exact
        // numeric representatives selected by its parameter-check Results.
        // Make those frozen FactIds visible before constructing the
        // instantiated component types; otherwise a compound argument such
        // as `c * a` has no certificate from which to select its real
        // representative.
        for (component_index, check) in argument_verification.checks.iter().enumerate() {
            let check = check
                .factual_success()
                .ok_or_else(|| "by-definition parameter child is not factual".to_string())?;
            let fact_id = check.store.fact_id.ok_or_else(|| {
                format!("by-definition parameter check {component_index} has no FactId")
            })?;
            if self
                .environment_stack
                .fact_propositions
                .contains_key(&fact_id)
            {
                continue;
            }
            let compiled = self
                .construct_direct_fact_proof_with_result_owned_well_definedness(check)
                .map_err(|error| {
                    format!(
                        "by-definition parameter check {component_index} proof replay failed (recursive WD: {}): {error}",
                        check.well_definedness.recursive.is_some()
                    )
                })?
                .ok_or_else(|| {
                    format!(
                        "by-definition parameter check {component_index} has no direct proof consumer"
                    )
                })?;
            self.environment_stack
                .fact_names
                .insert(fact_id, compiled.proof_expression);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, compiled.fact);
        }

        let expected_components =
            instantiated_predicate_components(&target, &binding, &self.environment_stack)?;
        if expected_components.len() != binding.requirement_count + binding.clause_count {
            return Err("active predicate definition produced an invalid component arity".into());
        }
        let mut components = Vec::with_capacity(expected_components.len());
        let parameter_types = definition
            .typed_parameters
            .collect_param_bindings_with_types();
        for (component_index, check) in argument_verification.checks.iter().enumerate() {
            let check = check
                .factual_success()
                .ok_or_else(|| "by-definition parameter child is not factual".to_string())?;
            validate_scoped_fact_check_result(
                check,
                &check.fact(),
                &format!("by-definition parameter check {component_index}"),
            )?;
            let (_, parameter_type) = &parameter_types[component_index];
            let proof = if matches!(parameter_type, ParamType::Set(_)) {
                // A `set` parameter is already represented by the native
                // `Litex.Set` binder. Its verifier-owned `$is_set` child is
                // retained and validated above, while the concrete
                // predicate's Lean requirement is definitionally `True`.
                "True.intro".to_string()
            } else if binding.exact_parameters[component_index] {
                let ParamType::Obj(set) = parameter_type else {
                    return Err("exact predicate parameter retained a non-object type".into());
                };
                let checked_fact = check.fact();
                let (checked_argument, checked_set) = membership_parts(&checked_fact)?;
                if obj_equality_key(checked_argument)
                    != obj_equality_key(&target_predicate.body[component_index])
                    || obj_equality_key(checked_set) != obj_equality_key(set)
                {
                    return Err(format!(
                        "by-definition exact function parameter check {component_index} changed its source argument or set"
                    ));
                }
                let argument = render_exact_predicate_argument(
                    &target_predicate.body[component_index],
                    set,
                    &self.environment_stack,
                )?;
                format!(
                    "Litex.In.own {} {argument}",
                    render_obj(set, &self.environment_stack)?
                )
            } else {
                let ParamType::Obj(set) = parameter_type else {
                    return Err(
                        "concrete predicate object requirement retained another parameter type"
                            .into(),
                    );
                };
                let checked_fact = check.fact();
                let (checked_argument, checked_set) = membership_parts(&checked_fact)?;
                if obj_equality_key(checked_argument)
                    != obj_equality_key(&target_predicate.body[component_index])
                    || obj_equality_key(checked_set) != obj_equality_key(set)
                {
                    return Err(format!(
                        "by-definition parameter check {component_index} changed its source argument or set"
                    ));
                }
                let Some(proof) = self.construct_lean_proof_from_direct_fact_result(check)? else {
                    return Err(format!(
                        "by-definition parameter check {component_index} has no direct proof consumer: {:?}",
                        check.proof()
                    ));
                };
                if render_fact(&checked_fact, &self.environment_stack)?
                    == expected_components[component_index]
                {
                    proof
                } else {
                    let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
                    let source_argument = render_obj(
                        &target_predicate.body[component_index],
                        &self.environment_stack,
                    )?;
                    let exact_argument = match LeanTargetObjectRepresentation::lower(
                        &target_predicate.body[component_index],
                    )? {
                        LeanTargetObjectRepresentation::Symbol { symbol_id, .. } => self
                            .environment_stack
                            .exact_carrier_values
                            .get(&symbol_id)
                            .cloned(),
                        _ => None,
                    };
                    exact_argument
                        .and_then(|argument| exact_set_numeric_proof(&lowered_set, &argument))
                        .or_else(|| {
                            membership_numeric_proof(&lowered_set, &source_argument, &proof)
                        })
                        .ok_or_else(|| {
                            format!(
                                "by-definition numeric parameter check {component_index} cannot construct its canonical predicate-boundary membership"
                            )
                        })?
                }
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

            // Clause proof Results retain the definition-time occurrence IDs
            // and function-contract FactIds.  Render them in a lexical copy
            // of the current application environment, rebinding each
            // definition parameter to this invocation's actual argument.
            // The aliases must not escape: the same predicate can be invoked
            // later with different function arguments under the same
            // definition-owned FactIds.
            let mut clause_proof_environment = self.environment_stack.clone();
            if let Some(definition_well_definedness) = &binding.definition_well_definedness {
                clause_proof_environment.well_definedness =
                    Some(definition_well_definedness.clone());
            }
            for ((definition_parameter, _), argument) in
                parameter_types.iter().zip(target_predicate.body.iter())
            {
                clause_proof_environment.symbol_names.insert(
                    definition_parameter.id(),
                    render_obj(argument, &self.environment_stack)?,
                );
            }
            for (parameter_index, ((definition_parameter, parameter_type), _)) in parameter_types
                .iter()
                .zip(target_predicate.body.iter())
                .enumerate()
            {
                let ParamType::Obj(set) = parameter_type else {
                    continue;
                };
                if !matches!(set, Obj::FnSet(_) | Obj::FiniteSeqSet(_) | Obj::SeqSet(_)) {
                    continue;
                }
                let definition_well_definedness = binding
                    .definition_well_definedness
                    .as_ref()
                    .ok_or_else(|| {
                        "by-definition function parameter has no retained definition WD context"
                            .to_string()
                    })?;
                let alias = definition_well_definedness
                    .parameter_fact_aliases
                    .iter()
                    .find(|alias| alias.symbol_id == definition_parameter.id())
                    .ok_or_else(|| {
                        format!(
                            "by-definition function parameter {parameter_index} has no definition FactId alias"
                        )
                    })?;
                install_parameter_fact_aliases(
                    definition_parameter.id(),
                    alias.fact_id,
                    &alias.proposition,
                    &components[parameter_index].proof_expression,
                    set,
                    &mut clause_proof_environment,
                )?;
            }
            let proof = if matches!(check.proof(), SuccessFactProofResult::ForallProof(_)) {
                let fact_id = check.store.fact_id.ok_or_else(|| {
                    format!("by-definition forall clause {clause_index} has no frozen FactId")
                })?;
                resolve_fact_citation(&fact_id, retained_clause, &clause_proof_environment)?
            } else {
                let mut nested_compiler =
                    StmtResultToLeanCompiler::new("nested by-definition clause proof");
                nested_compiler.environment_stack = clause_proof_environment;
                let Some(proof) = nested_compiler
                    .construct_direct_fact_proof_with_result_owned_well_definedness(check)?
                    .map(|proof| proof.proof_expression)
                else {
                    return Err(format!(
                        "by-definition clause check {clause_index} has no direct proof consumer: {:?}",
                        check.proof()
                    ));
                };
                if !nested_compiler.declarations.is_empty() {
                    return Err(format!(
                        "by-definition clause check {clause_index} attempted to emit a top-level declaration"
                    ));
                }
                proof
            };
            // A bare reference to a theorem with an implicit host-carrier
            // binder is eagerly instantiated by Lean.  When a concrete
            // predicate consumes the complete retained forall proposition,
            // preserve that binder explicitly instead of collapsing it to a
            // fresh metavariable.
            let proof = if matches!(retained_clause, Fact::ForallFact(_)) {
                format!("@{proof}")
            } else {
                proof
            };
            let definition_clause = &definition.iff_facts[clause_index];
            let transportable_clause = match definition_clause {
                Fact::AtomicFact(AtomicFact::EqualFact(_)) => true,
                Fact::ExistFact(existential) => matches!(
                    existential.facts()[0].from_ref_to_cloned_fact(),
                    Fact::AtomicFact(AtomicFact::EqualFact(_))
                ),
                _ => false,
            };
            let proof = if transportable_clause {
                let mut clause_source = self.environment_stack.clone();
                let mut clause_target = self.environment_stack.clone();
                if let Some(definition_well_definedness) = &binding.definition_well_definedness {
                    clause_source.well_definedness = Some(definition_well_definedness.clone());
                    clause_target.well_definedness = Some(definition_well_definedness.clone());
                }
                let mut transports = Vec::new();
                for (parameter_index, ((definition_parameter, parameter_type), argument)) in
                    parameter_types
                        .iter()
                        .zip(target_predicate.body.iter())
                        .enumerate()
                {
                    let source_value = render_obj(argument, &self.environment_stack)?;
                    let target_value = render_concrete_predicate_argument(
                        &binding,
                        parameter_index,
                        argument,
                        &self.environment_stack,
                    )?;
                    clause_source
                        .symbol_names
                        .insert(definition_parameter.id(), source_value.clone());
                    clause_target
                        .symbol_names
                        .insert(definition_parameter.id(), target_value.clone());
                    if let ParamType::Obj(set) = parameter_type {
                        if matches!(set, Obj::FnSet(_) | Obj::FiniteSeqSet(_) | Obj::SeqSet(_)) {
                            let definition_well_definedness = binding
                                .definition_well_definedness
                                .as_ref()
                                .ok_or_else(|| {
                                    "by-definition function parameter has no retained definition WD context"
                                        .to_string()
                                })?;
                            let alias = definition_well_definedness
                                .parameter_fact_aliases
                                .iter()
                                .find(|alias| alias.symbol_id == definition_parameter.id())
                                .ok_or_else(|| {
                                    format!(
                                        "by-definition function parameter {parameter_index} has no definition FactId alias"
                                    )
                                })?;
                            let parameter_proof = &components[parameter_index].proof_expression;
                            install_parameter_fact_aliases(
                                definition_parameter.id(),
                                alias.fact_id,
                                &alias.proposition,
                                parameter_proof,
                                set,
                                &mut clause_source,
                            )?;
                            install_parameter_fact_aliases(
                                definition_parameter.id(),
                                alias.fact_id,
                                &alias.proposition,
                                parameter_proof,
                                set,
                                &mut clause_target,
                            )?;
                        }
                    }
                    if !binding.exact_parameters[parameter_index] {
                        if source_value != target_value {
                            return Err(format!(
                                "by-definition clause {clause_index} changed non-exact parameter {parameter_index}"
                            ));
                        }
                        continue;
                    }
                    let ParamType::Obj(set) = parameter_type else {
                        return Err(
                            "by-definition exact clause parameter is not object-valued".into()
                        );
                    };
                    install_exact_predicate_carrier_value(
                        definition_parameter.id(),
                        set,
                        &target_value,
                        &mut clause_target,
                    )?;
                    if source_value != target_value {
                        let exact_to_source = render_exact_predicate_argument_same_to_source(
                            argument,
                            set,
                            &self.environment_stack,
                        )?;
                        transports.push((
                            definition_parameter.id(),
                            set.clone(),
                            source_value,
                            target_value,
                            format!("Litex.Same.symm ({exact_to_source})"),
                        ));
                    }
                }
                let mut transported = format!(
                    "(by simpa [Litex.fnApplyOwn, Litex.abs, Complex.ext_iff, Real.norm_eq_abs] using ({proof}))"
                );
                let mut current = clause_source;
                for (symbol_id, set, source_value, target_value, bridge) in transports {
                    let mut next = current.clone();
                    next.symbol_names.insert(symbol_id, target_value.clone());
                    install_exact_predicate_carrier_value(
                        symbol_id,
                        &set,
                        &target_value,
                        &mut next,
                    )?;
                    transported = match definition_clause {
                        Fact::AtomicFact(AtomicFact::EqualFact(equality)) => {
                            render_equality_across_representative(
                                equality,
                                &current,
                                &next,
                                &source_value,
                                &target_value,
                                &bridge,
                                &transported,
                            )?
                        }
                        Fact::ExistFact(existential) => {
                            render_one_witness_existential_across_representative(
                                existential,
                                &current,
                                &next,
                                &source_value,
                                &target_value,
                                &bridge,
                                &transported,
                            )?
                        }
                        _ => unreachable!("transportable clause was checked above"),
                    };
                    current = next;
                }
                if render_fact(definition_clause, &current)? != expected_components[component_index]
                {
                    return Err(format!(
                        "by-definition clause {clause_index} did not reach its exact predicate representation"
                    ));
                }
                transported
            } else {
                format!(
                    "(by simpa [Litex.fnApplyOwn, Litex.abs, Complex.ext_iff, Real.norm_eq_abs] using ({proof}))"
                )
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
}
