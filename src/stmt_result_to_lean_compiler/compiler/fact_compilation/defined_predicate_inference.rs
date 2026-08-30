//! Defined-predicate inference compilation.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: publish the exact proved predicate application, then consume
    /// its typed parameter-requirement and definition-clause projection
    /// children. Every conclusion is installed under its retained FactId in
    /// the current compiler environment before its own nested infer Result is
    /// entered.
    pub(in super::super) fn compile_defined_predicate_fact_with_inference(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let source_fact = result.fact();
        let Fact::AtomicFact(AtomicFact::NormalAtomicFact(_)) = &source_fact else {
            return Ok(false);
        };
        if result.store.infers.rule_applications.is_empty()
            || result
                .store
                .infers
                .rule_applications
                .iter()
                .any(|application| !defined_predicate_infer_rule(&application.rule))
        {
            return Ok(false);
        }
        if result.store.fact.to_string() != source_fact.to_string() {
            return Err("defined-predicate fact changed between verification and store".into());
        }
        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        let Some(source_proof) =
            self.construct_lean_proof_from_direct_fact_result_using_its_well_definedness(result)?
        else {
            return Ok(false);
        };
        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "defined-predicate source store has no FactId".to_string())?;
        let source_proposition = render_fact(&source_fact, &self.environment_stack)?;
        let source_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {source_theorem_name} : {source_proposition} := by\n  exact {source_proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, source_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact.clone());
        self.next_fact_name_index += 1;

        self.compile_defined_predicate_inference_results_in_current_environment(
            &result.store.infers,
            DefinedPredicateInferenceConclusionPublication::PersistentLeanTheorem,
        )?;
        validate_flattened_inferred_fact_ids_are_visible(
            &result.store.infers,
            &self.environment_stack,
            "defined-predicate source store",
        )?;
        Ok(true)
    }

    /// Recursively compile only the defined-predicate inference family in the
    /// active target-language environment. This is `Combine`, not a second
    /// statement IR: the child `SuccessStoreFactResult` remains the semantic
    /// owner of its nested effects.
    pub(in super::super) fn compile_defined_predicate_inference_results_in_current_environment(
        &mut self,
        infer_result: &SuccessInferResult,
        publication: DefinedPredicateInferenceConclusionPublication,
    ) -> Result<(), String> {
        for application in &infer_result.rule_applications {
            if defined_predicate_infer_rule(&application.rule) {
                self.compile_defined_predicate_inference_application_in_current_environment(
                    application,
                    publication,
                )?;
            } else {
                for conclusion in &application.conclusions {
                    self.compile_defined_predicate_inference_results_in_current_environment(
                        &conclusion.infers,
                        publication,
                    )?;
                }
            }
        }
        Ok(())
    }

    pub(in super::super) fn compile_defined_predicate_inference_application_in_current_environment(
        &mut self,
        application: &SuccessInferRuleApplicationResult,
        publication: DefinedPredicateInferenceConclusionPublication,
    ) -> Result<(), String> {
        let [premise] = application.premises.as_slice() else {
            return Err("defined-predicate inference must retain one source premise".into());
        };
        let source_fact_id = premise.fact_id.ok_or_else(|| {
            "defined-predicate inference source premise has no FactId".to_string()
        })?;
        let source_proof =
            resolve_fact_citation(&source_fact_id, &premise.fact, &self.environment_stack)?;
        let Fact::AtomicFact(AtomicFact::NormalAtomicFact(source_predicate)) = &premise.fact else {
            return Err(
                "defined-predicate inference premise is not a predicate application".into(),
            );
        };
        let (predicate_name, component_index) = match &application.rule {
            InferRule::DefinedPredicateParameterRequirementProjection(rule) => {
                (&rule.predicate_name, rule.parameter_index)
            }
            InferRule::DefinedPredicateDefinitionClauseProjection(rule) => {
                let binding = self
                    .environment_stack
                    .predicate_bindings
                    .get(&rule.predicate_name)
                    .ok_or_else(|| {
                        format!(
                            "defined predicate `{}` is not visible in this compiler environment",
                            rule.predicate_name
                        )
                    })?;
                (
                    &rule.predicate_name,
                    binding.requirement_count + rule.clause_index,
                )
            }
            _ => return Err("defined-predicate compiler received another infer rule".into()),
        };
        if source_predicate.predicate.to_string() != *predicate_name {
            return Err("defined-predicate inference changed its source predicate".into());
        }
        let binding = self
            .environment_stack
            .predicate_bindings
            .get(predicate_name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "defined predicate `{predicate_name}` is not visible in this compiler environment"
                )
            })?;
        let [conclusion] = application.conclusions.as_slice() else {
            return Err("defined-predicate inference must retain one conclusion Result".into());
        };
        let conclusion_fact_id = conclusion
            .fact_id
            .ok_or_else(|| "defined-predicate inference conclusion has no FactId".to_string())?;
        if let InferRule::DefinedPredicateParameterRequirementProjection(rule) = &application.rule {
            let definition = binding.definition.as_ref().ok_or_else(|| {
                "defined-predicate parameter projection has no concrete definition".to_string()
            })?;
            let parameters = definition
                .typed_parameters
                .collect_param_bindings_with_types();
            let (definition_parameter, parameter_type) =
                parameters.get(rule.parameter_index).ok_or_else(|| {
                    "defined-predicate parameter projection selected a missing parameter"
                        .to_string()
                })?;
            if matches!(
                parameter_type,
                ParamType::Obj(Obj::FnSet(_) | Obj::FiniteSeqSet(_) | Obj::SeqSet(_))
            ) {
                if binding.exact_parameters.get(rule.parameter_index) != Some(&true) {
                    return Err(
                        "concrete function parameter lost its exact-carrier ABI flag".into(),
                    );
                }
                let source_argument =
                    source_predicate
                        .body
                        .get(rule.parameter_index)
                        .ok_or_else(|| {
                            "defined-predicate function projection lost its source argument"
                                .to_string()
                        })?;
                let exact_argument = render_exact_predicate_function_argument(
                    source_argument,
                    &self.environment_stack,
                )?;
                let function = match parameter_type {
                    ParamType::Obj(Obj::FnSet(function)) => {
                        LeanTargetFunctionTypeRepresentation::lower(function)?
                    }
                    ParamType::Obj(Obj::FiniteSeqSet(sequence)) => {
                        let function = Runtime::default()
                            .finite_seq_set_to_fn_set(sequence, default_line_file());
                        LeanTargetFunctionTypeRepresentation::lower(&function)?
                    }
                    ParamType::Obj(Obj::SeqSet(sequence)) => {
                        let function =
                            Runtime::default().seq_set_to_fn_set(sequence, default_line_file());
                        LeanTargetFunctionTypeRepresentation::lower(&function)?
                    }
                    _ => unreachable!("guarded function-like parameter type"),
                };
                let function_set = render_function_set(&function, &self.environment_stack)?;
                let exact_parameter_proof =
                    format!("(Litex.In.own {function_set} {exact_argument})");
                if self
                    .environment_stack
                    .fact_propositions
                    .contains_key(&conclusion_fact_id)
                {
                    resolve_fact_citation(
                        &conclusion_fact_id,
                        &conclusion.fact,
                        &self.environment_stack,
                    )?;
                } else {
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    self.environment_stack
                        .fact_names
                        .insert(conclusion_fact_id, exact_parameter_proof.clone());
                    self.environment_stack
                        .fact_propositions
                        .insert(conclusion_fact_id, conclusion.fact.clone());
                    self.environment_stack
                        .fact_lean_propositions
                        .insert(conclusion_fact_id, conclusion_proposition);
                }
                let definition_well_definedness = binding
                    .definition_well_definedness
                    .as_ref()
                    .ok_or_else(|| {
                        "defined-predicate function parameter has no retained definition WD context"
                            .to_string()
                    })?;
                let definition_fact_id = definition_well_definedness
                    .parameter_fact_aliases
                    .iter()
                    .find(|alias| alias.symbol_id == definition_parameter.id())
                    .map(|alias| alias.fact_id)
                    .ok_or_else(|| {
                        "defined-predicate function parameter has no exact definition FactId alias"
                            .to_string()
                    })?;
                let mut current_function = self
                    .environment_stack
                    .function_bindings
                    .get(&conclusion_fact_id)
                    .cloned()
                    .unwrap_or(FunctionBinding {
                        symbol_id: definition_parameter.id(),
                        function: function.clone(),
                        membership_proof_name: exact_parameter_proof.clone(),
                        direct: true,
                    });
                current_function.symbol_id = definition_parameter.id();
                current_function.function = function;
                current_function.membership_proof_name = exact_parameter_proof.clone();
                current_function.direct = true;
                self.environment_stack
                    .function_bindings
                    .insert(definition_fact_id, current_function);
                self.environment_stack
                    .fact_names
                    .insert(definition_fact_id, exact_parameter_proof);
                self.environment_stack
                    .fact_propositions
                    .insert(definition_fact_id, conclusion.fact.clone());
            }
        }
        let components =
            instantiated_predicate_components(&premise.fact, &binding, &self.environment_stack)?;
        if component_index >= components.len() {
            return Err(format!(
                "defined-predicate inference selected component {component_index}, but `{predicate_name}` has {} components",
                components.len()
            ));
        }
        match &application.rule {
            InferRule::DefinedPredicateParameterRequirementProjection(rule)
                if rule.parameter_index >= binding.requirement_count =>
            {
                return Err(
                    "defined-predicate parameter projection left the requirement prefix".into(),
                );
            }
            InferRule::DefinedPredicateDefinitionClauseProjection(rule)
                if rule.clause_index >= binding.clause_count =>
            {
                return Err(
                    "defined-predicate clause projection left the definition clause range".into(),
                );
            }
            _ => {}
        }
        let conclusion_proposition = components[component_index].clone();
        let preserve_implicit_host_carrier = matches!(conclusion.fact, Fact::ForallFact(_));
        let proof_expression = if binding.dependent_parameter_evidence {
            let component_names = (0..components.len())
                .map(|index| format!("__component{index}"))
                .collect::<Vec<_>>();
            let selected_component = if preserve_implicit_host_carrier {
                format!("@{}", component_names[component_index])
            } else {
                component_names[component_index].clone()
            };
            format!(
                "(by\n  have __definition := {source_proof}\n  unfold {} at __definition\n  rcases __definition with \u{27e8}{}\u{27e9}\n  exact {})",
                binding.lean_name,
                component_names.join(", "),
                selected_component,
            )
        } else {
            let selector = conjunction_selector(component_index, components.len())?;
            let selected_component = if preserve_implicit_host_carrier {
                format!("@(__definition{selector})")
            } else {
                format!("__definition{selector}")
            };
            format!(
                "(by\n  have __definition := {source_proof}\n  unfold {} at __definition\n  exact {selected_component})",
                binding.lean_name,
            )
        };
        match self
            .environment_stack
            .fact_propositions
            .get(&conclusion_fact_id)
        {
            Some(_) => {
                resolve_fact_citation(
                    &conclusion_fact_id,
                    &conclusion.fact,
                    &self.environment_stack,
                )?;
            }
            None => {
                let proof_name = match publication {
                    DefinedPredicateInferenceConclusionPublication::PersistentLeanTheorem => {
                        let theorem_name = format!("__fact{}", self.next_fact_name_index);
                        self.declarations.push(format!(
                            "theorem {theorem_name} : {conclusion_proposition} := by\n  exact {proof_expression}"
                        ));
                        self.next_fact_name_index += 1;
                        theorem_name
                    }
                    DefinedPredicateInferenceConclusionPublication::LocalProofExpression => {
                        format!("(show {conclusion_proposition} from {proof_expression})")
                    }
                };
                self.environment_stack
                    .fact_names
                    .insert(conclusion_fact_id, proof_name);
                self.environment_stack
                    .fact_propositions
                    .insert(conclusion_fact_id, conclusion.fact.clone());
                self.environment_stack
                    .fact_lean_propositions
                    .insert(conclusion_fact_id, conclusion_proposition.clone());
            }
        }
        let direct_source_keys = conclusion
            .infers
            .rule_applications
            .iter()
            .filter(|application| {
                infer_rule_has_direct_compiler_environment_consumer(&application.rule)
            })
            .filter_map(|application| {
                application.premises.first().and_then(|premise| {
                    premise
                        .fact_id
                        .map(|fact_id| (fact_id, premise.fact.to_string()))
                })
            })
            .collect::<HashSet<_>>();
        let direct_infers = SuccessInferResult {
            store_fact_outputs: conclusion
                .infers
                .store_fact_outputs
                .iter()
                .filter(|output| {
                    output.fact_id.is_some_and(|fact_id| {
                        direct_source_keys.contains(&(
                            fact_id,
                            output.itself_and_why_itself_is_stored.0.to_string(),
                        ))
                    })
                })
                .cloned()
                .collect(),
            rule_applications: conclusion
                .infers
                .rule_applications
                .iter()
                .filter(|application| {
                    infer_rule_has_direct_compiler_environment_consumer(&application.rule)
                })
                .cloned()
                .collect(),
        };
        if !direct_infers.rule_applications.is_empty() {
            let allowed_sources = vec![(conclusion_fact_id, conclusion.fact.clone())];
            match publication {
                DefinedPredicateInferenceConclusionPublication::PersistentLeanTheorem => {
                    self.compile_typed_infer_result_as_top_level_declarations_with_allowed_sources(
                        &direct_infers,
                        &allowed_sources,
                        "defined-predicate nested direct inference",
                    )?;
                }
                DefinedPredicateInferenceConclusionPublication::LocalProofExpression => {
                    self.compile_typed_inference_results_in_current_compiler_environment(
                        &direct_infers,
                        &allowed_sources,
                        CompiledInferenceFactAvailabilityInLeanEnvironment::InlineProofExpression,
                        "defined-predicate nested direct inference",
                        None,
                    )?;
                }
            }
        }
        self.compile_defined_predicate_inference_results_in_current_environment(
            &conclusion.infers,
            publication,
        )?;
        validate_flattened_inferred_fact_ids_are_visible(
            &conclusion.infers,
            &self.environment_stack,
            "defined-predicate conclusion store",
        )?;
        Ok(())
    }
}
