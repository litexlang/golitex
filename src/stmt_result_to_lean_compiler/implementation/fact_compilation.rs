use super::*;

fn fact_proof_is_not_equal_from_strict_order(proof: &SuccessFactProofResult) -> bool {
    match proof {
        SuccessFactProofResult::BuiltinRule(builtin) => matches!(
            builtin.evidence.typed(),
            Some(BuiltinRuleEvidence::NotEqualFromStrictOrder)
        ),
        SuccessFactProofResult::Reuse(reuse) => {
            fact_proof_is_not_equal_from_strict_order(reuse.source.proof())
        }
        _ => false,
    }
}

impl StmtResultToLeanCompiler {
    /// A frozen proof/check Result may repeat an alpha-equivalent anonymous
    /// function under a fresh parser occurrence. Rebind that occurrence only
    /// when the active WD certificate has exactly one semantic owner. This is
    /// the fact-level analogue of witness aliasing and is deliberately scoped
    /// to the current compiler environment.
    pub(super) fn install_fact_anonymous_function_occurrence_aliases(
        &mut self,
        fact: &Fact,
        result_layer: &str,
    ) -> Result<(), String> {
        fn collect_from_object(
            object: &Obj,
            functions: &mut Vec<(SourceObjectOccurrenceId, String)>,
        ) {
            if let Obj::AnonymousFn(function) = object {
                if let Some(occurrence_id) = function.source_occurrence_id {
                    functions.push((occurrence_id, obj_equality_key(object)));
                }
            }
            // Function-application traversal treats the callable head as a
            // different structural field from ordinary arguments. Visit it
            // explicitly so an applied anonymous literal is not skipped.
            if let Obj::FnObj(application) = object {
                let head: Obj = application.head.as_ref().clone().into();
                collect_from_object(&head, functions);
            }
            let _: Result<bool, ()> = Runtime::same_shape_and_corresponding_args_match(
                object,
                object,
                &mut |child, _| {
                    collect_from_object(child, functions);
                    Ok(true)
                },
            );
        }

        fn collect_from_forall(
            forall: &ForallFact,
            functions: &mut Vec<(SourceObjectOccurrenceId, String)>,
        ) {
            for group in &forall.typed_parameters.groups {
                if let ParamType::Obj(carrier) = &group.param_type {
                    collect_from_object(carrier, functions);
                }
            }
            for premise in &forall.dom_facts {
                collect_from_fact(premise, functions);
            }
            for conclusion in &forall.then_facts {
                collect_from_fact(&conclusion.clone().to_fact(), functions);
            }
        }

        fn collect_from_fact(
            fact: &Fact,
            functions: &mut Vec<(SourceObjectOccurrenceId, String)>,
        ) {
            let arguments = match fact {
                Fact::AtomicFact(fact) => fact.get_args_from_fact_ref(),
                Fact::ExistFact(fact) => fact.get_args_from_fact_ref(),
                Fact::OrFact(fact) => fact.get_args_from_fact_ref(),
                Fact::AndFact(fact) => fact.get_args_from_fact_ref(),
                Fact::ChainFact(fact) => fact.get_args_from_fact_ref(),
                Fact::ForallFact(forall) => {
                    collect_from_forall(forall, functions);
                    return;
                }
                Fact::ForallFactWithIff(forall) => {
                    collect_from_forall(&forall.forall_fact, functions);
                    for conclusion in &forall.iff_facts {
                        collect_from_fact(&conclusion.clone().to_fact(), functions);
                    }
                    return;
                }
                Fact::NotForall(forall) => {
                    collect_from_forall(&forall.forall_fact, functions);
                    return;
                }
            };
            for argument in arguments {
                collect_from_object(argument, functions);
            }
        }

        let mut functions = Vec::new();
        collect_from_fact(fact, &mut functions);
        functions.sort_by_key(|(occurrence_id, _)| occurrence_id.value());
        functions.dedup_by_key(|(occurrence_id, _)| occurrence_id.value());
        if functions.is_empty() {
            return Ok(());
        }
        let context = self
            .environment_stack
            .well_definedness
            .as_mut()
            .ok_or_else(|| format!("{result_layer} has no active WD Result"))?;
        for (source_occurrence, semantic_key) in functions {
            if context.anonymous_functions.contains_key(&source_occurrence) {
                continue;
            }
            let owners = context
                .anonymous_functions
                .iter()
                .filter_map(|(owner_occurrence, certificate)| {
                    (obj_equality_key(&certificate.source_function) == semantic_key)
                        .then_some(*owner_occurrence)
                })
                .collect::<Vec<_>>();
            let [owner_occurrence] = owners.as_slice() else {
                return Err(format!(
                    "{result_layer} anonymous function occurrence {} has {} alpha-equivalent WD owners",
                    source_occurrence.value(),
                    owners.len()
                ));
            };
            if let Some(previous) = context
                .anonymous_function_occurrence_aliases
                .insert(source_occurrence, *owner_occurrence)
            {
                if previous != *owner_occurrence {
                    return Err(format!(
                        "{result_layer} anonymous function occurrence {} changed its WD owner",
                        source_occurrence.value()
                    ));
                }
            }
        }
        Ok(())
    }

    pub(super) fn compile_fact_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<(), String> {
        self.install_atomic_fact_well_definedness_store_results(result)
            .map_err(|error| format!("fact WD installation: {error}"))?;
        if self
            .compile_object_reflexivity_fact_result(result)
            .map_err(|error| format!("object-reflexivity route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_rational_normalization_fact_result(result)
            .map_err(|error| format!("rational-normalization route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_rational_algebraic_normalization_fact_result(result)
            .map_err(|error| format!("rational-algebraic-normalization route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_complex_algebraic_normalization_fact_result(result)
            .map_err(|error| format!("complex-algebraic-normalization route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_exact_fact_citation_result(result)
            .map_err(|error| format!("exact-citation route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_closed_standard_numeric_membership_fact_result(result)
            .map_err(|error| format!("closed-standard-numeric-membership route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_direct_standard_numeric_membership_with_inference(result)
            .map_err(|error| format!("standard-numeric-membership inference route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_direct_set_builder_membership_with_inference(result)
            .map_err(|error| format!("set-builder inference route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_direct_list_set_membership_with_inference(result)
            .map_err(|error| format!("list-set inference route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_registered_transitive_predicate_chain_with_inference(result)
            .map_err(|error| format!("registered transitive-chain inference route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_defined_predicate_fact_with_inference(result)
            .map_err(|error| format!("defined-predicate inference route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_direct_conjunction_fact_with_component_inference(result)
            .map_err(|error| format!("conjunction-component inference route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_direct_forall_fact_result(result)
            .map_err(|error| format!("forall route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_direct_fact_with_typed_inference(result)
            .map_err(|error| format!("generic typed-inference fact route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_direct_fact_without_inference(result)
            .map_err(|error| format!("direct fact route: {error}"))?
        {
            return Ok(());
        }
        Err(format!(
            "StmtResult-to-Lean compiler has no direct fact consumer for `{}` ({})",
            result.fact(),
            describe_success_fact_result_for_direct_compilation_audit(result),
        ))
    }

    /// `Combine`: publish an otherwise-direct fact proof, then consume every
    /// typed inference child from that source FactId in its retained order.
    /// Specialized fact families run before this method; this is the common
    /// path for proof evidence such as a Runtime-resolved numeric comparison
    /// whose ordinary store also owns supported inference Results.
    pub(super) fn compile_direct_fact_with_typed_inference(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        if result.store.infers.rule_applications.is_empty() {
            return Ok(false);
        }
        let source_fact = result.fact();
        if result.store.fact.to_string() != source_fact.to_string() {
            return Err("typed-inference fact changed between verification and store".into());
        }
        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "typed-inference fact store has no FactId".to_string())?;
        let source_outputs = result
            .store
            .infers
            .store_fact_outputs
            .iter()
            .filter(|output| {
                output.fact_id == Some(source_fact_id)
                    && output.itself_and_why_itself_is_stored.0.to_string()
                        == source_fact.to_string()
            })
            .collect::<Vec<_>>();
        let [source_output] = source_outputs.as_slice() else {
            return Err("typed-inference fact must retain one exact source store output".into());
        };
        if source_output.inferred_facts.len() != source_output.inferred_fact_ids.len() {
            return Err("typed-inference fact changed its inferred FactId arity".into());
        }
        let Some(proof) = self.construct_lean_proof_from_direct_fact_result(result)? else {
            return Ok(false);
        };
        if matches!(source_fact, Fact::AtomicFact(_)) {
            validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        }
        let proposition = render_fact(&source_fact, &self.environment_stack)?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {proposition} := by\n  exact {proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, theorem_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact.clone());
        self.next_fact_name_index += 1;
        let allowed_sources = self
            .install_equality_chain_adjacent_projections_for_typed_inference(
                &source_fact,
                source_fact_id,
                &theorem_name,
                &result.store.infers,
                "typed-inference fact Result",
            )?;
        self.compile_typed_infer_result_as_top_level_declarations_with_allowed_sources(
            &result.store.infers,
            &allowed_sources,
            "typed-inference fact Result",
        )?;
        Ok(true)
    }

    /// `Combine`: publish the proved conjunction once, then bind every exact
    /// inferred component FactId to its structural Lean projection. Later
    /// Results cite those identities through the ordinary compiler stack.
    pub(super) fn compile_direct_conjunction_fact_with_component_inference(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let source_fact = result.fact();
        let Fact::AndFact(source_conjunction) = &source_fact else {
            return Ok(false);
        };
        if result.store.infers.rule_applications.is_empty()
            || result
                .store
                .infers
                .rule_applications
                .iter()
                .any(|application| {
                    !matches!(application.rule, InferRule::ConjunctionImpliesComponent(_))
                })
        {
            return Ok(false);
        }
        if result.store.fact.to_string() != source_fact.to_string() {
            return Err("conjunction changed between verification and store".into());
        }
        let components = source_conjunction
            .facts
            .iter()
            .cloned()
            .map(Fact::from)
            .collect::<Vec<_>>();
        let (source_fact_id, component_fact_ids) =
            validate_conjunction_store_and_component_inference_results(
                &result.store.infers,
                &source_fact,
                &components,
                "conjunction fact store",
            )?;
        let Some(source_proof) =
            self.construct_lean_proof_from_direct_fact_result_using_its_well_definedness(result)?
        else {
            return Ok(false);
        };
        let source_proposition = render_fact(&source_fact, &self.environment_stack)?;
        let source_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {source_theorem_name} : {source_proposition} := by\n  exact {source_proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, source_theorem_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact);
        self.next_fact_name_index += 1;

        for (component_index, (component, component_fact_id)) in components
            .iter()
            .zip(component_fact_ids.into_iter())
            .enumerate()
        {
            let projection = conjunction_projection(
                &format!("({source_theorem_name})"),
                component_index,
                components.len(),
            )?;
            self.environment_stack
                .fact_names
                .insert(component_fact_id, projection);
            self.environment_stack
                .fact_propositions
                .insert(component_fact_id, component.clone());
        }
        for (component_index, application) in
            result.store.infers.rule_applications.iter().enumerate()
        {
            let [component] = application.conclusions.as_slice() else {
                return Err(format!(
                    "conjunction component {component_index} lost its nested inference Result"
                ));
            };
            self.compile_defined_predicate_inference_results_in_current_environment(
                &component.infers,
                DefinedPredicateInferenceConclusionPublication::PersistentLeanTheorem,
            )?;
        }
        validate_flattened_inferred_fact_ids_are_visible(
            &result.store.infers,
            &self.environment_stack,
            "conjunction fact store",
        )?;
        Ok(true)
    }

    /// `Combine`: publish the exact proved predicate application, then consume
    /// its typed parameter-requirement and definition-clause projection
    /// children. Every conclusion is installed under its retained FactId in
    /// the current compiler environment before its own nested infer Result is
    /// entered.
    pub(super) fn compile_defined_predicate_fact_with_inference(
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
    pub(super) fn compile_defined_predicate_inference_results_in_current_environment(
        &mut self,
        infer_result: &SuccessInferResult,
        publication: DefinedPredicateInferenceConclusionPublication,
    ) -> Result<(), String> {
        for application in &infer_result.rule_applications {
            if !defined_predicate_infer_rule(&application.rule) {
                continue;
            }
            self.compile_defined_predicate_inference_application_in_current_environment(
                application,
                publication,
            )?;
        }
        Ok(())
    }

    pub(super) fn compile_defined_predicate_inference_application_in_current_environment(
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
                resolve_fact_citation(
                    &conclusion_fact_id,
                    &conclusion.fact,
                    &self.environment_stack,
                )?;
                if binding
                    .exact_parameters
                    .get(rule.parameter_index)
                    != Some(&true)
                {
                    return Err(
                        "concrete function parameter lost its exact-carrier ABI flag".into(),
                    );
                }
                let source_argument = source_predicate
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
                        let function = Runtime::default()
                            .seq_set_to_fn_set(sequence, default_line_file());
                        LeanTargetFunctionTypeRepresentation::lower(&function)?
                    }
                    _ => unreachable!("guarded function-like parameter type"),
                };
                let function_set = render_function_set(&function, &self.environment_stack)?;
                let exact_parameter_proof =
                    format!("(Litex.In.own {function_set} {exact_argument})");
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
                self.environment_stack.fact_names.insert(
                    definition_fact_id,
                    exact_parameter_proof,
                );
                self.environment_stack.fact_propositions.insert(
                    definition_fact_id,
                    conclusion.fact.clone(),
                );
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
        let proof_expression = if binding.dependent_parameter_evidence {
            let component_names = (0..components.len())
                .map(|index| format!("__component{index}"))
                .collect::<Vec<_>>();
            format!(
                "(by\n  have __definition := {source_proof}\n  unfold {} at __definition\n  rcases __definition with \u{27e8}{}\u{27e9}\n  exact {})",
                binding.lean_name,
                component_names.join(", "),
                component_names[component_index],
            )
        } else {
            let selector = conjunction_selector(component_index, components.len())?;
            format!(
                "(by\n  have __definition := {source_proof}\n  unfold {} at __definition\n  exact __definition{selector})",
                binding.lean_name
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
                        format!(
                            "(show {conclusion_proposition} from {proof_expression})"
                        )
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

    /// `Combine`: publish the proved source chain, expose each retained chain
    /// component FactId as a projection from that theorem in the current
    /// compiler environment, then fold the visible registered transitivity
    /// theorem over every typed inference application's ordered premises.
    pub(super) fn compile_registered_transitive_predicate_chain_with_inference(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let has_registered_transitive_application = result
            .store
            .infers
            .rule_applications
            .iter()
            .any(|application| {
                matches!(
                    application.rule,
                    InferRule::RegisteredTransitivePredicateChainClosure(_)
                )
            });
        if !has_registered_transitive_application {
            return Ok(false);
        }
        let source_fact = result.fact();
        let Fact::ChainFact(chain) = &source_fact else {
            return Err(
                "registered transitive-chain inference retained a non-chain source fact".into(),
            );
        };
        if result.store.fact.to_string() != source_fact.to_string() {
            return Err(
                "registered transitive chain changed between verification and store".into(),
            );
        }
        let adjacent_facts = chain
            .facts()
            .map_err(|error| format!("invalid registered transitive chain: {error:?}"))?
            .into_iter()
            .map(Fact::from)
            .collect::<Vec<_>>();
        if adjacent_facts.len() < 2 {
            return Err(
                "registered transitive inference retained a chain with fewer than two edges".into(),
            );
        }
        validate_chain_fact_well_definedness_result(
            &result.well_definedness,
            chain,
            &adjacent_facts,
        )?;

        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "registered transitive chain store has no FactId".to_string())?;
        let Some(source_proof) =
            self.construct_lean_proof_from_direct_fact_result_using_its_well_definedness(result)?
        else {
            return Ok(false);
        };
        let source_proposition = render_fact(&source_fact, &self.environment_stack)?;
        let source_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {source_theorem_name} : {source_proposition} := by\n  exact {source_proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, source_theorem_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact.clone());
        self.next_fact_name_index += 1;

        let expected_application_count = (1..adjacent_facts.len())
            .map(|distance| distance)
            .sum::<usize>();
        if result.store.infers.rule_applications.len() != expected_application_count {
            return Err(format!(
                "registered transitive chain expected {expected_application_count} closure applications, retained {}",
                result.store.infers.rule_applications.len()
            ));
        }
        let mut adjacent_fact_ids = vec![None; adjacent_facts.len()];
        let mut expected_conclusions = Vec::with_capacity(expected_application_count);
        let mut expected_application_index = 0;
        for start_object_index in 0..chain.objs.len() {
            for end_object_index in start_object_index + 2..chain.objs.len() {
                let application =
                    &result.store.infers.rule_applications[expected_application_index];
                expected_application_index += 1;
                let InferRule::RegisteredTransitivePredicateChainClosure(rule) = &application.rule
                else {
                    return Err(
                        "registered transitive chain mixed another typed inference rule into its closure"
                            .into(),
                    );
                };
                let predicate_name = chain.prop_names[0].to_string();
                if rule.predicate_name != predicate_name
                    || rule.start_object_index != start_object_index
                    || rule.end_object_index != end_object_index
                {
                    return Err(format!(
                        "registered transitive-chain application {} changed its predicate or object interval",
                        expected_application_index - 1
                    ));
                }
                let expected_premises = &adjacent_facts[start_object_index..end_object_index];
                if application.premises.len() != expected_premises.len() {
                    return Err(format!(
                        "registered transitive-chain application {} changed its premise arity",
                        expected_application_index - 1
                    ));
                }
                for (offset, (premise, expected_fact)) in application
                    .premises
                    .iter()
                    .zip(expected_premises.iter())
                    .enumerate()
                {
                    if premise.fact.to_string() != expected_fact.to_string() {
                        return Err(format!(
                            "registered transitive-chain application {} changed premise {offset}",
                            expected_application_index - 1
                        ));
                    }
                    let fact_id = premise.fact_id.ok_or_else(|| {
                        format!(
                            "registered transitive-chain application {} premise {offset} has no FactId",
                            expected_application_index - 1
                        )
                    })?;
                    let adjacent_index = start_object_index + offset;
                    match adjacent_fact_ids[adjacent_index] {
                        Some(existing) if existing != fact_id => {
                            return Err(format!(
                                "registered transitive chain assigned two FactIds to adjacent edge {adjacent_index}"
                            ));
                        }
                        _ => adjacent_fact_ids[adjacent_index] = Some(fact_id),
                    }
                }
                let [conclusion] = application.conclusions.as_slice() else {
                    return Err(format!(
                        "registered transitive-chain application {} must retain one conclusion",
                        expected_application_index - 1
                    ));
                };
                let expected_conclusion: Fact = NormalAtomicFact::new(
                    chain.prop_names[0].clone(),
                    vec![
                        chain.objs[start_object_index].clone(),
                        chain.objs[end_object_index].clone(),
                    ],
                    chain.line_file.clone(),
                )
                .into();
                if conclusion.fact.to_string() != expected_conclusion.to_string() {
                    return Err(format!(
                        "registered transitive-chain application {} changed its conclusion",
                        expected_application_index - 1
                    ));
                }
                let conclusion_fact_id = validate_success_store_fact_result(
                    conclusion,
                    &expected_conclusion,
                    &format!(
                        "registered transitive-chain application {} conclusion",
                        expected_application_index - 1
                    ),
                )?;
                expected_conclusions.push((expected_conclusion, conclusion_fact_id));
            }
        }
        for (index, (fact, fact_id)) in adjacent_facts
            .iter()
            .zip(adjacent_fact_ids.into_iter())
            .enumerate()
        {
            let fact_id = fact_id.ok_or_else(|| {
                format!("registered transitive chain lost adjacent edge {index} FactId")
            })?;
            let projection = conjunction_projection(
                &format!("({source_theorem_name})"),
                index,
                adjacent_facts.len(),
            )?;
            self.environment_stack
                .fact_names
                .insert(fact_id, projection);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, fact.clone());
        }

        let mut seen_flattened_conclusions = HashSet::new();
        let unique_expected_conclusions = expected_conclusions
            .iter()
            .filter(|(fact, _)| seen_flattened_conclusions.insert(fact.to_string()))
            .collect::<Vec<_>>();
        let [source_store_output] = result.store.infers.store_fact_outputs.as_slice() else {
            return Err(
                "registered transitive chain must retain one flattened source store output".into(),
            );
        };
        if source_store_output.fact_id != Some(source_fact_id)
            || source_store_output
                .itself_and_why_itself_is_stored
                .0
                .to_string()
                != source_fact.to_string()
            || source_store_output.inferred_facts.len() != unique_expected_conclusions.len()
            || source_store_output.inferred_fact_ids.len() != unique_expected_conclusions.len()
        {
            return Err(
                "registered transitive chain source store disagrees with its typed closure".into(),
            );
        }
        for (index, ((stored_fact, stored_fact_id), (expected_fact, expected_fact_id))) in
            source_store_output
                .inferred_facts
                .iter()
                .zip(source_store_output.inferred_fact_ids.iter())
                .zip(unique_expected_conclusions.iter())
                .enumerate()
        {
            if stored_fact.to_string() != expected_fact.to_string()
                || *stored_fact_id != Some(*expected_fact_id)
            {
                return Err(format!(
                    "registered transitive chain flattened closure output {index} changed its fact or FactId"
                ));
            }
        }
        for (application, (expected_fact, expected_fact_id)) in result
            .store
            .infers
            .rule_applications
            .iter()
            .zip(expected_conclusions.iter())
        {
            self.compile_registered_transitive_predicate_chain_inference_application(
                application,
                expected_fact,
                *expected_fact_id,
            )?;
        }
        Ok(true)
    }

    pub(super) fn compile_registered_transitive_predicate_chain_inference_application(
        &mut self,
        application: &SuccessInferRuleApplicationResult,
        expected_conclusion: &Fact,
        expected_conclusion_fact_id: FactId,
    ) -> Result<(), String> {
        let InferRule::RegisteredTransitivePredicateChainClosure(rule) = &application.rule else {
            return Err("registered transitive compiler received another inference rule".into());
        };
        let binding = self
            .environment_stack
            .registered_transitive_predicate_theorem_bindings
            .get(&rule.predicate_name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "registered transitivity theorem for `{}` is not visible in this compiler environment",
                    rule.predicate_name
                )
            })?;
        let Some(first_premise) = application.premises.first() else {
            return Err("registered transitive application retained no premises".into());
        };
        let first_fact_id = first_premise.fact_id.ok_or_else(|| {
            "registered transitive application first premise has no FactId".to_string()
        })?;
        let mut current_fact = first_premise.fact.clone();
        let mut current_proof =
            resolve_fact_citation(&first_fact_id, &current_fact, &self.environment_stack)?;
        for (index, next_premise) in application.premises.iter().enumerate().skip(1) {
            let next_fact_id = next_premise.fact_id.ok_or_else(|| {
                format!("registered transitive application premise {index} has no FactId")
            })?;
            let next_proof =
                resolve_fact_citation(&next_fact_id, &next_premise.fact, &self.environment_stack)?;
            let (next_conclusion, parameter_arguments) =
                instantiate_registered_transitive_predicate_application(
                    &binding.forall_fact,
                    &rule.predicate_name,
                    &current_fact,
                    &next_premise.fact,
                )?;
            let mut theorem_application = binding.theorem_name.clone();
            for argument in parameter_arguments {
                theorem_application.push(' ');
                theorem_application.push_str(&render_obj(&argument, &self.environment_stack)?);
            }
            theorem_application.push_str(&format!(" ({current_proof}) ({next_proof})"));
            current_fact = next_conclusion;
            current_proof = theorem_application;
        }
        if current_fact.to_string() != expected_conclusion.to_string() {
            return Err(
                "registered transitive theorem fold changed its retained conclusion".into(),
            );
        }
        let proposition = render_fact(expected_conclusion, &self.environment_stack)?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {proposition} := by\n  exact {current_proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(expected_conclusion_fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(expected_conclusion_fact_id, expected_conclusion.clone());
        self.next_fact_name_index += 1;
        Ok(())
    }

    /// Common `Leaf` / `Wrap` fact publication path. Proof construction reads
    /// the recursive Result directly, while this statement layer owns the
    /// exact store FactId and Lean declaration. Facts with inference children
    /// stay in their dedicated `Combine` paths until those typed infer Results
    /// are migrated.
    pub(super) fn compile_direct_fact_without_inference(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        // Binder-owning forall Results have a dedicated compiler layer.
        // In particular, Runtime may publish reduced-binder projections when
        // a conclusion omits source parameters; the generic stored-fact path
        // must not consume that structured store shape first.
        if matches!(result.proof(), SuccessFactProofResult::ForallProof(_)) {
            return Ok(false);
        }
        if fact_result_contains_inferred_facts(result)
            || !result.store.infers.rule_applications.is_empty()
        {
            return Ok(false);
        }
        let Some(proof) = self
            .construct_lean_proof_from_direct_fact_result_using_its_well_definedness(result)
            .map_err(|error| format!("direct fact proof construction: {error}"))?
        else {
            return Ok(false);
        };
        if matches!(result.fact(), Fact::AtomicFact(_)) {
            validate_atomic_fact_well_definedness_result(&result.well_definedness, &result.fact())
                .map_err(|error| format!("direct fact WD validation: {error}"))?;
        }
        self.compile_stored_fact_without_inference(result, proof)
            .map_err(|error| format!("direct fact publication: {error}"))?;
        Ok(true)
    }

    /// `Combine`: enter the binder owned by a `ForallProof`, install its
    /// parameter SymbolIds and FactIds in one inherited compiler environment,
    /// install any zero-extra-inference domain FactIds, compile the ordered
    /// conclusion Results there, then pop before publishing the outer forall
    /// theorem. Typed inference children are validated and either compiled as
    /// local `have` declarations or installed as exact target bindings in the
    /// same binder environment.
    pub(super) fn compile_direct_forall_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::ForallProof(proof) = result.proof() else {
            return Ok(false);
        };
        let Fact::ForallFact(source_forall) = result.fact() else {
            return Err("ForallProof Result retained a non-forall target".into());
        };
        if source_forall.to_string() != proof.forall_fact.to_string() {
            return Err("ForallProof Result changed its source forall".into());
        }
        if proof
            .assumption_infers
            .rule_applications
            .iter()
            .any(|application| {
                !infer_rule_has_direct_compiler_environment_consumer(&application.rule)
            })
        {
            return self.direct_forall_result_is_not_yet_supported(
                "its assumption inference contains a typed rule without a direct compiler-environment consumer",
            );
        }
        if !infer_result_effects_are_fully_owned_by_direct_compiler_rules(&proof.assumption_infers)
        {
            return Err(format!(
                "direct ForallProof compiler found flattened assumption effects without matching typed rules: {:?}",
                proof.assumption_infers.store_fact_outputs
            ));
        }
        let publication_selections =
            direct_forall_result_publication_selections(result, &source_forall)?;
        let Some(SuccessVerifyFactWellDefinedProofResult::ForallFact(well_definedness)) =
            result.well_definedness.recursive.as_deref()
        else {
            return Err("ForallProof Result retained no recursive forall well-definedness".into());
        };
        if well_definedness.statement.to_string() != source_forall.to_string()
            || well_definedness.premises.len() != source_forall.dom_facts.len()
            || well_definedness.conclusions.len() != source_forall.then_facts.len()
            || proof.proves.len() != source_forall.then_facts.len()
        {
            return Err("ForallProof well-definedness or conclusion arity changed".into());
        }
        // One recursive forall WD tree owns the binder and every named
        // premise/conclusion child. Keep that whole tree active while a child
        // proof is rendered; projecting a conclusion in isolation would lose
        // the parent-owned function-prefix and binder context.
        let forall_well_definedness =
            self.construct_well_definedness_to_lean_compilation_context(&result.well_definedness)?;

        let source_parameters = source_forall
            .typed_parameters
            .collect_param_bindings_with_types();
        let source_well_defined_parameters = well_definedness
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
        if source_well_defined_parameters.len() != source_parameters.len() {
            return Err("ForallProof binder changed its parameter arity".into());
        }
        let source_parameter_facts = source_well_defined_parameters
            .iter()
            .map(|(_, parameter)| parameter.proposition.clone())
            .collect::<Vec<_>>();
        // The proof Result, not the flat inference-effect list or the sibling
        // WD Result, owns the identities installed in this lexical frame.
        // A repeated domain premise therefore carries the same exact FactId
        // as its earlier parameter assumption without creating another store
        // output.
        if proof.parameter_assumptions.len() != source_parameter_facts.len()
            || proof.domain_assumptions.len() != source_forall.dom_facts.len()
        {
            return Err("ForallProof changed its proof-scope assumption arity".into());
        }
        let mut source_parameter_fact_ids = Vec::with_capacity(source_parameter_facts.len());
        for (parameter_index, (expected, retained)) in source_parameter_facts
            .iter()
            .zip(proof.parameter_assumptions.iter())
            .enumerate()
        {
            if retained.fact.to_string() != expected.to_string() {
                return Err(format!(
                    "ForallProof parameter assumption {parameter_index} changed its fact"
                ));
            }
            source_parameter_fact_ids.push(retained.fact_id);
        }
        let mut source_premise_fact_ids = Vec::with_capacity(source_forall.dom_facts.len());
        for (premise_index, ((source_premise, retained), well_defined_premise)) in source_forall
            .dom_facts
            .iter()
            .zip(proof.domain_assumptions.iter())
            .zip(well_definedness.premises.iter())
            .enumerate()
        {
            if retained.fact.to_string() != source_premise.to_string()
                || well_defined_premise.proposition.to_string() != source_premise.to_string()
                || well_defined_premise.store.fact.to_string() != source_premise.to_string()
            {
                return Err(format!(
                    "ForallProof domain premise {premise_index} changed its source proposition"
                ));
            }
            source_premise_fact_ids.push(retained.fact_id);
        }
        for (fact, fact_id) in source_parameter_facts
            .iter()
            .zip(source_parameter_fact_ids.iter())
            .chain(
                source_forall
                    .dom_facts
                    .iter()
                    .zip(source_premise_fact_ids.iter()),
            )
        {
            if !infer_result_retains_fact_id(&proof.assumption_infers, fact, *fact_id) {
                return Err(format!(
                    "ForallProof assumption effects do not retain exact FactId `{fact_id}` for `{fact}`"
                ));
            }
        }

        for publication_selection in publication_selections {
            let parameters = publication_selection
                .source_parameter_indices
                .iter()
                .map(|source_index| source_parameters[*source_index].clone())
                .collect::<Vec<_>>();
            let well_defined_parameters = publication_selection
                .source_parameter_indices
                .iter()
                .map(|source_index| source_well_defined_parameters[*source_index])
                .collect::<Vec<_>>();
            let parameter_facts = publication_selection
                .source_parameter_indices
                .iter()
                .map(|source_index| source_parameter_facts[*source_index].clone())
                .collect::<Vec<_>>();
            let parameter_fact_ids = publication_selection
                .source_parameter_indices
                .iter()
                .map(|source_index| source_parameter_fact_ids[*source_index])
                .collect::<Vec<_>>();
            let premise_fact_ids = source_premise_fact_ids.clone();

            self.environment_stack.push_inherited_environment();
            self.environment_stack.well_definedness = Some(forall_well_definedness.clone());
            let compilation: Result<Option<CompiledDirectForallProofBody>, String> = (|| {
                let mut intro_names = Vec::new();
                let mut parameter_premises = Vec::with_capacity(parameters.len());
                // The whole binder Result is visible at once. Install every exact
                // domain identity before rendering parameter aliases because a
                // parameter-associated function application in the WD tree may
                // already cite one of these domain facts.
                for (premise_index, ((source_premise, well_defined_premise), fact_id)) in
                    source_forall
                        .dom_facts
                        .iter()
                        .zip(well_definedness.premises.iter())
                        .zip(premise_fact_ids.iter())
                        .enumerate()
                {
                    let premise_name = format!("__domain{}", premise_index + 1);
                    self.environment_stack
                        .fact_names
                        .insert(*fact_id, premise_name.clone());
                    self.environment_stack
                        .fact_propositions
                        .insert(*fact_id, source_premise.clone());
                    let well_definedness_fact_id = well_defined_premise
                        .store
                        .fact_id
                        .expect("validated before entering the compiler environment");
                    self.environment_stack
                        .fact_names
                        .insert(well_definedness_fact_id, premise_name);
                    self.environment_stack
                        .fact_propositions
                        .insert(well_definedness_fact_id, source_premise.clone());
                }
                for (
                    parameter_index,
                    ((((binding, parameter_type), (group, parameter)), fact), fact_id),
                ) in parameters
                    .iter()
                    .zip(well_defined_parameters.iter())
                    .zip(parameter_facts.iter())
                    .zip(parameter_fact_ids.iter())
                    .enumerate()
                {
                    if group.parameter_type.to_string() != parameter_type.to_string()
                        || parameter.symbol_id != Some(binding.id())
                        || parameter.proposition.to_string() != fact.to_string()
                    {
                        return Err(format!(
                        "ForallProof parameter {parameter_index} changed its type, SymbolId, or proposition"
                    ));
                    }
                    let parameter_name = lean_identifier(binding.name());
                    if self
                        .environment_stack
                        .symbol_names
                        .insert(binding.id(), parameter_name.clone())
                        .is_some()
                    {
                        return Err(format!(
                            "ForallProof parameter {parameter_index} reused its SymbolId"
                        ));
                    }
                    if matches!(parameter_type, ParamType::Obj(set) if matches!(set, Obj::FnSet(_)) || set_requires_heterogeneous_carrier(set))
                    {
                        // `render_forall_fact_type` represents these source
                        // objects with an implicit carrier followed by the value.
                        // Tactic `intro` also consumes implicit binders, so the
                        // proof layer must name that carrier before introducing
                        // the source parameter itself.
                        intro_names.push(format!("__carrier{}", parameter_index + 1));
                    }
                    intro_names.push(parameter_name.clone());
                    parameter_premises.push(LeanLocalFactPremise::new(*fact_id, fact.clone()));

                    match parameter_type {
                        ParamType::Set(_) => {
                            validate_set_parameter_premise(binding.id(), fact)?;
                        }
                        ParamType::Obj(set) => {
                            validate_object_parameter_premise(binding.id(), set, fact)?;
                            let native_integer_parameter =
                                matches!(set, Obj::StandardSet(StandardSet::Z));
                            if native_integer_parameter {
                                install_structured_induction_native_integer_symbol(
                                    binding.id(),
                                    &parameter_name,
                                    &mut self.environment_stack,
                                );
                            } else if forall_parameter_uses_exact_refined_numeric_carrier(set) {
                                let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
                                self.environment_stack
                                    .exact_carrier_values
                                    .insert(binding.id(), parameter_name.clone());
                                self.environment_stack
                                    .exact_positive_real_carriers
                                    .insert(binding.id(), parameter_name.clone());
                                if let Some(real) =
                                    exact_set_real_value(&lowered_set, &parameter_name)
                                {
                                    self.environment_stack
                                        .numeric_real_values
                                        .insert(binding.id(), real);
                                }
                                if let Some(integer) =
                                    exact_set_integer_value(&lowered_set, &parameter_name)
                                {
                                    self.environment_stack
                                        .numeric_integer_values
                                        .insert(binding.id(), integer);
                                }
                                if let Some(rational) =
                                    exact_set_rational_value(&lowered_set, &parameter_name)
                                {
                                    self.environment_stack
                                        .numeric_rational_values
                                        .insert(binding.id(), rational);
                                }
                                if let Some(numeric) =
                                    exact_set_numeric_value(&lowered_set, &parameter_name)
                                {
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
                                if let Some(proof) =
                                    exact_set_numeric_proof(&lowered_set, &parameter_name)
                                {
                                    self.environment_stack
                                        .numeric_representation_memberships
                                        .insert(binding.id(), proof);
                                }
                            }
                            let proposition = render_fact(fact, &self.environment_stack).map_err(
                            |error| {
                                format!(
                                    "ForallProof parameter {parameter_index} failed to render: {error}"
                                )
                            },
                        )?;
                            let hypothesis = if native_integer_parameter {
                                format!("(Litex.In.own Litex.Z {parameter_name})")
                            } else {
                                let hypothesis = format!("__h{}", fact_id.value());
                                intro_names.push(hypothesis.clone());
                                hypothesis
                            };
                            self.environment_stack
                                .fact_names
                                .insert(*fact_id, hypothesis.clone());
                            self.environment_stack
                                .fact_propositions
                                .insert(*fact_id, fact.clone());
                            let well_definedness_fact_ids =
                                exact_ordered_fact_ids_from_store_results(
                                    &parameter.infers,
                                    std::slice::from_ref(fact),
                                    &format!("ForallProof WD parameter {parameter_index}"),
                                )?;
                            let [well_definedness_fact_id] = well_definedness_fact_ids.as_slice()
                            else {
                                return Err(format!(
                                "ForallProof WD parameter {parameter_index} retained the wrong store arity"
                            ));
                            };
                            self.environment_stack
                                .fact_names
                                .insert(*well_definedness_fact_id, hypothesis.clone());
                            self.environment_stack
                                .fact_propositions
                                .insert(*well_definedness_fact_id, fact.clone());
                            install_parameter_fact_aliases(
                                binding.id(),
                                *fact_id,
                                fact,
                                &hypothesis,
                                set,
                                &mut self.environment_stack,
                            )
                            .map_err(|error| {
                                format!(
                                    "ForallProof parameter {parameter_index} aliases failed to install: {error}"
                                )
                            })?;
                            if native_integer_parameter {
                                // Generic membership aliases select `In.rep`.
                                // This binder is already the exact `Z.Carrier`,
                                // so restore the direct native observation used
                                // by `render_forall_fact_type` and `callOwn`.
                                install_structured_induction_native_integer_symbol(
                                    binding.id(),
                                    &parameter_name,
                                    &mut self.environment_stack,
                                );
                            } else if forall_parameter_uses_exact_refined_numeric_carrier(set) {
                                let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
                                self.environment_stack
                                    .exact_carrier_values
                                    .insert(binding.id(), parameter_name.clone());
                                self.environment_stack
                                    .exact_positive_real_carriers
                                    .insert(binding.id(), parameter_name.clone());
                                if let Some(real) =
                                    exact_set_real_value(&lowered_set, &parameter_name)
                                {
                                    self.environment_stack
                                        .numeric_real_values
                                        .insert(binding.id(), real);
                                }
                                if let Some(integer) =
                                    exact_set_integer_value(&lowered_set, &parameter_name)
                                {
                                    self.environment_stack
                                        .numeric_integer_values
                                        .insert(binding.id(), integer);
                                }
                                if let Some(rational) =
                                    exact_set_rational_value(&lowered_set, &parameter_name)
                                {
                                    self.environment_stack
                                        .numeric_rational_values
                                        .insert(binding.id(), rational);
                                }
                                if let Some(numeric) =
                                    exact_set_numeric_value(&lowered_set, &parameter_name)
                                {
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
                                if let Some(proof) =
                                    exact_set_numeric_proof(&lowered_set, &parameter_name)
                                {
                                    self.environment_stack
                                        .numeric_representation_memberships
                                        .insert(binding.id(), proof);
                                }
                            }
                            let expected = format!(
                                "Litex.In {parameter_name} {}",
                                render_obj(set, &self.environment_stack)?
                            );
                            if proposition != expected {
                                return Err(format!(
                                "ForallProof parameter {parameter_index} rendered `{proposition}` instead of `{expected}`"
                            ));
                            }
                        }
                        ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {
                            validate_refined_set_parameter_premise(
                                binding.id(),
                                parameter_type,
                                fact,
                            )?;
                            let proposition = render_fact(fact, &self.environment_stack)?;
                            let hypothesis = format!("__h{}", fact_id.value());
                            intro_names.push(hypothesis.clone());
                            self.environment_stack
                                .fact_names
                                .insert(*fact_id, hypothesis.clone());
                            self.environment_stack
                                .fact_propositions
                                .insert(*fact_id, fact.clone());
                            let well_definedness_fact_ids =
                                exact_ordered_fact_ids_from_store_results(
                                    &parameter.infers,
                                    std::slice::from_ref(fact),
                                    &format!("ForallProof WD parameter {parameter_index}"),
                                )?;
                            let [well_definedness_fact_id] = well_definedness_fact_ids.as_slice()
                            else {
                                return Err(format!(
                                "ForallProof WD parameter {parameter_index} retained the wrong store arity"
                            ));
                            };
                            self.environment_stack
                                .fact_names
                                .insert(*well_definedness_fact_id, hypothesis.clone());
                            self.environment_stack
                                .fact_propositions
                                .insert(*well_definedness_fact_id, fact.clone());
                            install_rendered_parameter_aliases(
                                binding.id(),
                                &proposition,
                                &hypothesis,
                                None,
                                &mut self.environment_stack,
                            )?;
                        }
                    }
                }

                let mut premises = Vec::with_capacity(source_forall.dom_facts.len());
                for (premise_index, ((source_premise, _well_defined_premise), fact_id)) in
                    source_forall
                        .dom_facts
                        .iter()
                        .zip(well_definedness.premises.iter())
                        .zip(premise_fact_ids.iter())
                        .enumerate()
                {
                    let source_premise = source_premise.clone();
                    let premise_name = format!("__domain{}", premise_index + 1);
                    render_fact(&source_premise, &self.environment_stack).map_err(|error| {
                    format!(
                        "ForallProof domain premise {premise_index} failed before installation: {error}"
                    )
                })?;
                    intro_names.push(premise_name.clone());
                    premises.push(LeanLocalFactPremise::new(*fact_id, source_premise));
                }

                let mut proof_lines = Vec::with_capacity(
                    publication_selection.source_conclusion_indices.len()
                        + proof.assumption_infers.rule_applications.len()
                        + 2,
                );
                let visible_assumption_sources = parameter_facts
                    .iter()
                    .cloned()
                    .zip(parameter_fact_ids.iter().copied())
                    .chain(
                        source_forall
                            .dom_facts
                            .iter()
                            .cloned()
                            .zip(premise_fact_ids.iter().copied()),
                    )
                    .map(|(fact, fact_id)| (fact_id, fact))
                    .collect::<Vec<_>>();
                let complete_assumption_sources = source_parameter_facts
                    .iter()
                    .cloned()
                    .zip(source_parameter_fact_ids.iter().copied())
                    .chain(
                        source_forall
                            .dom_facts
                            .iter()
                            .cloned()
                            .zip(source_premise_fact_ids.iter().copied()),
                    )
                    .map(|(fact, fact_id)| (fact_id, fact))
                    .collect::<Vec<_>>();
                let visible_assumption_infers =
                    select_typed_inference_results_for_visible_forall_sources(
                        &proof.assumption_infers,
                        &complete_assumption_sources,
                        &visible_assumption_sources,
                        "ForallProof assumption inference",
                    )?;
                self.compile_typed_inference_results_as_local_have_statements(
                    &visible_assumption_infers,
                    &visible_assumption_sources,
                    &mut proof_lines,
                    "ForallProof assumption inference",
                )?;
                let mut direct_single_heterogeneous_subset_proof = None;
                let selected_conclusion_indices = publication_selection
                    .source_conclusion_indices
                    .iter()
                    .copied()
                    .collect::<HashSet<_>>();
                let last_selected_conclusion_index = publication_selection
                    .source_conclusion_indices
                    .iter()
                    .copied()
                    .max()
                    .ok_or_else(|| "ForallProof publication retained no conclusion".to_string())?;
                // Runtime verifies source conclusions in order, so a later
                // conclusion may cite the exact FactId of an earlier one. A
                // projected stored forall still has to replay those preceding
                // child Results locally even when only the later conclusion is
                // published by the outer theorem.
                for source_conclusion_index in 0..=last_selected_conclusion_index {
                    let conclusion_is_published =
                        selected_conclusion_indices.contains(&source_conclusion_index);
                    let proved = &proof.proves[source_conclusion_index];
                    let expected = &source_forall.then_facts[source_conclusion_index];
                    let expected = expected.clone().to_fact();
                    if proved.stmt.clone().to_fact().to_string() != expected.to_string() {
                        return Err(format!(
                        "ForallProof conclusion {source_conclusion_index} changed its retained statement"
                    ));
                    }
                    let child = proved.result.factual_success().ok_or_else(|| {
                        format!("ForallProof conclusion {source_conclusion_index} is not factual")
                    })?;
                    if child.fact().to_string() != expected.to_string()
                        || child.store.fact.to_string() != expected.to_string()
                    {
                        return Err(format!(
                            "ForallProof conclusion {source_conclusion_index} changed its target"
                        ));
                    }
                    if child
                        .store
                        .infers
                        .rule_applications
                        .iter()
                        .any(|application| {
                            !infer_rule_has_direct_compiler_environment_consumer(&application.rule)
                        })
                    {
                        return Err(format!(
                            "ForallProof conclusion {source_conclusion_index} contains a typed inference rule that the binder compiler does not support"
                        ));
                    }
                    let conclusion_fact_id = child.store.fact_id.ok_or_else(|| {
                        format!(
                            "ForallProof conclusion {source_conclusion_index} has no frozen FactId"
                        )
                    })?;
                    // The conclusion is a real child Result layer. Its proof may
                    // render objects (notably function applications) whose exact
                    // verifier-selected contracts live in the corresponding
                    // named WD child. The complete parent-owned WD tree is active
                    // for this binder frame; install only this child's intrinsic
                    // stores before constructing the child proof.
                    let conclusion_well_definedness =
                        &well_definedness.conclusions[source_conclusion_index];
                    install_fact_well_definedness_proof_store_results_in_active_environment(
                    conclusion_well_definedness.well_definedness.as_ref(),
                    &mut self.environment_stack,
                )
                .map_err(|error| {
                    let preceding_fact_ids = proof
                        .proves
                        .iter()
                        .take(source_conclusion_index)
                        .filter_map(|proved| proved.result.factual_success())
                        .filter_map(|proved| proved.store.fact_id)
                        .map(|fact_id| fact_id.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!(
                        "ForallProof conclusion {source_conclusion_index} WD stores failed to install after preceding FactIds [{preceding_fact_ids}]: {error}"
                    )
                })?;
                    self.install_fact_anonymous_function_occurrence_aliases(
                        &expected,
                        &format!("ForallProof conclusion {source_conclusion_index}"),
                    )?;
                    self.install_fact_anonymous_function_occurrence_aliases(
                        &child.fact(),
                        &format!(
                            "ForallProof conclusion {source_conclusion_index} retained proof target"
                        ),
                    )?;
                    let Some(conclusion_proof) = self
                    .construct_lean_proof_from_direct_fact_result(child)
                    .map_err(|error| {
                        format!("ForallProof conclusion {source_conclusion_index} proof failed: {error}")
                    })?
                else {
                        return Err(format!(
                            "ForallProof conclusion {source_conclusion_index} proof constructor does not yet consume its Result shape: {:?}",
                            child.proof()
                        ));
                };
                    if conclusion_is_published
                        && publication_selection.published_conclusions.len() == 1
                        && publication_selection.published_conclusions[0].1
                            == conclusion_fact_id
                        && matches!(
                            &expected,
                            Fact::AtomicFact(
                                AtomicFact::SubsetFact(_) | AtomicFact::SupersetFact(_)
                            )
                        )
                    {
                        // `Litex.Subset` is heterogeneous. Keeping the proof
                        // directly under the enclosing theorem goal prevents a
                        // standalone local `have` from prematurely choosing its
                        // implicit carrier (notably for `empty subset A`).
                        direct_single_heterogeneous_subset_proof = Some(conclusion_proof);
                        continue;
                    }
                    let proposition = render_fact(&expected, &self.environment_stack)?;
                    let conclusion_name = format!(
                        "__prior{}_{}",
                        self.next_fact_name_index, source_conclusion_index
                    );
                    proof_lines.push(format!(
                        "have {conclusion_name} : {proposition} := {conclusion_proof}"
                    ));
                    self.environment_stack
                        .fact_names
                        .insert(conclusion_fact_id, conclusion_name.clone());
                    self.environment_stack
                        .fact_propositions
                        .insert(conclusion_fact_id, expected.clone());
                    // WD verifies and stores each conclusion before the proof
                    // phase verifies and stores it again. Both identities are
                    // frozen in the recursive Result, and a later conclusion's
                    // WD proof may cite the earlier WD-stage identity exactly.
                    // They denote the same proposition and are discharged by
                    // the same local Lean `have`, so retain both exact IDs
                    // instead of falling back to proposition lookup.
                    let well_definedness_conclusion_fact_id = conclusion_well_definedness
                        .store
                        .fact_id
                        .ok_or_else(|| {
                            format!(
                                "ForallProof WD conclusion {source_conclusion_index} has no frozen FactId"
                            )
                        })?;
                    self.environment_stack
                        .fact_names
                        .insert(well_definedness_conclusion_fact_id, conclusion_name.clone());
                    self.environment_stack
                        .fact_propositions
                        .insert(well_definedness_conclusion_fact_id, expected.clone());
                    if !conclusion_well_definedness.store.infers.is_empty() {
                        if conclusion_well_definedness
                            .store
                            .infers
                            .rule_applications
                            .iter()
                            .any(|application| {
                                !infer_rule_has_direct_compiler_environment_consumer(
                                    &application.rule,
                                )
                            })
                        {
                            return Err(format!(
                                "ForallProof WD conclusion {source_conclusion_index} contains an inference rule without a direct compiler consumer"
                            ));
                        }
                        let layer = format!(
                            "ForallProof WD conclusion {source_conclusion_index} inference"
                        );
                        let mut allowed_sources = self
                            .install_equality_chain_adjacent_projections_for_typed_inference(
                                &expected,
                                well_definedness_conclusion_fact_id,
                                &conclusion_name,
                                &conclusion_well_definedness.store.infers,
                                &layer,
                            )?;
                        for source in self
                            .install_numeric_order_chain_adjacent_projections_for_typed_inference(
                                &expected,
                                well_definedness_conclusion_fact_id,
                                &conclusion_name,
                                &conclusion_well_definedness.store.infers,
                                &layer,
                            )?
                        {
                            if !allowed_sources.iter().any(|existing| {
                                existing.0 == source.0
                                    && existing.1.to_string() == source.1.to_string()
                            }) {
                                allowed_sources.push(source);
                            }
                        }
                        self.compile_typed_inference_results_as_local_have_statements(
                            &conclusion_well_definedness.store.infers,
                            &allowed_sources,
                            &mut proof_lines,
                            &layer,
                        )?;
                    }
                    let child_inference_layer =
                        format!("ForallProof conclusion {source_conclusion_index} inference");
                    let mut child_allowed_sources = self
                        .install_equality_chain_adjacent_projections_for_typed_inference(
                            &expected,
                            conclusion_fact_id,
                            &conclusion_name,
                            &child.store.infers,
                            &child_inference_layer,
                        )?;
                    for source in self
                        .install_numeric_order_chain_adjacent_projections_for_typed_inference(
                            &expected,
                            conclusion_fact_id,
                            &conclusion_name,
                            &child.store.infers,
                            &child_inference_layer,
                        )?
                    {
                        if !child_allowed_sources.iter().any(|existing| {
                            existing.0 == source.0
                                && existing.1.to_string() == source.1.to_string()
                        }) {
                            child_allowed_sources.push(source);
                        }
                    }
                    self.compile_typed_inference_results_as_local_have_statements(
                        &child.store.infers,
                        &child_allowed_sources,
                        &mut proof_lines,
                        &child_inference_layer,
                    )?;
                }
                let mut conclusion_names =
                    Vec::with_capacity(publication_selection.published_conclusions.len());
                let mut conclusions =
                    Vec::with_capacity(publication_selection.published_conclusions.len());
                for (_, fact_id, fact) in &publication_selection.published_conclusions {
                    let Some(name) = self.environment_stack.fact_names.get(fact_id) else {
                        if direct_single_heterogeneous_subset_proof.is_some()
                            && publication_selection.published_conclusions.len() == 1
                        {
                            conclusions.push((*fact_id, fact.clone()));
                            continue;
                        }
                        return Err(format!(
                            "ForallProof published conclusion FactId `{fact_id}` was not replayed"
                        ));
                    };
                    let retained = self
                        .environment_stack
                        .fact_propositions
                        .get(fact_id)
                        .ok_or_else(|| {
                            format!(
                                "ForallProof published conclusion FactId `{fact_id}` lost its proposition"
                            )
                        })?;
                    if retained.to_string() != fact.to_string() {
                        return Err(format!(
                            "ForallProof published conclusion FactId `{fact_id}` changed its proposition"
                        ));
                    }
                    conclusion_names.push(name.clone());
                    conclusions.push((*fact_id, fact.clone()));
                }
                if let Some(direct) = direct_single_heterogeneous_subset_proof {
                    proof_lines.push(format!("exact {direct}"));
                } else if conclusion_names.len() == 1 {
                    proof_lines.push(format!("exact {}", conclusion_names[0]));
                } else {
                    proof_lines.push(format!("exact ⟨{}⟩", conclusion_names.join(", ")));
                }
                let projected_fact: Fact = publication_selection.forall_fact.clone().into();
                let proposition =
                    render_fact(&projected_fact, &self.environment_stack).map_err(|error| {
                        format!("ForallProof target failed to render in its binder: {error}")
                    })?;
                let mut lines = vec!["by".to_string()];
                if !intro_names.is_empty() {
                    lines.push(format!("  intro {}", intro_names.join(" ")));
                }
                lines.extend(proof_lines.into_iter().map(|line| indent_lines(&line, 2)));
                Ok(Some(CompiledDirectForallProofBody {
                    proposition,
                    proof_expression: lines.join("\n"),
                    parameter_premises,
                    premises,
                    conclusions,
                }))
            })(
            );
            self.environment_stack.pop_local_environment();
            let Some(compiled) = compilation? else {
                return Ok(false);
            };

            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {theorem_name} :\n    {} := {}",
                compiled.proposition, compiled.proof_expression
            ));
            if let Some(stored_fact_id) = publication_selection.stored_fact_id {
                let published_fact: Fact = publication_selection.forall_fact.clone().into();
                self.environment_stack
                    .fact_names
                    .insert(stored_fact_id, theorem_name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(stored_fact_id, published_fact);
            }
            self.next_fact_name_index += 1;
            for (conclusion_index, (fact_id, fact)) in compiled.conclusions.iter().enumerate() {
                self.environment_stack
                    .fact_propositions
                    .insert(*fact_id, fact.clone());
                self.environment_stack.forall_conclusion_bindings.insert(
                    *fact_id,
                    ForallConclusionBinding {
                        theorem_name: theorem_name.clone(),
                        forall: publication_selection.forall_fact.clone(),
                        parameter_premises: compiled.parameter_premises.clone(),
                        premises: compiled.premises.clone(),
                        conclusion_index,
                        conclusion_count: compiled.conclusions.len(),
                    },
                );
            }
        }
        Ok(true)
    }

    pub(super) fn direct_forall_result_is_not_yet_supported(
        &self,
        reason: &str,
    ) -> Result<bool, String> {
        Err(format!(
            "direct ForallProof compiler rejected this Result because {reason}"
        ))
    }

    /// `Combine`: publish a directly constructed standard numeric membership
    /// proof, then consume its typed sign/nonzero inference Results. Closed
    /// evaluation has a stricter dedicated path above; this route covers
    /// symbolic closure and primitive constant rules.
    pub(super) fn compile_direct_standard_numeric_membership_with_inference(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let source_fact = result.fact();
        let Ok((_, set)) = membership_parts(&source_fact) else {
            return Ok(false);
        };
        if !matches!(set, Obj::StandardSet(_)) || result.store.infers.rule_applications.is_empty() {
            return Ok(false);
        }
        let Some(proof) = self.construct_lean_proof_from_direct_fact_result(result)? else {
            return Ok(false);
        };
        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "stored standard numeric membership has no FactId".to_string())?;
        let proposition = render_fact(&source_fact, &self.environment_stack)?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {proposition} := by\n  exact {proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact.clone());
        self.next_fact_name_index += 1;
        self.compile_standard_numeric_membership_infer_result_as_top_level_declarations(
            &source_fact,
            source_fact_id,
            &result.store.infers,
            "standard numeric membership inference",
        )?;
        Ok(true)
    }

    /// `Combine`: publish membership in one literal set builder, then publish
    /// the exact base-membership and predicate projections named by its typed
    /// infer Results. Every projection cites the source statement's FactId;
    /// the compiler never rediscovers these consequences from proposition
    /// shape or a store-reason string.
    pub(super) fn compile_direct_set_builder_membership_with_inference(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let source_fact = result.fact();
        let Ok((_, source_set)) = membership_parts(&source_fact) else {
            return Ok(false);
        };
        let Obj::SetBuilder(_) = source_set else {
            return Ok(false);
        };
        if result.store.infers.rule_applications.is_empty() {
            return Ok(false);
        }
        let Some(source_proof) = self.construct_lean_proof_from_direct_fact_result(result)? else {
            return Ok(false);
        };
        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "stored set-builder membership has no FactId".to_string())?;
        let source_proposition = render_fact(&source_fact, &self.environment_stack)?;
        let source_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {source_name} : {source_proposition} := by\n  exact {source_proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, source_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact.clone());
        self.next_fact_name_index += 1;

        self.compile_set_builder_membership_infer_result_as_top_level_declarations(
            &source_fact,
            source_fact_id,
            &source_name,
            &result.store.infers,
        )?;
        Ok(true)
    }

    pub(super) fn compile_set_builder_membership_infer_result_as_top_level_declarations(
        &mut self,
        source_fact: &Fact,
        source_fact_id: FactId,
        source_name: &str,
        infers: &SuccessInferResult,
    ) -> Result<(), String> {
        let (source_element, source_set) = membership_parts(source_fact)?;
        let Obj::SetBuilder(builder) = source_set else {
            return Err("set-builder inference source retained a non-builder set".into());
        };
        resolve_fact_citation(&source_fact_id, source_fact, &self.environment_stack)?;
        let expected_application_count = builder.facts.len() + 1;
        if infers.rule_applications.len() != expected_application_count {
            return Err(format!(
                "set-builder membership retained {} typed projections instead of {expected_application_count}",
                infers.rule_applications.len()
            ));
        }
        for (application_index, application) in infers.rule_applications.iter().enumerate() {
            let [premise] = application.premises.as_slice() else {
                return Err(format!(
                    "set-builder projection {application_index} must cite one source premise"
                ));
            };
            if premise.fact_id != Some(source_fact_id)
                || premise.fact.to_string() != source_fact.to_string()
            {
                return Err(format!(
                    "set-builder projection {application_index} does not cite the exact source FactId"
                ));
            }
            let [conclusion] = application.conclusions.as_slice() else {
                return Err(format!(
                    "set-builder projection {application_index} must retain one conclusion"
                ));
            };
            let conclusion_fact_id = conclusion.fact_id.ok_or_else(|| {
                format!("set-builder projection {application_index} has no conclusion FactId")
            })?;
            if conclusion_fact_id == source_fact_id
                || !infer_result_retains_fact_id(infers, &conclusion.fact, conclusion_fact_id)
            {
                return Err(format!(
                    "set-builder projection {application_index} disagrees with its ordered store effect"
                ));
            }

            let proof = match &application.rule {
                InferRule::SetBuilderBaseMembershipProjection if application_index == 0 => {
                    let (element, set) = membership_parts(&conclusion.fact)?;
                    if obj_equality_key(element) != obj_equality_key(source_element)
                        || obj_equality_key(set) != obj_equality_key(builder.param_set.as_ref())
                    {
                        return Err(
                            "set-builder base projection changed its element or base set".into(),
                        );
                    }
                    format!("Litex.Rules.inBaseOfInSetBuilder ({source_name})")
                }
                InferRule::SetBuilderPredicateProjection { clause_index }
                    if application_index == *clause_index + 1
                        && *clause_index < builder.facts.len() =>
                {
                    render_set_builder_predicate_projection_from_fact_and_proof(
                        &conclusion.fact,
                        *clause_index,
                        &source_fact,
                        &source_name,
                        &self.environment_stack,
                    )?
                }
                _ => {
                    return Err(format!(
                        "set-builder projection {application_index} changed its typed rule or clause order"
                    ));
                }
            };
            let proposition = render_fact(&conclusion.fact, &self.environment_stack)?;
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {theorem_name} : {proposition} := by\n  exact {proof}"
            ));
            self.environment_stack
                .fact_names
                .insert(conclusion_fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(conclusion_fact_id, conclusion.fact.clone());
            self.next_fact_name_index += 1;
        }
        Ok(())
    }

    /// `Combine`: publish the selected list-set membership proof and then
    /// publish the exact ordered equality alternatives returned by inference.
    /// Both layers cite frozen FactIds; the compiler never reconstructs this
    /// rule from a store-reason string.
    pub(super) fn compile_direct_list_set_membership_with_inference(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let source_fact = result.fact();
        let Ok((_, source_set)) = membership_parts(&source_fact) else {
            return Ok(false);
        };
        let Obj::ListSet(list_set) = source_set else {
            return Ok(false);
        };
        let matching_applications = result
            .store
            .infers
            .rule_applications
            .iter()
            .filter(|application| {
                matches!(
                    application.rule,
                    InferRule::ListSetMembershipImpliesEqualityAlternatives(_)
                )
            })
            .collect::<Vec<_>>();
        if matching_applications.is_empty() {
            return Ok(false);
        }
        let [application] = matching_applications.as_slice() else {
            return Err("list-set membership retained more than one alternatives inference".into());
        };
        if result.store.infers.rule_applications.len() != 1 {
            return Err("list-set membership retained unrelated top-level inference rules".into());
        }
        let InferRule::ListSetMembershipImpliesEqualityAlternatives(rule) = &application.rule
        else {
            unreachable!("matching list-set inference filtered above")
        };
        if rule.element_count == 0 || rule.element_count != list_set.list.len() {
            return Err("list-set alternatives rule changed its nonempty source arity".into());
        }
        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "stored list-set membership has no FactId".to_string())?;
        let [premise] = application.premises.as_slice() else {
            return Err("list-set alternatives inference must cite one membership premise".into());
        };
        if premise.fact_id != Some(source_fact_id)
            || premise.fact.to_string() != source_fact.to_string()
        {
            return Err("list-set alternatives inference changed its source FactId".into());
        }
        let [conclusion] = application.conclusions.as_slice() else {
            return Err("list-set alternatives inference must retain one conclusion".into());
        };
        let conclusion_fact_id = conclusion
            .fact_id
            .ok_or_else(|| "list-set alternatives conclusion has no FactId".to_string())?;
        if !infer_result_retains_fact_id(&result.store.infers, &conclusion.fact, conclusion_fact_id)
        {
            return Err(
                "list-set alternatives conclusion disagrees with its flattened store effect".into(),
            );
        }
        if !conclusion.infers.rule_applications.is_empty()
            || conclusion.infers.store_fact_outputs.iter().any(|output| {
                output.fact_id != Some(conclusion_fact_id)
                    || output.itself_and_why_itself_is_stored.0.to_string()
                        != conclusion.fact.to_string()
                    || !output.inferred_facts.is_empty()
                    || !output.inferred_fact_ids.is_empty()
            })
        {
            return Err(
                "list-set alternatives conclusion retained unsupported recursive effects".into(),
            );
        }

        let Some(source_proof) = self.construct_lean_proof_from_direct_fact_result(result)? else {
            return Ok(false);
        };
        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        let source_proposition = render_fact(&source_fact, &self.environment_stack)?;
        let source_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {source_name} : {source_proposition} := by\n  exact {source_proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, source_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact.clone());
        self.next_fact_name_index += 1;

        let conclusion_proof = render_list_set_membership_elimination_from_fact_and_proof(
            &conclusion.fact,
            &source_fact,
            &source_name,
            &self.environment_stack,
        )?;
        let conclusion_proposition = render_fact(&conclusion.fact, &self.environment_stack)?;
        let conclusion_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {conclusion_name} : {conclusion_proposition} := by\n  exact {conclusion_proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(conclusion_fact_id, conclusion_name);
        self.environment_stack
            .fact_propositions
            .insert(conclusion_fact_id, conclusion.fact.clone());
        self.next_fact_name_index += 1;
        validate_flattened_inferred_fact_ids_are_visible(
            &result.store.infers,
            &self.environment_stack,
            "list-set membership inference",
        )?;
        Ok(true)
    }

    /// Some object-WD constructors intentionally store a fact for later
    /// statements. Function application is the important example: checking
    /// `f(x)` stores `f(x) $in ReturnSet` under a real FactId. These are not
    /// display-only WD details, so the compiler installs their proof bindings
    /// before compiling the enclosing fact proof.
    pub(super) fn install_atomic_fact_well_definedness_store_results(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<(), String> {
        self.install_fact_well_definedness_store_results(&result.well_definedness, &result.fact())
    }

    /// Install the observable stores owned by one exact fact-WD child layer.
    /// Nested verifier Results (for example a forall conclusion) may own their
    /// WD result in the parent's named `conclusions` field while their factual
    /// execution Result intentionally carries no duplicate certificate.
    pub(super) fn install_fact_well_definedness_store_results(
        &mut self,
        well_definedness: &SuccessVerifyFactWellDefinedResult,
        _source_fact: &Fact,
    ) -> Result<(), String> {
        let Some(recursive) = well_definedness.recursive.as_deref() else {
            return Ok(());
        };
        if !fact_well_definedness_result_contains_outer_intrinsic_store(recursive) {
            return Ok(());
        }
        let certificate =
            self.construct_well_definedness_to_lean_compilation_context(well_definedness)?;
        let previous_well_definedness =
            self.environment_stack.well_definedness.replace(certificate);
        let installation = install_fact_well_definedness_proof_store_results_in_active_environment(
            recursive,
            &mut self.environment_stack,
        );
        self.environment_stack.well_definedness = previous_well_definedness;
        installation
    }

    pub(super) fn compile_object_reflexivity_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::BuiltinRule(builtin) = result.proof() else {
            return Ok(false);
        };
        let Some(BuiltinRuleEvidence::ObjectReflexivity(evidence)) = builtin.evidence.typed()
        else {
            return Ok(false);
        };
        if !builtin.subgoals.is_empty() {
            return Err("object reflexivity gained unexpected proof children".into());
        }
        let source_fact = result.fact();
        if evidence.expected_target.to_string() != source_fact.to_string() {
            return Err("object-reflexivity evidence changed its target".into());
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
            return Err("object-reflexivity evidence targets a non-equality fact".into());
        };
        if obj_equality_key(&equality.left) != obj_equality_key(&equality.right) {
            return Err("object-reflexivity evidence changed its equality endpoints".into());
        }
        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        let proof = format!(
            "Litex.Same.refl {}",
            self.render_object_using_well_definedness_from_fact_result(result, &equality.left)?
        );
        if !fact_result_contains_inferred_facts(result) {
            self.compile_stored_fact_without_inference(result, proof)?;
            return Ok(true);
        }

        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "object-reflexivity source has no FactId".to_string())?;
        let source_output = result
            .store
            .infers
            .store_fact_outputs
            .iter()
            .find(|output| {
                output.fact_id == Some(source_fact_id)
                    && output.itself_and_why_itself_is_stored.0.to_string()
                        == source_fact.to_string()
            })
            .ok_or_else(|| {
                "object-reflexivity typed inference lost its source store output".to_string()
            })?;
        if source_output.inferred_facts.len() != source_output.inferred_fact_ids.len() {
            return Err("object-reflexivity source store changed its inferred FactId arity".into());
        }
        let proposition = render_fact(&source_fact, &self.environment_stack)?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {proposition} := by\n  exact {proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact.clone());
        self.next_fact_name_index += 1;
        self.compile_tuple_equality_shape_infer_result(
            &source_fact,
            source_fact_id,
            &result.store.infers,
        )?;
        Ok(true)
    }

    pub(super) fn compile_rational_normalization_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::BuiltinRule(builtin) = result.proof() else {
            return Ok(false);
        };
        let Some(BuiltinRuleEvidence::RationalNormalization(evidence)) = builtin.evidence.typed()
        else {
            return Ok(false);
        };
        if fact_result_contains_inferred_facts(result) {
            return Ok(false);
        }
        if !builtin.subgoals.is_empty() {
            return Err("rational normalization gained unexpected proof children".into());
        }
        let source_fact = result.fact();
        if evidence.expected_target.to_string() != source_fact.to_string() {
            return Err("rational-normalization evidence changed its target".into());
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
            return Err("rational-normalization evidence targets a non-equality fact".into());
        };
        if obj_equality_key(&equality.left)
            != obj_equality_key(&evidence.left_evaluation.expression)
            || obj_equality_key(&equality.right)
                != obj_equality_key(&evidence.right_evaluation.expression)
        {
            return Err("rational-normalization evidence changed an equality endpoint".into());
        }
        validate_success_evaluate_obj_result(&evidence.left_evaluation)?;
        validate_success_evaluate_obj_result(&evidence.right_evaluation)?;
        if evidence.left_evaluation.value.normalized_value
            != evidence.right_evaluation.value.normalized_value
        {
            return Err("rational-normalization evidence retained unequal normal forms".into());
        }
        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        self.render_object_using_well_definedness_from_fact_result(result, &equality.left)?;
        self.render_object_using_well_definedness_from_fact_result(result, &equality.right)?;
        self.compile_stored_fact_without_inference(
            result,
            "Litex.Same.ofEq (by norm_num [Litex.abs, Litex.min, Litex.max, Litex.tupleDim, Litex.TupleShape.dimension])"
                .to_string(),
        )?;
        Ok(true)
    }

    pub(super) fn compile_complex_algebraic_normalization_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::BuiltinRule(builtin) = result.proof() else {
            return Ok(false);
        };
        let Some(BuiltinRuleEvidence::ComplexAlgebraicNormalization(evidence)) =
            builtin.evidence.typed()
        else {
            return Ok(false);
        };
        if fact_result_contains_inferred_facts(result) {
            return Ok(false);
        }
        let source_fact = result.fact();
        let Some(proof) = self.construct_lean_complex_algebraic_normalization_from_result(
            &source_fact,
            evidence,
            &builtin.subgoals,
        )?
        else {
            return Ok(false);
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
            unreachable!();
        };
        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        self.render_object_using_well_definedness_from_fact_result(result, &equality.left)?;
        self.render_object_using_well_definedness_from_fact_result(result, &equality.right)?;
        self.compile_stored_fact_without_inference(result, proof)?;
        Ok(true)
    }

    pub(super) fn compile_rational_algebraic_normalization_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::BuiltinRule(builtin) = result.proof() else {
            return Ok(false);
        };
        let Some(BuiltinRuleEvidence::RationalAlgebraicNormalization(evidence)) =
            builtin.evidence.typed()
        else {
            return Ok(false);
        };
        if fact_result_contains_inferred_facts(result) {
            return Ok(false);
        }
        let source_fact = result.fact();
        let Some(proof) = self.construct_lean_rational_algebraic_normalization_from_result(
            &source_fact,
            evidence,
            &builtin.subgoals,
        )?
        else {
            return Ok(false);
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
            unreachable!();
        };
        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        self.render_object_using_well_definedness_from_fact_result(result, &equality.left)?;
        self.render_object_using_well_definedness_from_fact_result(result, &equality.right)?;
        self.compile_stored_fact_without_inference(result, proof)?;
        Ok(true)
    }

    /// Compile the exact nonzero child Results retained by complex calculate,
    /// bridge each semantic `!= 0` proof to native Complex nonzero, and feed
    /// only those named proofs to the fixed field/ring adapter.
    pub(super) fn construct_lean_complex_algebraic_normalization_from_result(
        &mut self,
        target: &Fact,
        evidence: &ComplexAlgebraicNormalizationBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        validate_complex_algebraic_normalization_builtin_rule_evidence(target, evidence)?;
        self.construct_lean_algebraic_normalization_from_result(
            target,
            &evidence.expected_nonzero_premises,
            subgoals,
        )
    }

    pub(super) fn construct_lean_rational_algebraic_normalization_from_result(
        &mut self,
        target: &Fact,
        evidence: &RationalAlgebraicNormalizationBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        validate_rational_algebraic_normalization_builtin_rule_evidence(target, evidence)?;
        self.construct_lean_algebraic_normalization_from_result(
            target,
            &evidence.expected_nonzero_premises,
            subgoals,
        )
    }

    fn construct_lean_algebraic_normalization_from_result(
        &mut self,
        target: &Fact,
        expected_nonzero_premises: &[Fact],
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let native = self.construct_lean_native_algebraic_normalization_from_result(
            target,
            expected_nonzero_premises,
            subgoals,
        )?;
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = target else {
            unreachable!("algebraic normalization validator requires equality")
        };
        let source_to_numeric = |object: &Obj| -> Result<(String, String, String), String> {
            let source = render_obj(object, &self.environment_stack)?;
            let numeric = render_numeric_obj(object, &self.environment_stack)?;
            if source == numeric {
                return Ok((
                    source.clone(),
                    numeric,
                    format!("Litex.Same.refl ({source})"),
                ));
            }
            let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
                LeanTargetObjectRepresentation::lower(object)?
            else {
                return Err(format!(
                    "algebraic normalization changed non-symbol endpoint `{source}` to `{numeric}` without a structural Same bridge"
                ));
            };
            let bridge = self
                .environment_stack
                .numeric_representation_equalities
                .get(&symbol_id)
                .cloned()
                .ok_or_else(|| {
                    format!(
                        "algebraic normalization endpoint `{source}` has no exact numeric Same bridge"
                    )
                })?;
            Ok((source, numeric, bridge))
        };
        let (_source_left, numeric_left, left_bridge) =
            source_to_numeric(&equality.left)?;
        let (_source_right, numeric_right, right_bridge) =
            source_to_numeric(&equality.right)?;
        let native = format!(
            "(show {numeric_left} = {numeric_right} from {native})"
        );
        Ok(Some(format!(
            "Litex.Same.trans ({left_bridge}) (Litex.Same.trans (Litex.Same.ofEq ({native})) (Litex.Same.symm ({right_bridge})))"
        )))
    }

    pub(super) fn construct_lean_native_algebraic_normalization_from_result(
        &mut self,
        target: &Fact,
        expected_nonzero_premises: &[Fact],
        subgoals: &[StmtResult],
    ) -> Result<String, String> {
        let Fact::AtomicFact(AtomicFact::EqualFact(_)) = target else {
            unreachable!("complex normalization validator requires an equality")
        };
        if subgoals.len() != expected_nonzero_premises.len() {
            return Err(
                "complex-algebraic-normalization proof lost an ordered nonzero child Result".into(),
            );
        }

        let mut declarations = Vec::with_capacity(subgoals.len());
        let mut native_nonzero_names = Vec::with_capacity(subgoals.len());
        for (index, (expected, subgoal)) in expected_nonzero_premises
            .iter()
            .zip(subgoals.iter())
            .enumerate()
        {
            let subgoal = subgoal
                .factual_success()
                .ok_or_else(|| format!("complex nonzero child {index} is not a factual Result"))?;
            if subgoal.fact().to_string() != expected.to_string()
                || subgoal.store.fact.to_string() != expected.to_string()
            {
                return Err(format!(
                    "complex nonzero child {index} changed its exact premise"
                ));
            }
            let Fact::AtomicFact(AtomicFact::NotEqualFact(nonzero)) = expected else {
                return Err(format!(
                    "complex nonzero premise {index} is not a disequality"
                ));
            };
            if !matches!(
                &nonzero.right,
                Obj::Number(number) if number.normalized_value == "0"
            ) {
                return Err(format!(
                    "complex nonzero premise {index} changed its zero endpoint"
                ));
            }
            let left = render_numeric_obj(&nonzero.left, &self.environment_stack)?;
            let right = render_numeric_obj(&nonzero.right, &self.environment_stack)?;
            let name = format!("__calculate_nonzero{}", index + 1);
            let native_proof = match self.construct_lean_proof_from_direct_fact_result(subgoal) {
                Ok(Some(semantic_proof)) => format!(
                    "by\n    intro __native_eq\n    exact ({semantic_proof}) (Litex.Same.ofEq __native_eq)"
                ),
                Ok(None) => {
                    // A few closed native constants still have legacy
                    // label-only nonzero Results. The target is independently
                    // checked here by Lean; symbolic premises never use this
                    // fallback because `norm_num` cannot manufacture them.
                    "by\n    norm_num [Complex.I_mul_I]".to_string()
                }
                Err(_error)
                    if fact_proof_is_not_equal_from_strict_order(subgoal.proof()) =>
                {
                    self.construct_native_nonzero_from_strict_order_result(
                        subgoal,
                        &nonzero.left,
                    )?
                }
                Err(error) => return Err(error),
            };
            declarations.push(format!(
                "  have {name} : {left} ≠ {right} := {native_proof}"
            ));
            native_nonzero_names.push(name);
        }

        let mut proof = "by\n".to_string();
        if !declarations.is_empty() {
            proof.push_str(&declarations.join("\n"));
            proof.push('\n');
        }
        if native_nonzero_names.is_empty() {
            proof.push_str("  ring_nf <;> norm_num [Complex.I_mul_I] <;> ring");
        } else {
            proof.push_str(&format!(
                "  field_simp [{}] <;> ring_nf <;> norm_num [Complex.I_mul_I] <;> ring",
                native_nonzero_names.join(", ")
            ));
        }
        Ok(format!("({proof})"))
    }

    fn construct_native_nonzero_from_strict_order_result(
        &mut self,
        result: &SuccessFactStmtResult,
        expected_object: &Obj,
    ) -> Result<String, String> {
        let mut proof = result.proof();
        while let SuccessFactProofResult::Reuse(reuse) = proof {
            proof = reuse.source.proof();
        }
        let SuccessFactProofResult::BuiltinRule(builtin) = proof else {
            return Err("strict-order nonzero Result changed its proof kind".into());
        };
        if !matches!(
            builtin.evidence.typed(),
            Some(BuiltinRuleEvidence::NotEqualFromStrictOrder)
        ) {
            return Err("native nonzero extraction requires strict-order evidence".into());
        }
        let mut selected = None;
        for child in &builtin.subgoals {
            let Some(child) = child.factual_success() else {
                return Err("strict-order nonzero evidence retained a non-factual child".into());
            };
            if let Ok((left, right, true)) = order_relation_parts(&child.fact()) {
                let endpoints_match = (is_literal_zero(left)
                    && obj_equality_key(right) == obj_equality_key(expected_object))
                    || (obj_equality_key(left) == obj_equality_key(expected_object)
                        && is_literal_zero(right));
                if endpoints_match {
                    if selected.is_some() {
                        return Err(
                            "strict-order nonzero evidence retained multiple matching orders"
                                .into(),
                        );
                    }
                    selected = Some(child);
                    continue;
                }
            }
            let child_fact = child.fact();
            let Ok((_, set)) = membership_parts(&child_fact) else {
                return Err(
                    "strict-order nonzero evidence retained an unrelated child fact".into(),
                );
            };
            if !matches!(set, Obj::StandardSet(StandardSet::R)) {
                return Err(
                    "strict-order nonzero evidence changed its real-carrier premise".into(),
                );
            }
        }
        let selected = selected
            .ok_or_else(|| "strict-order nonzero evidence lost its strict-order child".to_string())?;
        // Consume the retained strict-order child as authority for this
        // nonzero obligation, but prove the exact target term in Lean's
        // native real representation. This avoids treating Litex's
        // representative-owning `Positive` wrapper as definitionally equal
        // to a `Litex.Lt` proposition.
        self.construct_lean_proof_from_direct_fact_result(selected)?
            .ok_or_else(|| {
                "strict-order nonzero child has no direct Lean proof constructor".to_string()
            })?;
        let native_real = render_real_target_object_representation(
            &LeanTargetObjectRepresentation::lower(expected_object)?,
            &self.environment_stack,
        )?;
        Ok(format!(
            "by\n    intro __native_eq\n    have __native_re := congrArg Complex.re __native_eq\n    simp [Litex.abs, ← Complex.ofReal_add, ← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs] at __native_re\n    have __native_nonzero : ({native_real} : ℝ) ≠ 0 := by positivity\n    exact __native_nonzero __native_re"
        ))
    }

    pub(super) fn render_object_using_well_definedness_from_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
        object: &Obj,
    ) -> Result<String, String> {
        let certificate =
            self.construct_well_definedness_to_lean_compilation_context(&result.well_definedness)?;
        let previous_well_definedness =
            self.environment_stack.well_definedness.replace(certificate);
        let rendered = render_obj(object, &self.environment_stack);
        self.environment_stack.well_definedness = previous_well_definedness;
        rendered
    }

    pub(super) fn render_fact_using_well_definedness_result(
        &mut self,
        result: &SuccessVerifyFactWellDefinedResult,
        fact: &Fact,
    ) -> Result<String, String> {
        let certificate = self.construct_well_definedness_to_lean_compilation_context(result)?;
        let previous_well_definedness =
            self.environment_stack.well_definedness.replace(certificate);
        let rendered = render_fact(fact, &self.environment_stack);
        self.environment_stack.well_definedness = previous_well_definedness;
        rendered
    }

    pub(super) fn compile_stored_fact_without_inference(
        &mut self,
        result: &SuccessFactStmtResult,
        proof: String,
    ) -> Result<(), String> {
        let source_fact = result.fact();
        // Most facts render solely from the compiler environment. Function
        // applications are the remaining target-side exception: their exact
        // application term still reads the temporary WD rendering view. Only
        // construct that view if ordinary Result-driven rendering says it is
        // needed, then restore the surrounding compiler layer on every path.
        let proposition = match render_fact(&source_fact, &self.environment_stack) {
            Ok(proposition) => proposition,
            Err(initial_render_error) if matches!(source_fact, Fact::AtomicFact(_)) => {
                self.render_fact_using_well_definedness_result(
                    &result.well_definedness,
                    &source_fact,
                )
                .map_err(|wd_render_error| {
                    format!(
                        "{initial_render_error}; Result-owned WD rendering also failed: {wd_render_error}"
                    )
                })?
            }
            Err(error) => return Err(error),
        };
        self.compile_stored_fact_without_inference_with_pre_rendered_proposition(
            result,
            proof,
            proposition,
        )
    }

    /// Publish a fact whose proposition was rendered by the Result-owned
    /// child environment before that environment was popped. Forall/function
    /// telescopes need this path because re-rendering their type in the parent
    /// would discard exact local FactId bindings.
    pub(super) fn compile_stored_fact_without_inference_with_pre_rendered_proposition(
        &mut self,
        result: &SuccessFactStmtResult,
        proof: String,
        proposition: String,
    ) -> Result<(), String> {
        let source_fact = result.fact();
        if result.store.fact.to_string() != source_fact.to_string() {
            return Err("fact changed between verification and store".into());
        }
        let fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "stored fact has no FactId".to_string())?;
        if !result.store.infers.rule_applications.is_empty() {
            return Err("zero-inference fact retained unexpected typed infer rules".into());
        }
        match result.store.infers.store_fact_outputs.as_slice() {
            [store]
                if store.fact_id == Some(fact_id)
                    && store.itself_and_why_itself_is_stored.0.to_string()
                        == source_fact.to_string()
                    && store.inferred_facts.is_empty()
                    && store.inferred_fact_ids.is_empty() => {}
            [] if self
                .environment_stack
                .fact_propositions
                .get(&fact_id)
                .is_some_and(|stored| {
                    stored.to_string() == source_fact.to_string()
                        || equality_facts_are_equal_up_to_nested_binder_alpha(stored, &source_fact)
                }) => {}
            _ => {
                let installed = self
                    .environment_stack
                    .fact_propositions
                    .get(&fact_id)
                    .map(ToString::to_string);
                return Err(format!(
                    "zero-inference fact store output disagrees with the statement store: FactId `{fact_id}`, statement `{source_fact}`, store outputs {}, installed proposition {:?}",
                    result.store.infers.store_fact_outputs.len(),
                    installed,
                ));
            }
        }
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        let declaration = if matches!(source_fact, Fact::ForallFact(_)) {
            format!("theorem {theorem_name} :\n    {proposition} := {proof}")
        } else {
            format!("theorem {theorem_name} : {proposition} := by\n  exact {proof}")
        };
        self.declarations.push(declaration);
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, source_fact);
        self.next_fact_name_index += 1;
        Ok(())
    }

    pub(super) fn compile_exact_fact_citation_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::StoredFactCitation(citation) = result.proof() else {
            return Ok(false);
        };
        let source_fact_id = citation.source_fact_id;
        if fact_result_contains_inferred_facts(result) {
            return Ok(false);
        }
        let source_fact = result.fact();
        // FactId is the citation identity. `resolve_fact_citation` additionally
        // checks that the retained proposition is unchanged, including
        // alpha-equivalent forall binders, before exposing its Lean name.
        let proof = resolve_fact_citation(
            &source_fact_id,
            &citation.source_fact,
            &self.environment_stack,
        )?;
        if matches!(source_fact, Fact::AtomicFact(_)) {
            validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        }
        self.compile_stored_fact_without_inference(result, proof)?;
        Ok(true)
    }

    /// Direct `Leaf + Combine` compilation for a closed expression proved to
    /// belong to one standard numeric carrier. The recursive evaluation,
    /// source store identity, and every typed carrier inference are consumed
    /// from `SuccessFactStmtResult` without constructing backend fact IR.
    pub(super) fn compile_closed_standard_numeric_membership_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::BuiltinRule(builtin) = result.proof() else {
            return Ok(false);
        };
        let Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) = builtin.evidence.typed()
        else {
            return Ok(false);
        };
        if !builtin.subgoals.is_empty() {
            return Err("closed standard numeric membership gained proof subgoals".into());
        }

        let source_fact = result.fact();
        if result.store.fact.to_string() != source_fact.to_string()
            || evidence.expected_target.to_string() != source_fact.to_string()
        {
            return Err(
                "closed standard numeric membership changed between verification, proof, and store"
                    .into(),
            );
        }
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = &source_fact else {
            return Err(
                "closed standard numeric membership retained a non-membership target".into(),
            );
        };
        if !matches!(&membership.set, Obj::StandardSet(set) if *set == evidence.target_set)
            || obj_equality_key(&membership.element)
                != obj_equality_key(&evidence.evaluation.expression)
        {
            return Err(
                "closed standard numeric membership changed its expression or target carrier"
                    .into(),
            );
        }

        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        validate_success_evaluate_obj_result(&evidence.evaluation)?;

        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "stored closed numeric membership has no FactId".to_string())?;
        let proposition = render_fact(&source_fact, &self.environment_stack)?;
        let proof = render_closed_numeric_membership_from_result(
            &source_fact,
            evidence.target_set,
            &evidence.evaluation,
            &self.environment_stack,
        )?;
        let source_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {source_theorem_name} : {proposition} := by\n  exact {proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, source_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact.clone());
        self.next_fact_name_index += 1;

        self.compile_standard_numeric_membership_infer_result_as_top_level_declarations(
            &source_fact,
            source_fact_id,
            &result.store.infers,
            "closed standard numeric membership inference",
        )?;
        Ok(true)
    }

    pub(super) fn compile_natural_membership_infer_result(
        &mut self,
        source_fact: &Fact,
        source_fact_id: FactId,
        infers: &SuccessInferResult,
    ) -> Result<(), String> {
        let applications = infers
            .rule_applications
            .iter()
            .filter(|application| {
                application.rule == InferRule::NaturalMembershipImpliesNonnegative
                    && application.premises.len() == 1
                    && application.premises[0].fact_id == Some(source_fact_id)
                    && application.premises[0].fact.to_string() == source_fact.to_string()
            })
            .collect::<Vec<_>>();
        if applications.len() != 1 {
            return Err(format!(
                "natural membership expected one typed nonnegative inference for its exact FactId, retained {}",
                applications.len()
            ));
        }
        let application = applications[0];
        if application.conclusions.len() != 1 {
            return Err("natural-membership inference must retain one conclusion".into());
        }
        let conclusion = &application.conclusions[0];
        let conclusion_fact_id = conclusion
            .fact_id
            .ok_or_else(|| "natural-membership inference conclusion has no FactId".to_string())?;
        let conclusion_retains_its_store =
            conclusion.infers.store_fact_outputs.iter().any(|output| {
                output.fact_id == Some(conclusion_fact_id)
                    && output.itself_and_why_itself_is_stored.0.to_string()
                        == conclusion.fact.to_string()
            });
        if !conclusion_retains_its_store {
            return Err("natural-membership inference conclusion lost its store layer".into());
        }
        let output_retains_conclusion = infers.store_fact_outputs.iter().any(|output| {
            output
                .inferred_facts
                .iter()
                .zip(output.inferred_fact_ids.iter())
                .any(|(fact, fact_id)| {
                    fact.to_string() == conclusion.fact.to_string()
                        && *fact_id == Some(conclusion_fact_id)
                })
                || (output.itself_and_why_itself_is_stored.0.to_string()
                    == conclusion.fact.to_string()
                    && output.fact_id == Some(conclusion_fact_id))
        });
        if !output_retains_conclusion {
            return Err(
                "typed natural-membership inference and ordered store effects disagree".into(),
            );
        }

        let source_theorem_name = self
            .environment_stack
            .fact_names
            .get(&source_fact_id)
            .ok_or_else(|| "stored source FactId is unavailable to its inference".to_string())?
            .clone();
        let conclusion_proposition = render_fact(&conclusion.fact, &self.environment_stack)?;
        let conclusion_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {conclusion_theorem_name} : {conclusion_proposition} := by\n  exact Litex.Rules.nonnegativeOfInN ({source_theorem_name})"
        ));
        self.environment_stack
            .fact_names
            .insert(conclusion_fact_id, conclusion_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(conclusion_fact_id, conclusion.fact.clone());
        self.next_fact_name_index += 1;
        Ok(())
    }

    /// Publish typed standard-numeric inference children as top-level Lean
    /// theorems. The shared compiler first returns each conclusion as one
    /// structured local proof step; this wrapper renders earlier steps as the
    /// local closure of later proofs and publishes the current step under its
    /// exact retained FactId.
    pub(super) fn compile_standard_numeric_membership_infer_result_as_top_level_declarations(
        &mut self,
        source_fact: &Fact,
        source_fact_id: FactId,
        infers: &SuccessInferResult,
        result_layer: &str,
    ) -> Result<(), String> {
        self.compile_typed_infer_result_as_top_level_declarations_with_allowed_sources(
            infers,
            &[(source_fact_id, source_fact.clone())],
            result_layer,
        )
    }

    pub(super) fn compile_typed_infer_result_as_top_level_declarations_with_allowed_sources(
        &mut self,
        infers: &SuccessInferResult,
        allowed_sources: &[(FactId, Fact)],
        result_layer: &str,
    ) -> Result<(), String> {
        if infers.rule_applications.is_empty() {
            if infers.store_fact_outputs.iter().all(|output| {
                output.inferred_facts.is_empty() && output.inferred_fact_ids.is_empty()
            }) {
                return Ok(());
            }
            return Err(format!(
                "{result_layer} retained inferred store effects without typed rule applications"
            ));
        }

        let compiled_steps = self.compile_typed_inference_results_in_current_compiler_environment(
            infers,
            allowed_sources,
            CompiledInferenceFactAvailabilityInLeanEnvironment::LocalProofName,
            result_layer,
            None,
        )?;
        let mut preceding_steps: Vec<CompiledInferenceFactProofStep> = Vec::new();
        for step in compiled_steps {
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            let mut proof_lines = vec!["by".to_string()];
            proof_lines.extend(
                preceding_steps
                    .iter()
                    .map(CompiledInferenceFactProofStep::render_as_local_have_statement)
                    .map(|line| indent_lines(&line, 2)),
            );
            proof_lines.push(indent_lines(&format!("exact {}", step.proof_expression), 2));
            self.declarations.push(format!(
                "theorem {theorem_name} : {} := {}",
                step.proposition,
                proof_lines.join("\n")
            ));
            self.environment_stack
                .fact_names
                .insert(step.fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(step.fact_id, step.fact.clone());
            self.next_fact_name_index += 1;
            preceding_steps.push(step);
        }
        Ok(())
    }

    /// Validate one equality-chain closure Result against its exact source,
    /// then expose the adjacent edge FactIds as projections of the already
    /// published source proof. The returned allowlist roots later inference
    /// compilation in this Result rather than in ambient proposition lookup.
    pub(super) fn install_equality_chain_adjacent_projections_for_typed_inference(
        &mut self,
        source_fact: &Fact,
        source_fact_id: FactId,
        source_lean_reference: &str,
        infers: &SuccessInferResult,
        result_layer: &str,
    ) -> Result<Vec<(FactId, Fact)>, String> {
        let equality_applications = infers
            .rule_applications
            .iter()
            .filter(|application| matches!(application.rule, InferRule::EqualityChainClosure(_)))
            .collect::<Vec<_>>();
        if equality_applications.is_empty() {
            return Ok(vec![(source_fact_id, source_fact.clone())]);
        }
        let Fact::ChainFact(chain) = source_fact else {
            return Err(format!(
                "{result_layer} retained equality-chain closure for a non-chain source"
            ));
        };
        if chain
            .prop_names
            .iter()
            .any(|predicate| predicate.to_string() != EQUAL)
        {
            return Err(format!(
                "{result_layer} retained equality closure for a mixed relation chain"
            ));
        }
        let adjacent_facts = chain
            .facts()
            .map_err(|error| format!("{result_layer} retained an invalid chain: {error:?}"))?
            .into_iter()
            .map(Fact::from)
            .collect::<Vec<_>>();
        if adjacent_facts.len() < 2 {
            return Err(format!(
                "{result_layer} equality closure has fewer than two adjacent edges"
            ));
        }
        let expected_application_count = adjacent_facts
            .len()
            .saturating_sub(1)
            .saturating_mul(adjacent_facts.len())
            / 2;
        if equality_applications.len() != expected_application_count {
            return Err(format!(
                "{result_layer} expected {expected_application_count} equality closure applications, retained {}",
                equality_applications.len()
            ));
        }

        let mut adjacent_fact_ids = vec![None; adjacent_facts.len()];
        let mut application_index = 0;
        for start_object_index in 0..chain.objs.len() {
            for end_object_index in start_object_index + 2..chain.objs.len() {
                let application = equality_applications[application_index];
                let InferRule::EqualityChainClosure(rule) = &application.rule else {
                    unreachable!("filtered equality-chain application")
                };
                if rule.start_object_index != start_object_index
                    || rule.end_object_index != end_object_index
                {
                    return Err(format!(
                        "{result_layer} equality application {application_index} changed its object interval"
                    ));
                }
                let expected_premises = &adjacent_facts[start_object_index..end_object_index];
                if application.premises.len() != expected_premises.len() {
                    return Err(format!(
                        "{result_layer} equality application {application_index} changed its premise arity"
                    ));
                }
                for (offset, (premise, expected)) in application
                    .premises
                    .iter()
                    .zip(expected_premises.iter())
                    .enumerate()
                {
                    if premise.fact.to_string() != expected.to_string() {
                        return Err(format!(
                            "{result_layer} equality application {application_index} changed premise {offset}"
                        ));
                    }
                    let fact_id = premise.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} equality application {application_index} premise {offset} has no FactId"
                        )
                    })?;
                    let adjacent_index = start_object_index + offset;
                    match adjacent_fact_ids[adjacent_index] {
                        Some(existing) if existing != fact_id => {
                            return Err(format!(
                                "{result_layer} assigned two FactIds to adjacent equality {adjacent_index}"
                            ));
                        }
                        _ => adjacent_fact_ids[adjacent_index] = Some(fact_id),
                    }
                }
                let [conclusion] = application.conclusions.as_slice() else {
                    return Err(format!(
                        "{result_layer} equality application {application_index} must retain one conclusion"
                    ));
                };
                let expected_conclusion: Fact = EqualFact::new(
                    chain.objs[start_object_index].clone(),
                    chain.objs[end_object_index].clone(),
                    chain.line_file.clone(),
                )
                .into();
                validate_success_store_fact_result(
                    conclusion,
                    &expected_conclusion,
                    &format!("{result_layer} equality application {application_index}"),
                )?;
                application_index += 1;
            }
        }

        let mut allowed_sources = vec![(source_fact_id, source_fact.clone())];
        for (adjacent_index, (fact, fact_id)) in adjacent_facts
            .into_iter()
            .zip(adjacent_fact_ids.into_iter())
            .enumerate()
        {
            let fact_id = fact_id.ok_or_else(|| {
                format!("{result_layer} lost adjacent equality {adjacent_index} FactId")
            })?;
            let projection = conjunction_projection(
                &format!("({source_lean_reference})"),
                adjacent_index,
                chain.prop_names.len(),
            )?;
            self.environment_stack
                .fact_names
                .insert(fact_id, projection);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, fact.clone());
            allowed_sources.push((fact_id, fact));
        }
        Ok(allowed_sources)
    }

    /// Expose the exact adjacent premises used by retained mixed strict/weak
    /// numeric-order closure applications as projections of the source chain.
    pub(super) fn install_numeric_order_chain_adjacent_projections_for_typed_inference(
        &mut self,
        source_fact: &Fact,
        source_fact_id: FactId,
        source_lean_reference: &str,
        infers: &SuccessInferResult,
        result_layer: &str,
    ) -> Result<Vec<(FactId, Fact)>, String> {
        let applications = infers
            .rule_applications
            .iter()
            .filter(|application| {
                matches!(application.rule, InferRule::NumericOrderChainClosure(_))
            })
            .collect::<Vec<_>>();
        if applications.is_empty() {
            return Ok(vec![(source_fact_id, source_fact.clone())]);
        }
        let Fact::ChainFact(chain) = source_fact else {
            return Err(format!(
                "{result_layer} retained numeric-order closure for a non-chain source"
            ));
        };
        let expected_steps = chain
            .numeric_order_chain_closure_steps()
            .map_err(|error| format!("{result_layer} retained an invalid order chain: {error:?}"))?;
        if applications.len() != expected_steps.len() {
            return Err(format!(
                "{result_layer} expected {} numeric-order closure applications, retained {}",
                expected_steps.len(),
                applications.len()
            ));
        }
        let adjacent_facts = chain
            .facts()
            .map_err(|error| format!("{result_layer} retained an invalid chain: {error:?}"))?
            .into_iter()
            .map(Fact::from)
            .collect::<Vec<_>>();
        let mut adjacent_fact_ids = vec![None; adjacent_facts.len()];
        for (application_index, (application, expected)) in
            applications.iter().zip(expected_steps.iter()).enumerate()
        {
            let InferRule::NumericOrderChainClosure(rule) = &application.rule else {
                unreachable!("filtered numeric-order application")
            };
            if rule.start_object_index != expected.start_object_index
                || rule.end_object_index != expected.end_object_index
                || application.premises.len() != expected.premises.len()
                || application.conclusions.len() != 1
            {
                return Err(format!(
                    "{result_layer} numeric-order application {application_index} changed its interval or arity"
                ));
            }
            for (offset, (premise, expected_premise)) in application
                .premises
                .iter()
                .zip(expected.premises.iter())
                .enumerate()
            {
                if premise.fact.to_string() != expected_premise.to_string() {
                    return Err(format!(
                        "{result_layer} numeric-order application {application_index} changed premise {offset}"
                    ));
                }
                let fact_id = premise.fact_id.ok_or_else(|| {
                    format!(
                        "{result_layer} numeric-order application {application_index} premise {offset} has no FactId"
                    )
                })?;
                let adjacent_index = expected.start_object_index + offset;
                match adjacent_fact_ids[adjacent_index] {
                    Some(existing) if existing != fact_id => {
                        return Err(format!(
                            "{result_layer} assigned two FactIds to order edge {adjacent_index}"
                        ));
                    }
                    _ => adjacent_fact_ids[adjacent_index] = Some(fact_id),
                }
            }
            if application.conclusions[0].fact.to_string()
                != Fact::from(expected.conclusion.clone()).to_string()
            {
                return Err(format!(
                    "{result_layer} numeric-order application {application_index} changed its conclusion"
                ));
            }
        }

        let mut allowed_sources = vec![(source_fact_id, source_fact.clone())];
        for (adjacent_index, (fact, fact_id)) in adjacent_facts
            .into_iter()
            .zip(adjacent_fact_ids.into_iter())
            .enumerate()
        {
            let Some(fact_id) = fact_id else {
                continue;
            };
            let projection = conjunction_projection(
                &format!("({source_lean_reference})"),
                adjacent_index,
                chain.prop_names.len(),
            )?;
            self.environment_stack.fact_names.insert(fact_id, projection);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, fact.clone());
            allowed_sources.push((fact_id, fact));
        }
        Ok(allowed_sources)
    }

    /// `Combine`: publish the two exact consequences retained when equality
    /// exposes a literal tuple shape. The current Lean representation can
    /// replay this rule when the selected target is the same concrete tuple;
    /// other heterogeneous transports remain fail-closed until the Lean ABI
    /// has an explicit tuple-shape transport theorem.
    pub(super) fn compile_tuple_equality_shape_infer_result(
        &mut self,
        source_fact: &Fact,
        source_fact_id: FactId,
        infers: &SuccessInferResult,
    ) -> Result<(), String> {
        validate_typed_infer_result_identity_completeness(
            infers,
            "tuple-equality shape inference",
        )?;
        let [application] = infers.rule_applications.as_slice() else {
            return Err("tuple equality must retain exactly one typed shape inference".into());
        };
        let InferRule::TupleEqualityWithKnownTupleImpliesTupleShape(rule) = &application.rule
        else {
            return Err("object reflexivity retained a non-tuple inference rule".into());
        };
        let [premise] = application.premises.as_slice() else {
            return Err("tuple-shape inference must cite one equality premise".into());
        };
        if premise.fact_id != Some(source_fact_id)
            || premise.fact.to_string() != source_fact.to_string()
        {
            return Err("tuple-shape inference changed its source equality FactId".into());
        }
        let equality_proof =
            resolve_fact_citation(&source_fact_id, source_fact, &self.environment_stack)?;
        if equality_proof.is_empty() {
            return Err("tuple-shape inference resolved an empty equality proof".into());
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = source_fact else {
            return Err("tuple-shape inference source is not equality".into());
        };
        let (known_object, target_object) = match rule.known_side {
            KnownTupleEqualitySide::Left => (&equality.left, &equality.right),
            KnownTupleEqualitySide::Right => (&equality.right, &equality.left),
        };
        let Obj::Tuple(known_tuple) = known_object else {
            return Err("tuple-shape inference selected a non-tuple known side".into());
        };
        if known_tuple.args.len() != rule.tuple_length || rule.tuple_length < 2 {
            return Err("tuple-shape inference changed its retained tuple length".into());
        }
        if obj_equality_key(known_object) != obj_equality_key(target_object) {
            return Err(
                "tuple-shape inference requires an explicit Lean transport theorem for a distinct target object"
                    .into(),
            );
        }

        let expected_tuple_fact: Fact =
            IsTupleFact::new(target_object.clone(), equality.line_file.clone()).into();
        let expected_dimension_fact: Fact = EqualFact::new(
            TupleDim::new(target_object.clone()).into(),
            Number::new(rule.tuple_length.to_string()).into(),
            equality.line_file.clone(),
        )
        .into();
        let expected = [
            (expected_tuple_fact, "⟨inferInstance⟩".to_string()),
            (
                expected_dimension_fact,
                "Litex.Same.ofEq (by norm_num [Litex.tupleDim, Litex.TupleShape.dimension])"
                    .to_string(),
            ),
        ];
        if application.conclusions.len() != expected.len() {
            return Err("tuple-shape inference changed its two-conclusion contract".into());
        }

        for (conclusion, (expected_fact, proof)) in
            application.conclusions.iter().zip(expected.into_iter())
        {
            if conclusion.fact.to_string() != expected_fact.to_string() {
                return Err("tuple-shape inference changed an ordered conclusion".into());
            }
            let fact_id = conclusion
                .fact_id
                .ok_or_else(|| "tuple-shape conclusion has no FactId".to_string())?;
            let recursively_stored = conclusion.infers.store_fact_outputs.iter().any(|output| {
                output.fact_id == Some(fact_id)
                    && output.itself_and_why_itself_is_stored.0.to_string()
                        == conclusion.fact.to_string()
            });
            if !recursively_stored {
                return Err("tuple-shape conclusion lost its recursive store Result".into());
            }
            let advertised = infers.store_fact_outputs.iter().any(|output| {
                output
                    .inferred_facts
                    .iter()
                    .zip(output.inferred_fact_ids.iter())
                    .any(|(fact, id)| {
                        fact.to_string() == conclusion.fact.to_string() && *id == Some(fact_id)
                    })
                    || (output.fact_id == Some(fact_id)
                        && output.itself_and_why_itself_is_stored.0.to_string()
                            == conclusion.fact.to_string())
            });
            if !advertised {
                return Err("tuple-shape conclusion is absent from ordered store effects".into());
            }
            let proposition = render_fact(&conclusion.fact, &self.environment_stack)?;
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {theorem_name} : {proposition} := by\n  exact {proof}"
            ));
            self.environment_stack
                .fact_names
                .insert(fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, conclusion.fact.clone());
            self.next_fact_name_index += 1;
        }
        validate_flattened_inferred_fact_ids_are_visible(
            infers,
            &self.environment_stack,
            "tuple-equality shape inference",
        )
    }

    pub(super) fn next_local_inference_fact_proof_name(&mut self) -> String {
        let name = format!(
            "__infer{}_{}",
            self.next_fact_name_index, self.next_local_inference_name_index
        );
        self.next_local_inference_name_index += 1;
        name
    }

    pub(super) fn retain_compiled_inference_fact_proof_step_in_current_environment(
        &mut self,
        compiled_steps: &mut Vec<CompiledInferenceFactProofStep>,
        step: CompiledInferenceFactProofStep,
        availability: CompiledInferenceFactAvailabilityInLeanEnvironment,
    ) {
        let lean_reference = match availability {
            CompiledInferenceFactAvailabilityInLeanEnvironment::LocalProofName => {
                step.local_lean_name.clone()
            }
            CompiledInferenceFactAvailabilityInLeanEnvironment::InlineProofExpression => {
                format!("({})", step.proof_expression)
            }
        };
        self.environment_stack
            .fact_names
            .insert(step.fact_id, lean_reference);
        self.environment_stack
            .fact_propositions
            .insert(step.fact_id, step.fact.clone());
        compiled_steps.push(step);
    }

    /// Compile the typed inference children owned by one active Result scope.
    ///
    /// The returned records retain identity, proposition, name, and proof as
    /// separate fields. Callers decide whether those records become local
    /// `have`s, anonymous-function `let`s, or top-level theorems. No caller is
    /// permitted to recover semantic fields by parsing rendered Lean source.
    pub(super) fn compile_typed_inference_results_in_current_compiler_environment(
        &mut self,
        infers: &SuccessInferResult,
        allowed_sources: &[(FactId, Fact)],
        availability: CompiledInferenceFactAvailabilityInLeanEnvironment,
        result_layer: &str,
        force_replay_visible_conclusions: Option<&HashSet<FactId>>,
    ) -> Result<Vec<CompiledInferenceFactProofStep>, String> {
        validate_typed_infer_result_identity_completeness(infers, result_layer)?;

        let mut compiled_inference_fact_proof_steps = Vec::new();
        let mut advertised_conclusions = HashSet::new();
        for (store_index, output) in infers.store_fact_outputs.iter().enumerate() {
            let source_fact_id = output.fact_id.ok_or_else(|| {
                format!("{result_layer} store {store_index} has no source FactId")
            })?;
            if !allowed_sources.iter().any(|(allowed_fact_id, fact)| {
                *allowed_fact_id == source_fact_id
                    && fact.to_string() == output.itself_and_why_itself_is_stored.0.to_string()
            }) {
                return Err(format!(
                    "{result_layer} store {store_index} is not owned by a visible source fact"
                ));
            }
            if output.inferred_facts.len() != output.inferred_fact_ids.len() {
                return Err(format!(
                    "{result_layer} store {store_index} changed its inferred FactId arity"
                ));
            }
            for (fact, fact_id) in output
                .inferred_facts
                .iter()
                .zip(output.inferred_fact_ids.iter())
            {
                let fact_id = fact_id.ok_or_else(|| {
                    format!("{result_layer} advertised inferred fact `{fact}` without a FactId")
                })?;
                if !advertised_conclusions.insert((fact_id, fact.to_string())) {
                    return Err(format!(
                        "{result_layer} advertised inferred FactId `{fact_id}` more than once"
                    ));
                }
            }
        }

        let mut compiled_conclusions = HashSet::new();
        for (application_index, application) in infers.rule_applications.iter().enumerate() {
            let expected_premise_count = match &application.rule {
                InferRule::MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(_) => 2,
                InferRule::PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembership(
                    _,
                ) => 3,
                InferRule::EqualityChainClosure(rule) => rule
                    .end_object_index
                    .checked_sub(rule.start_object_index)
                    .ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} reversed its equality-chain interval"
                        )
                    })?,
                InferRule::NumericOrderChainClosure(rule) => rule
                    .end_object_index
                    .checked_sub(rule.start_object_index)
                    .ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} reversed its numeric-order interval"
                        )
                    })?,
                _ => 1,
            };
            if !infer_rule_has_direct_compiler_environment_consumer(&application.rule)
                || application.premises.len() != expected_premise_count
                || application.conclusions.len() != 1
            {
                return Err(format!(
                    "{result_layer} application {application_index} has no supported direct compiler-environment consumer"
                ));
            }
            let premise = &application.premises[0];
            let premise_fact_id = premise.fact_id.ok_or_else(|| {
                format!("{result_layer} application {application_index} premise has no FactId")
            })?;
            let premise_key = (premise_fact_id, premise.fact.to_string());
            if !allowed_sources.iter().any(|(allowed_fact_id, fact)| {
                *allowed_fact_id == premise_fact_id && fact.to_string() == premise.fact.to_string()
            }) && !compiled_conclusions.contains(&premise_key)
                && !self
                    .environment_stack
                    .fact_propositions
                    .get(&premise_fact_id)
                    .is_some_and(|visible| visible.to_string() == premise.fact.to_string())
            {
                let allowed = allowed_sources
                    .iter()
                    .map(|(fact_id, fact)| format!("{fact_id}:{fact}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                return Err(format!(
                    "{result_layer} application {application_index} ({:?}) cites `{premise_fact_id}:{}` outside this Result layer; allowed exact roots or earlier typed conclusions: [{allowed}]",
                    application.rule,
                    premise.fact,
                ));
            }
            if matches!(application.rule, InferRule::EqualityChainClosure(_)) {
                for (premise_index, premise) in application.premises.iter().enumerate() {
                    let premise_fact_id = premise.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} premise {premise_index} has no FactId"
                        )
                    })?;
                    if !allowed_sources.iter().any(|(allowed_fact_id, fact)| {
                        *allowed_fact_id == premise_fact_id
                            && fact.to_string() == premise.fact.to_string()
                    }) {
                        return Err(format!(
                            "{result_layer} application {application_index} equality premise {premise_index} is outside its source chain"
                        ));
                    }
                }
            }

            let conclusion = &application.conclusions[0];
            let conclusion_fact_id = conclusion.fact_id.ok_or_else(|| {
                format!("{result_layer} application {application_index} conclusion has no FactId")
            })?;
            let conclusion_key = (conclusion_fact_id, conclusion.fact.to_string());
            let force_replay = force_replay_visible_conclusions
                .is_some_and(|fact_ids| fact_ids.contains(&conclusion_fact_id));
            let conclusion_already_visible = if self
                .environment_stack
                .fact_propositions
                .contains_key(&conclusion_fact_id)
            {
                resolve_fact_citation(
                    &conclusion_fact_id,
                    &conclusion.fact,
                    &self.environment_stack,
                )?;
                !force_replay
            } else {
                false
            };
            let conclusion_is_advertised = advertised_conclusions.contains(&conclusion_key);
            if !conclusion_is_advertised && !conclusion_already_visible && !force_replay {
                return Err(format!(
                    "{result_layer} application {application_index} conclusion is neither in its ordered store output nor already visible by exact FactId"
                ));
            }
            if conclusion_is_advertised && !compiled_conclusions.insert(conclusion_key) {
                return Err(format!(
                    "{result_layer} application {application_index} repeats an inferred conclusion"
                ));
            }
            if let InferRule::NumericOrderChainClosure(rule) = &application.rule {
                if rule.end_object_index < rule.start_object_index + 2 {
                    return Err(format!(
                        "{result_layer} application {application_index} does not span a non-adjacent order consequence"
                    ));
                }
                let descending = application.premises.iter().all(|premise| {
                    matches!(
                        premise.fact,
                        Fact::AtomicFact(
                            AtomicFact::GreaterFact(_) | AtomicFact::GreaterEqualFact(_)
                        )
                    )
                });
                let ascending = application.premises.iter().all(|premise| {
                    matches!(
                        premise.fact,
                        Fact::AtomicFact(
                            AtomicFact::LessFact(_) | AtomicFact::LessEqualFact(_)
                        )
                    )
                });
                if ascending == descending {
                    return Err(format!(
                        "{result_layer} application {application_index} mixes incompatible order directions"
                    ));
                }
                let ordered_premises = if descending {
                    application.premises.iter().rev().collect::<Vec<_>>()
                } else {
                    application.premises.iter().collect::<Vec<_>>()
                };
                let mut rendered = Vec::with_capacity(ordered_premises.len());
                let mut expected_left = None;
                let mut expected_right: Option<Obj> = None;
                for (premise_index, premise) in ordered_premises.iter().enumerate() {
                    let fact_id = premise.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} premise {premise_index} has no FactId"
                        )
                    })?;
                    let visible = allowed_sources.iter().any(|(allowed_id, fact)| {
                        *allowed_id == fact_id && fact.to_string() == premise.fact.to_string()
                    }) || compiled_conclusions
                        .contains(&(fact_id, premise.fact.to_string()));
                    if !visible {
                        return Err(format!(
                            "{result_layer} application {application_index} order premise {premise_index} is outside its source chain"
                        ));
                    }
                    let (left, right, strict) = order_relation_parts(&premise.fact)?;
                    if let Some(previous_right) = expected_right.as_ref() {
                        if obj_equality_key(previous_right) != obj_equality_key(left) {
                            return Err(format!(
                                "{result_layer} application {application_index} order premises are not endpoint-contiguous"
                            ));
                        }
                    } else {
                        expected_left = Some(left.clone());
                    }
                    expected_right = Some(right.clone());
                    rendered.push((
                        resolve_fact_citation(
                            &fact_id,
                            &premise.fact,
                            &self.environment_stack,
                        )?,
                        strict,
                    ));
                }
                let (conclusion_left, conclusion_right, conclusion_strict) =
                    order_relation_parts(&conclusion.fact)?;
                if obj_equality_key(expected_left.as_ref().ok_or_else(|| {
                    format!(
                        "{result_layer} application {application_index} retained no order premises"
                    )
                })?) != obj_equality_key(conclusion_left)
                    || obj_equality_key(expected_right.as_ref().ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} retained no order endpoint"
                        )
                    })?) != obj_equality_key(conclusion_right)
                    || conclusion_strict != rendered.iter().any(|(_, strict)| *strict)
                {
                    return Err(format!(
                        "{result_layer} application {application_index} changed its order endpoints or strictness"
                    ));
                }
                if !conclusion_already_visible {
                    let (mut proof, mut proof_is_strict) = rendered[0].clone();
                    for (next, next_is_strict) in rendered.iter().skip(1) {
                        let theorem = match (proof_is_strict, *next_is_strict) {
                            (false, false) => "Litex.Le.trans",
                            (false, true) => "Litex.Le.transLt",
                            (true, false) => "Litex.Lt.transLe",
                            (true, true) => "Litex.Lt.trans",
                        };
                        proof = format!("{theorem} ({proof}) ({next})");
                        proof_is_strict |= *next_is_strict;
                    }
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            proof,
                        ),
                        availability,
                    );
                }
            } else if let InferRule::EqualityChainClosure(rule) = &application.rule {
                if rule.end_object_index < rule.start_object_index + 2 {
                    return Err(format!(
                        "{result_layer} application {application_index} does not span a non-adjacent equality"
                    ));
                }
                let mut expected_left: Option<Obj> = None;
                let mut expected_right: Option<Obj> = None;
                let mut proof_parts = Vec::with_capacity(application.premises.len());
                let mut native_proof_parts = Some(Vec::with_capacity(application.premises.len()));
                for (premise_index, premise) in application.premises.iter().enumerate() {
                    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &premise.fact else {
                        return Err(format!(
                            "{result_layer} application {application_index} premise {premise_index} is not equality"
                        ));
                    };
                    if let Some(previous_right) = expected_right.as_ref() {
                        if obj_equality_key(previous_right) != obj_equality_key(&equality.left) {
                            return Err(format!(
                                "{result_layer} application {application_index} equality premises are not endpoint-contiguous"
                            ));
                        }
                    } else {
                        expected_left = Some(equality.left.clone());
                    }
                    expected_right = Some(equality.right.clone());
                    let premise_fact_id = premise.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} premise {premise_index} has no FactId"
                        )
                    })?;
                    proof_parts.push(resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?);
                    if let Some(parts) = native_proof_parts.as_mut() {
                        if let Some(binding) = self
                            .environment_stack
                            .native_equality_proofs
                            .get(&premise_fact_id)
                        {
                            if binding.fact.to_string() != premise.fact.to_string() {
                                return Err(format!(
                                    "{result_layer} application {application_index} native equality premise {premise_index} changed its FactId proposition"
                                ));
                            }
                            parts.push(binding.proof_expression.clone());
                        } else {
                            native_proof_parts = None;
                        }
                    }
                }
                let Fact::AtomicFact(AtomicFact::EqualFact(conclusion_equality)) =
                    &conclusion.fact
                else {
                    return Err(format!(
                        "{result_layer} application {application_index} equality closure has a non-equality conclusion"
                    ));
                };
                if obj_equality_key(expected_left.as_ref().ok_or_else(|| {
                    format!(
                        "{result_layer} application {application_index} retained no equality premises"
                    )
                })?) != obj_equality_key(&conclusion_equality.left)
                    || obj_equality_key(expected_right.as_ref().ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} retained no equality endpoint"
                        )
                    })?) != obj_equality_key(&conclusion_equality.right)
                {
                    return Err(format!(
                        "{result_layer} application {application_index} changed its equality endpoints"
                    ));
                }
                if !conclusion_already_visible {
                    let mut proof = proof_parts[0].clone();
                    for next in proof_parts.iter().skip(1) {
                        proof = format!("Litex.Same.trans ({proof}) ({next})");
                    }
                    if let Some(native_parts) = native_proof_parts {
                        let mut native_proof = native_parts[0].clone();
                        for next in native_parts.iter().skip(1) {
                            native_proof = format!("Eq.trans ({native_proof}) ({next})");
                        }
                        self.retain_native_equality_proof_in_current_environment(
                            conclusion_fact_id,
                            &conclusion.fact,
                            native_proof,
                        )?;
                    }
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            proof,
                        ),
                        availability,
                    );
                }
            } else if let InferRule::ConjunctionImpliesComponent(rule) = &application.rule {
                validate_conjunction_component_inference_target(
                    rule,
                    &premise.fact,
                    &conclusion.fact,
                )?;
                if !conclusion_already_visible {
                    let premise_name = resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?;
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    let projection = conjunction_projection(
                        &format!("({premise_name})"),
                        rule.component_index,
                        rule.component_count,
                    )?;
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            projection,
                        ),
                        availability,
                    );
                }
            } else if let InferRule::ClosedPositivePowerEqualityImpliesEqualSideMembership(rule) =
                &application.rule
            {
                if !conclusion_already_visible {
                    let premise_name = resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?;
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    let proof = render_closed_positive_power_equality_membership_inference(
                        rule,
                        &premise.fact,
                        &conclusion.fact,
                        &premise_name,
                        &self.environment_stack,
                    )?;
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            proof,
                        ),
                        availability,
                    );
                }
            } else if let InferRule::PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembership(
                rule,
            ) = &application.rule
            {
                let base_positive = &application.premises[1];
                let base_in_z = &application.premises[2];
                for (premise_index, additional) in
                    application.premises.iter().enumerate().skip(1)
                {
                    let fact_id = additional.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} premise {premise_index} has no FactId"
                        )
                    })?;
                    let key = (fact_id, additional.fact.to_string());
                    let visible = allowed_sources.iter().any(|(allowed_fact_id, fact)| {
                        *allowed_fact_id == fact_id
                            && fact.to_string() == additional.fact.to_string()
                    }) || compiled_conclusions.contains(&key)
                        || self
                            .environment_stack
                            .fact_propositions
                            .get(&fact_id)
                            .is_some_and(|fact| fact.to_string() == additional.fact.to_string());
                    if !visible {
                        return Err(format!(
                            "{result_layer} application {application_index} premise {premise_index} is not an exact visible root or earlier typed conclusion"
                        ));
                    }
                }
                if !conclusion_already_visible {
                    let equality_proof = resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?;
                    let base_positive_fact_id = base_positive.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} positivity premise has no FactId"
                        )
                    })?;
                    let base_positive_proof = resolve_fact_citation(
                        &base_positive_fact_id,
                        &base_positive.fact,
                        &self.environment_stack,
                    )?;
                    let base_in_z_fact_id = base_in_z.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} Z premise has no FactId"
                        )
                    })?;
                    resolve_fact_citation(
                        &base_in_z_fact_id,
                        &base_in_z.fact,
                        &self.environment_stack,
                    )?;
                    let (expected_conclusion, proof) =
                        render_positive_integer_base_natural_power_equality_membership_inference(
                            rule,
                            &premise.fact,
                            &base_positive.fact,
                            &base_in_z.fact,
                            &equality_proof,
                            &base_positive_proof,
                            &self.environment_stack,
                        )?;
                    if expected_conclusion.to_string() != conclusion.fact.to_string() {
                        return Err(format!(
                            "{result_layer} application {application_index} changed its transported R+ conclusion"
                        ));
                    }
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            proof,
                        ),
                        availability,
                    );
                }
            } else if matches!(
                application.rule,
                InferRule::MultiplicationByNegativeOneReversesOrderAgainstZero
                    | InferRule::StrictOrderComparedToZeroImpliesWeakOrder
                    | InferRule::NumericOrderBoundImpliesZeroSign
            ) {
                if !conclusion_already_visible {
                    let premise_name = resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?;
                    if matches!(
                        application.rule,
                        InferRule::NumericOrderBoundImpliesZeroSign
                    ) {
                        let conclusion_proposition =
                            render_fact(&conclusion.fact, &self.environment_stack)?;
                        let conclusion_name = self.next_local_inference_fact_proof_name();
                        let proof = render_numeric_order_bound_implies_zero_sign_inference(
                            &premise.fact,
                            &conclusion.fact,
                            &premise_name,
                            &self.environment_stack,
                        )?;
                        self.retain_compiled_inference_fact_proof_step_in_current_environment(
                            &mut compiled_inference_fact_proof_steps,
                            CompiledInferenceFactProofStep::new(
                                conclusion_fact_id,
                                conclusion.fact.clone(),
                                conclusion_name,
                                conclusion_proposition,
                                proof,
                            ),
                            availability,
                        );
                    } else {
                        validate_order_sign_inference_target(
                            &application.rule,
                            &premise.fact,
                            &conclusion.fact,
                        )?;
                        let transported_premise =
                            transport_zero_ended_order_fact_proof_to_current_numeric_representation(
                                &premise.fact,
                                &premise_name,
                                &self.environment_stack,
                            )?;
                        let conclusion_proposition =
                            render_fact(&conclusion.fact, &self.environment_stack)?;
                        let conclusion_name = self.next_local_inference_fact_proof_name();
                        let proof = match application.rule {
                        InferRule::StrictOrderComparedToZeroImpliesWeakOrder => {
                            let (source_left, source_right, _) =
                                order_relation_parts(&premise.fact)?;
                            if is_literal_zero(source_left) {
                                format!("Litex.Positive.toNonnegative ({transported_premise})")
                            } else if is_literal_zero(source_right) {
                                format!("Litex.Negative.toNonpositive ({transported_premise})")
                            } else {
                                return Err(format!(
                                    "{result_layer} application {application_index} strict-to-weak premise is not compared with zero"
                                ));
                            }
                        }
                        InferRule::MultiplicationByNegativeOneReversesOrderAgainstZero => {
                            let (source_left, source_right, source_is_strict) =
                                order_relation_parts(&premise.fact)?;
                            if is_literal_zero(source_left) {
                                let theorem = if source_is_strict {
                                    "complexNegativeOneMulNegative"
                                } else {
                                    "complexNegativeOneMulNonpositive"
                                };
                                format!("Litex.Rules.{theorem} ({transported_premise})")
                            } else if is_literal_zero(source_right) {
                                let nonpositive_premise = if source_is_strict {
                                    format!("Litex.Negative.toNonpositive ({transported_premise})")
                                } else {
                                    transported_premise
                                };
                                format!(
                                    "Litex.Rules.complexNegativeOneMulNonnegative ({nonpositive_premise})"
                                )
                            } else {
                                return Err(format!(
                                    "{result_layer} application {application_index} negative-one premise is not compared with zero"
                                ));
                            }
                        }
                            _ => unreachable!("order-sign inference was matched above"),
                        };
                        self.retain_compiled_inference_fact_proof_step_in_current_environment(
                            &mut compiled_inference_fact_proof_steps,
                            CompiledInferenceFactProofStep::new(
                                conclusion_fact_id,
                                conclusion.fact.clone(),
                                conclusion_name,
                                conclusion_proposition,
                                proof,
                            ),
                            availability,
                        );
                    }
                }
            } else if matches!(
                application.rule,
                InferRule::SetBuilderBaseMembershipProjection
                    | InferRule::SetBuilderPredicateProjection { .. }
            ) {
                if !conclusion_already_visible {
                    let premise_name = resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?;
                    let proof = match &application.rule {
                        InferRule::SetBuilderBaseMembershipProjection => {
                            let (source_element, source_set) = membership_parts(&premise.fact)?;
                            let Obj::SetBuilder(builder) = source_set else {
                                return Err(format!(
                                    "{result_layer} application {application_index} set-builder base projection cites another set constructor"
                                ));
                            };
                            let (target_element, target_set) = membership_parts(&conclusion.fact)?;
                            if obj_equality_key(source_element) != obj_equality_key(target_element)
                                || obj_equality_key(builder.param_set.as_ref())
                                    != obj_equality_key(target_set)
                            {
                                return Err(format!(
                                    "{result_layer} application {application_index} changed its set-builder base projection"
                                ));
                            }
                            format!("Litex.Rules.inBaseOfInSetBuilder ({premise_name})")
                        }
                        InferRule::SetBuilderPredicateProjection { clause_index } => {
                            render_set_builder_predicate_projection_from_fact_and_proof(
                                &conclusion.fact,
                                *clause_index,
                                &premise.fact,
                                &premise_name,
                                &self.environment_stack,
                            )?
                        }
                        _ => unreachable!("set-builder inference was matched above"),
                    };
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            proof,
                        ),
                        availability,
                    );
                }
            } else if let InferRule::ListSetMembershipImpliesEqualityAlternatives(rule) =
                &application.rule
            {
                let (_, source_set) = membership_parts(&premise.fact)?;
                let Obj::ListSet(list_set) = source_set else {
                    return Err(format!(
                        "{result_layer} application {application_index} literal alternatives cite another set constructor"
                    ));
                };
                if rule.element_count == 0 || rule.element_count != list_set.list.len() {
                    return Err(format!(
                        "{result_layer} application {application_index} changed its literal alternatives arity"
                    ));
                }
                if !conclusion_already_visible {
                    let premise_name = resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?;
                    let proof = render_list_set_membership_elimination_from_fact_and_proof(
                        &conclusion.fact,
                        &premise.fact,
                        &premise_name,
                        &self.environment_stack,
                    )?;
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            proof,
                        ),
                        availability,
                    );
                }
            } else if matches!(
                application.rule,
                InferRule::MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(_)
                    | InferRule::SubsetImpliesElementwiseMembershipForall(_)
                    | InferRule::SupersetImpliesElementwiseMembershipForall(_)
            ) {
                // These runtime search accelerators are local to this binder.
                // Validate their complete typed shape, but do not publish an
                // unreviewed Lean proof. If a later Result actually cites one,
                // exact FactId resolution fails closed instead of silently
                // recreating the inference in Lean.
                if let InferRule::MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(
                    rule,
                ) = &application.rule
                {
                    let equality_premise = &application.premises[1];
                    let equality_fact_id = equality_premise.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} set equality has no FactId"
                        )
                    })?;
                    resolve_fact_citation(
                        &equality_fact_id,
                        &equality_premise.fact,
                        &self.environment_stack,
                    )?;
                    validate_membership_in_equal_set_inference_target(
                        rule,
                        &premise.fact,
                        &equality_premise.fact,
                        &conclusion.fact,
                    )?;
                } else if matches!(
                    application.rule,
                    InferRule::SubsetImpliesElementwiseMembershipForall(_)
                        | InferRule::SupersetImpliesElementwiseMembershipForall(_)
                ) {
                    validate_set_inclusion_elementwise_forall_inference_target(
                        &application.rule,
                        &premise.fact,
                        &conclusion.fact,
                    )?;
                }
            } else {
                let lean_theorem_name = validate_standard_numeric_membership_inference_target(
                    &application.rule,
                    &premise.fact,
                    &conclusion.fact,
                    &self.environment_stack,
                )?;
                if !conclusion_already_visible {
                    let premise_name = resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?;
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            format!("Litex.Rules.{lean_theorem_name} ({premise_name})"),
                        ),
                        availability,
                    );
                }
            }
            if !conclusion.infers.is_empty() {
                compiled_inference_fact_proof_steps.extend(
                    self.compile_typed_inference_results_in_current_compiler_environment(
                        &conclusion.infers,
                        &[(conclusion_fact_id, conclusion.fact.clone())],
                        availability,
                        &format!("{result_layer} application {application_index} conclusion"),
                        force_replay_visible_conclusions,
                    )?,
                );
                let mut recursively_compiled = HashSet::new();
                collect_supported_typed_infer_conclusions(
                    &conclusion.infers,
                    &mut recursively_compiled,
                );
                compiled_conclusions.extend(
                    recursively_compiled
                        .into_iter()
                        .filter(|conclusion| advertised_conclusions.contains(conclusion)),
                );
            }
        }

        // Only typed applications become Lean proof steps. Legacy flattened
        // store effects remain inert; if a later Result actually cites one,
        // exact FactId resolution will still fail closed at that use site.
        Ok(compiled_inference_fact_proof_steps)
    }

    /// Final target-source rendering for callers that already own a Lean
    /// tactic block. The structured compilation above remains the only place
    /// that creates or installs an inferred fact.
    pub(super) fn compile_typed_inference_results_as_local_have_statements(
        &mut self,
        infers: &SuccessInferResult,
        allowed_sources: &[(FactId, Fact)],
        proof_lines: &mut Vec<String>,
        result_layer: &str,
    ) -> Result<(), String> {
        let compiled_steps = self.compile_typed_inference_results_in_current_compiler_environment(
            infers,
            allowed_sources,
            CompiledInferenceFactAvailabilityInLeanEnvironment::LocalProofName,
            result_layer,
            None,
        )?;
        proof_lines.extend(
            compiled_steps
                .iter()
                .map(CompiledInferenceFactProofStep::render_as_local_have_statement),
        );
        Ok(())
    }

    /// Structured binders may reuse verified inference FactIds while changing
    /// only the Lean name of the exact source parameter. Replay those typed
    /// conclusions from the locally rebound assumptions instead of inheriting
    /// proof strings that mention the enclosing binder.
    pub(super) fn compile_typed_inference_results_as_local_have_statements_replaying_visible(
        &mut self,
        infers: &SuccessInferResult,
        allowed_sources: &[(FactId, Fact)],
        proof_lines: &mut Vec<String>,
        result_layer: &str,
        force_replay_visible_conclusions: &HashSet<FactId>,
    ) -> Result<(), String> {
        let compiled_steps = self.compile_typed_inference_results_in_current_compiler_environment(
            infers,
            allowed_sources,
            CompiledInferenceFactAvailabilityInLeanEnvironment::LocalProofName,
            result_layer,
            Some(force_replay_visible_conclusions),
        )?;
        proof_lines.extend(
            compiled_steps
                .iter()
                .map(CompiledInferenceFactProofStep::render_as_local_have_statement),
        );
        Ok(())
    }

    /// Validate the same typed inference Result as the proof-block route, but
    /// retain each conclusion as a direct Lean proof expression. Function and
    /// matrix constructors have no surrounding tactic block in which to emit
    /// a local `have`; their inherited compiler frame still owns the exact
    /// inferred FactIds and drops them when the Result-owned body is left.
    pub(super) fn install_standard_numeric_membership_inference_results_in_current_environment(
        &mut self,
        infers: &SuccessInferResult,
        allowed_sources: &[(FactId, Fact)],
        result_layer: &str,
    ) -> Result<(), String> {
        let _compiled_steps = self
            .compile_typed_inference_results_in_current_compiler_environment(
                infers,
                allowed_sources,
                CompiledInferenceFactAvailabilityInLeanEnvironment::InlineProofExpression,
                result_layer,
                None,
            )?;
        Ok(())
    }
}
