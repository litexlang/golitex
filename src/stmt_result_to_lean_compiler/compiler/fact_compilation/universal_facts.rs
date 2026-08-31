//! Direct universal fact result compilation and support reporting.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: enter the binder owned by a `ForallProof`, install its
    /// parameter SymbolIds and FactIds in one inherited compiler environment,
    /// install any zero-extra-inference domain FactIds, compile the ordered
    /// conclusion Results there, then pop before publishing the outer forall
    /// theorem. Typed inference children are validated and either compiled as
    /// local `have` declarations or installed as exact target bindings in the
    /// same binder environment.
    pub(in super::super) fn compile_direct_forall_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        self.compile_direct_forall_fact_result_with_optional_real_subset_observer(result, None)
    }

    /// Compile a verifier-owned forall while observing parameters of one
    /// exact set through the same checked `set subset R` proof consumed by a
    /// real-completeness theorem.  This is an internal adapter for a theorem
    /// requirement, not a change to the public heterogeneous forall ABI.
    pub(in super::super) fn compile_direct_forall_fact_result_with_real_subset_observer(
        &mut self,
        result: &SuccessFactStmtResult,
        observed_set: &Obj,
        subset_proof: &str,
    ) -> Result<bool, String> {
        self.compile_direct_forall_fact_result_with_optional_real_subset_observer(
            result,
            Some((observed_set, subset_proof)),
        )
    }

    fn compile_direct_forall_fact_result_with_optional_real_subset_observer(
        &mut self,
        result: &SuccessFactStmtResult,
        real_subset_observer: Option<(&Obj, &str)>,
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
        let mut forall_well_definedness =
            self.construct_well_definedness_to_lean_compilation_context(&result.well_definedness)?;
        if let Some(enclosing_well_definedness) = self.environment_stack.well_definedness.as_ref() {
            forall_well_definedness.merge_from(enclosing_well_definedness)?;
        }

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
                for (_premise_index, ((source_premise, well_defined_premise), fact_id)) in
                    source_forall
                        .dom_facts
                        .iter()
                        .zip(well_definedness.premises.iter())
                        .zip(premise_fact_ids.iter())
                        .enumerate()
                {
                    let premise_name = format!("__domain_f{}", fact_id.value());
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
                    if forall_parameter_uses_implicit_host_carrier(parameter_type) {
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
                            } else if forall_parameter_uses_exact_object_carrier(set) {
                                let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
                                self.environment_stack
                                    .exact_carrier_values
                                    .insert(binding.id(), parameter_name.clone());
                                if forall_parameter_uses_exact_refined_numeric_carrier(set) {
                                    self.environment_stack
                                        .exact_positive_real_carriers
                                        .insert(binding.id(), parameter_name.clone());
                                }
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
                            } else if forall_parameter_uses_exact_object_carrier(set) {
                                let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
                                self.environment_stack
                                    .exact_carrier_values
                                    .insert(binding.id(), parameter_name.clone());
                                if forall_parameter_uses_exact_refined_numeric_carrier(set) {
                                    self.environment_stack
                                        .exact_positive_real_carriers
                                        .insert(binding.id(), parameter_name.clone());
                                }
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
                            if let Some((observed_set, subset_proof)) = real_subset_observer {
                                if obj_equality_key(set) == obj_equality_key(observed_set) {
                                    install_real_subset_observation_for_parameter(
                                        binding.id(),
                                        &parameter_name,
                                        &hypothesis,
                                        set,
                                        subset_proof,
                                        &mut self.environment_stack,
                                    )?;
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
                    let premise_name = format!("__domain_f{}", fact_id.value());
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
                        && publication_selection.published_conclusions[0].1 == conclusion_fact_id
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
                            existing.0 == source.0 && existing.1.to_string() == source.1.to_string()
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
                    if let Some((observed_set, subset_proof)) = real_subset_observer {
                        render_forall_fact_type_with_real_subset_observer(
                            &publication_selection.forall_fact,
                            &self.environment_stack,
                            observed_set,
                            subset_proof,
                        )
                    } else {
                        render_fact(&projected_fact, &self.environment_stack)
                    }
                    .map_err(|error| {
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

    pub(in super::super) fn direct_forall_result_is_not_yet_supported(
        &self,
        reason: &str,
    ) -> Result<bool, String> {
        Err(format!(
            "direct ForallProof compiler rejected this Result because {reason}"
        ))
    }
}
