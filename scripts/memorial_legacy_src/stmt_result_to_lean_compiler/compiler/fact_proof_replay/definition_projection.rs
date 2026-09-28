//! Definition projection replay.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: unfold the exact active concrete predicate proof retained as
    /// the sole child, then select the existential definition clause matching
    /// this Result's target. No Runtime lookup or label reconstruction occurs.
    pub(in super::super) fn construct_lean_definition_projection_from_result(
        &mut self,
        target: &Fact,
        evidence: &DefinitionProjectionBuiltinRuleEvidence,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        let Fact::ExistFact(target_existential) = target else {
            return Err("definition projection requires an existential target".into());
        };
        if !target_existential.is_plain_exist() {
            return Ok(None);
        }
        let [source_result] = subgoals else {
            return Err(
                "definition projection must retain exactly one predicate source Result".into(),
            );
        };
        let source_result = source_result
            .verified()
            .ok_or_else(|| "definition projection source child is not factual".to_string())?;
        let source_fact: Fact = evidence.fact.clone().into();
        if source_result.fact().to_string() != source_fact.to_string() {
            return Err("definition projection changed its predicate source child".into());
        }

        let definition_name = evidence.definition.name.clone();
        if evidence.fact.predicate.to_string() != definition_name {
            return Err("definition projection evidence names a different predicate".into());
        }
        let binding = self
            .environment_stack
            .predicate_bindings
            .get(&definition_name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "definition projection references unavailable predicate `{definition_name}`"
                )
            })?;
        let Some(active_definition) = &binding.definition else {
            return Err("definition projection selected an abstract predicate".into());
        };
        if active_definition.to_string() != evidence.definition.to_string() {
            return Err(
                "definition projection does not match the active predicate definition".into(),
            );
        }

        let Some(source_proof) =
            self.construct_lean_proof_from_direct_fact_result(source_result)?
        else {
            return Ok(None);
        };
        let components =
            instantiated_predicate_components(&source_fact, &binding, &self.environment_stack)?;
        let rendered_target = render_fact(target, &self.environment_stack)?;
        if let Some(clause_index) = components
            .iter()
            .position(|component| component == &rendered_target)
        {
            let selector = conjunction_selector(clause_index, components.len())?;
            let selected_component = format!("__definition{selector}");
            let finish = if let Fact::ForallFact(forall) = target {
                render_eta_expanded_forall_projection(forall, &selected_component)?
            } else {
                format!(
                    "simpa [Litex.fnApply, Litex.fnApplyOwn, Litex.abs, Complex.ext_iff, Real.norm_eq_abs] using {selected_component}"
                )
            };
            return Ok(Some(format!(
                "(by\n  have __definition := {source_proof}\n  unfold {} at __definition\n  {finish})",
                binding.lean_name,
            )));
        }

        // Exact numeric predicate parameters change only the Lean carrier of
        // an instantiated definition clause, not its Litex value. For the
        // verifier's one-witness existential projection, transport the
        // equality body across the same checked representation bridge used at
        // the predicate call instead of pretending the two Lean propositions
        // are definitionally identical.
        let definition_clause = active_definition
            .iff_facts
            .first()
            .ok_or_else(|| "definition projection retained no definition clause".to_string())?;
        let Fact::ExistFact(definition_existential) = definition_clause else {
            return Err(format!(
                "definition projection target `{rendered_target}` is not an instantiated definition component; available: {}",
                components.join(" | ")
            ));
        };
        let definition_group = one_witness_existential_group(definition_existential)?;
        let target_group = one_witness_existential_group(target_existential)?;
        let definition_body = definition_existential.facts()[0].from_ref_to_cloned_fact();
        let target_body = target_existential.facts()[0].from_ref_to_cloned_fact();
        let definition_witness = definition_group.params[0].id();
        let target_witness = target_group.params[0].id();
        let parameters = active_definition
            .typed_parameters
            .collect_param_bindings_with_types();
        if !matches!(definition_body, Fact::AtomicFact(AtomicFact::EqualFact(_))) {
            if active_definition.iff_facts.len() != 1
                || components.len() != binding.requirement_count + 1
                || !binding.exact_parameters.iter().any(|exact| *exact)
            {
                return Err(format!(
                    "definition projection target `{rendered_target}` is not an instantiated definition component; available: {}",
                    components.join(" | ")
                ));
            }
            let substitutions = active_definition
                .typed_parameters
                .param_defs_and_args_to_param_to_arg_map(evidence.fact.body.as_slice());
            let instantiator = Runtime::default();
            let instantiated_clause = instantiator
                .inst_fact(
                    definition_clause,
                    &substitutions,
                    SubstitutionMode::ResultProjection,
                    None,
                )
                .map_err(|error| {
                    format!(
                        "definition projection could not replay its retained clause substitution: {}",
                        error.trace_message()
                    )
                })?;
            if !one_witness_existentials_are_alpha_equal(
                &instantiated_clause,
                target,
                &self.environment_stack,
            )? {
                return Err(
                    "predicate-bodied definition projection changed its instantiated existential"
                        .into(),
                );
            }
            let selector = conjunction_selector(binding.requirement_count, components.len())?;
            return Ok(Some(format!(
                "(by\n  have __definition := {source_proof}\n  unfold {} at __definition\n  simpa [Litex.In.rep, Litex.Rules.complexRealInR, Litex.Rules.complexAddInR, Litex.Rules.complexSubInR, Litex.Rules.complexMulInR, Litex.Rules.complexDivInR, Litex.Rules.inROfInRPos, Litex.Le, Litex.Lt, Litex.OrderValue] using (__definition{selector}))",
                binding.lean_name,
            )));
        }
        let (definition_left, definition_right) = equality_parts(&definition_body)?;
        let (target_left, target_right) = equality_parts(&target_body)?;
        let orientation = if object_is_symbol(definition_left, definition_witness)
            && object_is_symbol(target_left, target_witness)
        {
            Some((definition_right, target_right, true))
        } else if object_is_symbol(definition_right, definition_witness)
            && object_is_symbol(target_right, target_witness)
        {
            Some((definition_left, target_left, false))
        } else {
            None
        };
        let Some((definition_parameter_object, target_argument, witness_on_left)) = orientation
        else {
            return Err(format!(
                "definition projection target `{rendered_target}` is not an instantiated definition component; available: {}",
                components.join(" | ")
            ));
        };
        let parameter_index = parameters
            .iter()
            .position(|(parameter, _)| {
                object_is_symbol(definition_parameter_object, parameter.id())
            })
            .ok_or_else(|| {
                "definition projection equality does not reference a predicate parameter"
                    .to_string()
            })?;
        let source_argument = evidence
            .fact
            .body
            .get(parameter_index)
            .ok_or_else(|| "definition projection lost its source argument".to_string())?;
        if obj_equality_key(target_argument) != obj_equality_key(source_argument)
            || binding.exact_parameters.get(parameter_index) != Some(&true)
        {
            return Err("definition projection changed its exact source argument".into());
        }
        let ParamType::Obj(parameter_set) = &parameters[parameter_index].1 else {
            return Err("definition projection exact parameter is not an object".into());
        };
        let exact_to_source = render_exact_predicate_argument_same_to_source(
            source_argument,
            parameter_set,
            &self.environment_stack,
        )?;
        let clause_index = binding.requirement_count;
        if active_definition.iff_facts.len() != 1
            || components.len() != binding.requirement_count + 1
        {
            return Err(
                "definition projection representation transport requires one definition clause"
                    .into(),
            );
        }
        let selector = conjunction_selector(clause_index, components.len())?;
        let transported_body = if witness_on_left {
            format!("Litex.Same.trans __body ({exact_to_source})")
        } else {
            format!("Litex.Same.trans (Litex.Same.symm ({exact_to_source})) __body")
        };
        Ok(Some(format!(
            "(by\n  have __definition := {source_proof}\n  unfold {} at __definition\n  rcases __definition{selector} with ⟨__witness, __membership, __body⟩\n  exact ⟨__witness, __membership, {transported_body}⟩)",
            binding.lean_name
        )))
    }
}
