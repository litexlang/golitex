//! Litex theorem instantiation and proof construction.

use super::super::*;

struct TheoremApplicationParameterRendering {
    source_symbol_id: SymbolId,
    parameter_set: Obj,
    source_argument: Obj,
    target_value: String,
    target_membership_proof: String,
    native_integer_argument: Option<String>,
    application_value: String,
    application_membership_proof: Option<String>,
    application_to_target_same: Option<String>,
}

impl StmtResultToLeanCompiler {
    /// `Combine`: instantiate one previously compiled Litex theorem by its
    /// exact source FactId, combine the ordered argument-membership proofs,
    /// and publish each direct conclusion under the exact store FactId
    /// retained by this statement Result.
    pub(in super::super) fn compile_litex_theorem_instantiation_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessReleaseThmStmtResult,
    ) -> Result<bool, String> {
        let Some(conclusions) =
            self.construct_lean_proofs_from_litex_theorem_instantiation_stmt_result(result)?
        else {
            return Ok(false);
        };
        for conclusion in conclusions {
            let Some(fact_id) = conclusion.retained_fact_id else {
                continue;
            };
            let conclusion_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {conclusion_name} : {} := by\n  exact {}",
                conclusion.proposition, conclusion.proof_expression
            ));
            self.environment_stack
                .fact_names
                .insert(fact_id, conclusion_name);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, conclusion.fact);
            self.next_fact_name_index += 1;
        }
        Ok(true)
    }

    /// `Combine`: construct the exact ordered theorem conclusions without
    /// publishing them into the caller's compiler environment. The enclosing
    /// statement decides whether those Result-owned FactIds become visible or
    /// remain local to another proof layer.
    pub(in super::super) fn construct_lean_proofs_from_litex_theorem_instantiation_stmt_result(
        &mut self,
        result: &SuccessReleaseThmStmtResult,
    ) -> Result<Option<Vec<CompiledTheoremApplicationConclusionProofBody>>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        let SuccessVerifyTheoremApplicationSourceResult::Litex(source) = &verification.source
        else {
            return Ok(None);
        };
        if verification.theorem != result.statement.name().to_string()
            || verification.arguments.len() != result.statement.args().len()
            || verification
                .arguments
                .iter()
                .zip(result.statement.args().iter())
                .any(|(retained, source)| obj_equality_key(retained) != obj_equality_key(source))
        {
            return Err("release-thm Result changed its theorem name or argument order".into());
        }
        let source_fact_id = source
            .source_fact_id
            .ok_or_else(|| "release-thm Result has no source theorem FactId".to_string())?;
        let source_fact = self
            .environment_stack
            .fact_propositions
            .get(&source_fact_id)
            .cloned()
            .ok_or_else(|| {
                format!("release-thm cited unavailable source FactId `{source_fact_id}`")
            })?;
        match &source.mode {
            SuccessVerifyLitexTheoremApplicationMode::DirectFactCitation => {
                if !result.statement.call.is_bare()
                    || !verification.arguments.is_empty()
                    || verification.direct_conclusions.len() != 1
                    || verification.direct_conclusions[0].to_string() != source_fact.to_string()
                    || !result.common.infers.is_empty()
                {
                    return Err(
                        "direct theorem citation Result changed its source fact or effects".into(),
                    );
                }
                let theorem_name = self
                    .environment_stack
                    .fact_names
                    .get(&source_fact_id)
                    .cloned()
                    .ok_or_else(|| {
                        format!(
                            "direct theorem citation FactId `{source_fact_id}` has no Lean name"
                        )
                    })?;
                let proposition = render_fact(&source_fact, &self.environment_stack)?;
                return Ok(Some(vec![CompiledTheoremApplicationConclusionProofBody {
                    retained_fact_id: None,
                    fact: source_fact,
                    proposition,
                    proof_expression: theorem_name,
                }]));
            }
            SuccessVerifyLitexTheoremApplicationMode::ForallInstantiation { .. } => {
                if result.statement.call.is_bare() {
                    return Err("forall theorem instantiation lost its parenthesized call".into());
                }
            }
        }
        let Fact::ForallFact(source_forall) = &source_fact else {
            return Err("release-thm source FactId does not identify a forall fact".into());
        };
        let SuccessVerifyLitexTheoremApplicationMode::ForallInstantiation {
            argument_verification,
            domain_facts,
            domain_checks,
        } = &source.mode
        else {
            unreachable!("direct theorem citation returned above")
        };
        let source_parameters = source_forall
            .typed_parameters
            .collect_param_bindings_with_types();
        if source_parameters.iter().any(|(_, parameter_type)| {
            !matches!(parameter_type, ParamType::Obj(Obj::StandardSet(_)))
        }) {
            return Ok(None);
        }
        if source_parameters.len() != result.statement.args().len()
            || source_forall.dom_facts.len() != domain_facts.len()
            || domain_facts.len() != domain_checks.len()
            || source_forall.then_facts.len() != verification.direct_conclusions.len()
            || verification.direct_conclusions.is_empty()
        {
            return Err("release-thm Result changed its source theorem arity".into());
        }
        let source_substitutions = source_parameters
            .iter()
            .zip(result.statement.args().iter())
            .map(|((binding, _), argument)| (binding.id().substitution_key(), argument.clone()))
            .collect::<HashMap<_, _>>();
        let Some(argument_verification) = argument_verification else {
            return Err("release-thm Result has no argument verification children".into());
        };
        if !argument_verification.infers.is_empty()
            || argument_verification.checks.len() != source_parameters.len()
        {
            return Ok(None);
        }

        if result
            .common
            .infers
            .store_fact_outputs
            .iter()
            .any(|output| !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty())
            || !result.common.infers.rule_applications.is_empty()
        {
            return Ok(None);
        }
        if result.common.infers.store_fact_outputs.len() != verification.direct_conclusions.len() {
            return Err("release-thm Result changed its direct conclusion store count".into());
        }
        let conclusion_fact_ids = result
            .common
            .infers
            .store_fact_outputs
            .iter()
            .zip(verification.direct_conclusions.iter())
            .map(|(stored, expected)| {
                if stored.itself_and_why_itself_is_stored.0.to_string() != expected.to_string() {
                    return Err(
                        "release-thm Result changed a direct conclusion store proposition".into(),
                    );
                }
                Ok(stored.fact_id)
            })
            .collect::<Result<Vec<_>, String>>()?;

        let theorem_name = self
            .environment_stack
            .fact_names
            .get(&source_fact_id)
            .cloned()
            .ok_or_else(|| {
                format!("release-thm source FactId `{source_fact_id}` has no Lean name")
            })?;
        let mut application_parts = vec![theorem_name];
        let mut source_parameter_rendering_aliases = Vec::with_capacity(source_parameters.len());
        for (parameter_index, (((_, parameter_type), argument), check)) in source_parameters
            .iter()
            .zip(result.statement.args().iter())
            .zip(argument_verification.checks.iter())
            .enumerate()
        {
            let parameter_set = parameter_set(parameter_type)
                .map_err(|error| format!("release-thm parameter {parameter_index}: {error}"))?;
            let native_integer_parameter =
                matches!(parameter_set, Obj::StandardSet(StandardSet::Z));
            let rendered_argument = render_obj(argument, &self.environment_stack)?;
            let expected_parameter_fact = format!(
                "Litex.In {rendered_argument} {}",
                render_obj(parameter_set, &self.environment_stack)?
            );
            let factual_check = check.verified().ok_or_else(|| {
                format!("release-thm argument check {parameter_index} is not factual")
            })?;
            if render_fact(&factual_check.fact(), &self.environment_stack)?
                != expected_parameter_fact
            {
                return Err(format!(
                    "release-thm argument check {parameter_index} changed its parameter obligation"
                ));
            }
            let Some(parameter_proof) =
                self.construct_lean_proof_from_direct_fact_result(factual_check)?
            else {
                return Ok(None);
            };
            let native_integer_argument = if native_integer_parameter {
                Some(render_integer_obj(argument, &self.environment_stack)?)
            } else {
                None
            };
            let exact_object_parameter = forall_parameter_uses_exact_object_carrier(parameter_set);
            let (application_value, application_membership_proof, application_to_target_same) =
                if native_integer_parameter {
                    (
                        native_integer_argument
                            .clone()
                            .expect("native integer argument was constructed above"),
                        None,
                        None,
                    )
                } else if exact_object_parameter {
                    let exact_argument = render_exact_predicate_argument(
                        argument,
                        parameter_set,
                        &self.environment_stack,
                    )?;
                    let rendered_set = render_obj(parameter_set, &self.environment_stack)?;
                    let exact_membership = format!("Litex.In.own {rendered_set} {exact_argument}");
                    let exact_to_source = render_exact_predicate_argument_same_to_source(
                        argument,
                        parameter_set,
                        &self.environment_stack,
                    )?;
                    (
                        exact_argument,
                        Some(exact_membership),
                        Some(exact_to_source),
                    )
                } else {
                    (
                        rendered_argument.clone(),
                        Some(parameter_proof.clone()),
                        None,
                    )
                };
            application_parts.push(application_value.clone());
            if let Some(application_membership_proof) = &application_membership_proof {
                application_parts.push(format!("({application_membership_proof})"));
            }
            source_parameter_rendering_aliases.push(TheoremApplicationParameterRendering {
                source_symbol_id: source_parameters[parameter_index].0.id(),
                parameter_set: parameter_set.clone(),
                source_argument: argument.clone(),
                target_value: rendered_argument,
                target_membership_proof: parameter_proof,
                native_integer_argument,
                application_value,
                application_membership_proof,
                application_to_target_same,
            });
        }
        let mut instantiator = Runtime::default();
        // Capture-avoiding substitution for existential conclusions consults
        // the Runtime's visible-definition frame even though compilation does
        // not execute or search for any proof. Give this isolated structural
        // instantiator the same mandatory empty frame as an ordinary source.
        instantiator.start_isolated_source("stmt-result-to-lean release-thm projection");
        for (domain_index, ((source_domain, retained_domain), check)) in source_forall
            .dom_facts
            .iter()
            .zip(domain_facts.iter())
            .zip(domain_checks.iter())
            .enumerate()
        {
            let expected_domain = instantiator
                .inst_fact(
                    source_domain,
                    &source_substitutions,
                    SubstitutionMode::Named,
                    None,
                )
                .map_err(|error| {
                    format!(
                        "release-thm could not instantiate domain {domain_index}: {}",
                        error.trace_message()
                    )
                })?;
            if expected_domain.to_string() != retained_domain.to_string() {
                return Err(format!(
                    "release-thm domain {domain_index} changed under exact parameter substitution"
                ));
            }
            let factual_check = check
                .verified()
                .ok_or_else(|| format!("release-thm domain check {domain_index} is not factual"))?;
            if factual_check.fact().to_string() != retained_domain.to_string() {
                return Err(format!(
                    "release-thm domain check {domain_index} changed its retained obligation"
                ));
            }
            let Some(domain_proof) =
                self.construct_lean_proof_from_direct_fact_result(factual_check)?
            else {
                return Ok(None);
            };
            application_parts.push(format!("({domain_proof})"));
        }
        let theorem_application = format!("({})", application_parts.join(" "));

        let mut conclusion_rendering_context = self.environment_stack.clone();
        for parameter in &source_parameter_rendering_aliases {
            conclusion_rendering_context
                .symbol_names
                .insert(parameter.source_symbol_id, parameter.target_value.clone());
            if let Ok(real) =
                render_real_source_object(&parameter.source_argument, &self.environment_stack)
            {
                conclusion_rendering_context
                    .numeric_real_values
                    .insert(parameter.source_symbol_id, real);
            }
            if let Ok(integer) =
                render_integer_obj(&parameter.source_argument, &self.environment_stack)
            {
                conclusion_rendering_context
                    .numeric_integer_values
                    .insert(parameter.source_symbol_id, integer);
            }
            if let Ok(rational) =
                render_rational_obj(&parameter.source_argument, &self.environment_stack)
            {
                conclusion_rendering_context
                    .numeric_rational_values
                    .insert(parameter.source_symbol_id, rational);
            }
            if let Ok(numeric) =
                render_numeric_obj(&parameter.source_argument, &self.environment_stack)
            {
                conclusion_rendering_context
                    .numeric_representations
                    .insert(parameter.source_symbol_id, numeric);
            }
            if let Some(native_integer_argument) = &parameter.native_integer_argument {
                install_structured_induction_native_integer_symbol(
                    parameter.source_symbol_id,
                    native_integer_argument,
                    &mut conclusion_rendering_context,
                );
            }
        }
        if let Some(mut theorem_well_definedness) = self
            .environment_stack
            .fact_well_definedness
            .get(&source_fact_id)
            .cloned()
        {
            for alias in &theorem_well_definedness.parameter_fact_aliases {
                let Some(parameter) = source_parameter_rendering_aliases
                    .iter()
                    .find(|parameter| parameter.source_symbol_id == alias.symbol_id)
                else {
                    // The theorem WD tree also owns aliases for binders local
                    // to a projected conclusion (for example an existential
                    // witness). They are not theorem arguments and must stay
                    // under that conclusion's binder rather than being
                    // rebound to an application argument here.
                    continue;
                };
                conclusion_rendering_context
                    .fact_names
                    .insert(alias.fact_id, parameter.target_membership_proof.clone());
                conclusion_rendering_context
                    .fact_propositions
                    .insert(alias.fact_id, alias.proposition.clone());
            }
            let projected_applications =
                std::mem::take(&mut theorem_well_definedness.function_applications);
            for (_, mut application) in projected_applications {
                application.source_application = instantiator
                    .inst_obj(
                        &application.source_application,
                        &source_substitutions,
                        SubstitutionMode::ResultProjection,
                    )
                    .map_err(|error| {
                        format!(
                            "release-thm could not specialize a WD application: {}",
                            error.trace_message()
                        )
                    })?;
                if let Some(head) = &application.anonymous_function_head {
                    application.anonymous_function_head = Some(
                        instantiator
                            .inst_obj(
                                head,
                                &source_substitutions,
                                SubstitutionMode::ResultProjection,
                            )
                            .map_err(|error| {
                                format!(
                                    "release-thm could not specialize an anonymous application head: {}",
                                    error.trace_message()
                                )
                            })?,
                    );
                }
                for layer in &mut application.layers {
                    layer.source_prefix = instantiator
                        .inst_obj(
                            &layer.source_prefix,
                            &source_substitutions,
                            SubstitutionMode::ResultProjection,
                        )
                        .map_err(|error| {
                            format!(
                                "release-thm could not specialize an application prefix: {}",
                                error.trace_message()
                            )
                        })?;
                    if let Some(result_set) = &layer.intrinsic_result_set {
                        layer.intrinsic_result_set = Some(
                            instantiator
                                .inst_obj(
                                    result_set,
                                    &source_substitutions,
                                    SubstitutionMode::ResultProjection,
                                )
                                .map_err(|error| {
                                    format!(
                                        "release-thm could not specialize an application return set: {}",
                                        error.trace_message()
                                    )
                                })?,
                        );
                    }
                    for requirement in &mut layer.requirements {
                        requirement.expected_proposition = instantiator
                            .inst_fact(
                                &requirement.expected_proposition,
                                &source_substitutions,
                                SubstitutionMode::ResultProjection,
                                None,
                            )
                            .map_err(|error| {
                                format!(
                                    "release-thm could not specialize an application WD requirement: {}",
                                    error.trace_message()
                                )
                            })?;
                    }
                }
                let object_key = obj_equality_key(&application.source_application);
                if theorem_well_definedness
                    .function_applications
                    .insert(object_key.clone(), application)
                    .is_some()
                {
                    return Err(format!(
                        "release-thm projected two WD applications to `{object_key}`"
                    ));
                }
            }
            let projected_iterations = std::mem::take(&mut theorem_well_definedness.iterations);
            for (_, mut iteration) in projected_iterations {
                iteration.source_aggregate = instantiator
                    .inst_obj(
                        &iteration.source_aggregate,
                        &source_substitutions,
                        SubstitutionMode::ResultProjection,
                    )
                    .map_err(|error| {
                        format!(
                            "release-thm could not specialize an Iteration WD owner: {}",
                            error.trace_message()
                        )
                    })?;
                iteration.parameter_set = instantiator
                    .inst_obj(
                        &iteration.parameter_set,
                        &source_substitutions,
                        SubstitutionMode::ResultProjection,
                    )
                    .map_err(|error| error.trace_message())?;
                iteration.return_carrier = instantiator
                    .inst_obj(
                        &iteration.return_carrier,
                        &source_substitutions,
                        SubstitutionMode::ResultProjection,
                    )
                    .map_err(|error| error.trace_message())?;
                let object_key = obj_equality_key(&iteration.source_aggregate);
                if theorem_well_definedness
                    .iterations
                    .insert(object_key.clone(), iteration)
                    .is_some()
                {
                    return Err(format!(
                        "release-thm projected two Iteration WD owners to `{object_key}`"
                    ));
                }
            }
            conclusion_rendering_context.well_definedness = Some(theorem_well_definedness);
        }

        let mut theorem_conclusion_context = conclusion_rendering_context.clone();
        let mut application_to_target_bridges = Vec::new();
        for parameter in &source_parameter_rendering_aliases {
            theorem_conclusion_context.symbol_names.insert(
                parameter.source_symbol_id,
                parameter.application_value.clone(),
            );
            theorem_conclusion_context
                .exact_carrier_values
                .remove(&parameter.source_symbol_id);
            theorem_conclusion_context
                .numeric_real_values
                .remove(&parameter.source_symbol_id);
            theorem_conclusion_context
                .numeric_integer_values
                .remove(&parameter.source_symbol_id);
            theorem_conclusion_context
                .numeric_rational_values
                .remove(&parameter.source_symbol_id);
            theorem_conclusion_context
                .numeric_representations
                .remove(&parameter.source_symbol_id);
            theorem_conclusion_context
                .numeric_representation_equalities
                .remove(&parameter.source_symbol_id);
            theorem_conclusion_context
                .numeric_representation_memberships
                .remove(&parameter.source_symbol_id);
            if let Some(application_membership_proof) = &parameter.application_membership_proof {
                if parameter.application_to_target_same.is_some() {
                    install_exact_predicate_carrier_value(
                        parameter.source_symbol_id,
                        &parameter.parameter_set,
                        &parameter.application_value,
                        &mut theorem_conclusion_context,
                    )?;
                } else {
                    let lowered_set =
                        LeanTargetObjectRepresentation::lower(&parameter.parameter_set)?;
                    install_numeric_representations_from_membership(
                        parameter.source_symbol_id,
                        &lowered_set,
                        &parameter.application_value,
                        application_membership_proof,
                        &mut theorem_conclusion_context,
                    );
                }
            }
            if let Some(bridge) = &parameter.application_to_target_same {
                application_to_target_bridges.push((parameter.source_symbol_id, bridge.clone()));
            }
            if let Some(well_definedness) = &theorem_conclusion_context.well_definedness {
                let aliases = well_definedness
                    .parameter_fact_aliases
                    .iter()
                    .filter(|alias| alias.symbol_id == parameter.source_symbol_id)
                    .map(|alias| alias.fact_id)
                    .collect::<Vec<_>>();
                for fact_id in aliases {
                    if let Some(application_membership_proof) =
                        &parameter.application_membership_proof
                    {
                        theorem_conclusion_context
                            .fact_names
                            .insert(fact_id, application_membership_proof.clone());
                    }
                }
            }
        }

        let mut conclusions = Vec::with_capacity(verification.direct_conclusions.len());
        for (conclusion_index, (conclusion, fact_id)) in verification
            .direct_conclusions
            .iter()
            .zip(conclusion_fact_ids.iter())
            .enumerate()
        {
            let projected_proof = conjunction_projection(
                &theorem_application,
                conclusion_index,
                verification.direct_conclusions.len(),
            )?;
            let direct_proof = format!(
                "(by\n  have __projected_conclusion := {projected_proof}\n  try rw [Litex.In.rep_exact] at __projected_conclusion\n  exact __projected_conclusion)"
            );
            let source_conclusion = source_forall.then_facts[conclusion_index].clone().to_fact();
            let projected_conclusion = instantiator
                .inst_fact(
                    &source_conclusion,
                    &source_substitutions,
                    SubstitutionMode::ResultProjection,
                    None,
                )
                .map_err(|error| {
                    format!(
                        "release-thm could not project conclusion {conclusion_index} WD provenance: {}",
                        error.trace_message()
                    )
                })?;
            if projected_conclusion.to_string() != conclusion.to_string() {
                return Err(format!(
                    "release-thm projected conclusion {conclusion_index} changed its proposition"
                ));
            }
            let proposition = render_fact(&projected_conclusion, &conclusion_rendering_context)?;
            let theorem_target = render_fact(&source_conclusion, &theorem_conclusion_context)?;
            let projected_through_source_parameters =
                render_fact(&source_conclusion, &conclusion_rendering_context)?;
            if projected_through_source_parameters != proposition {
                return Err(format!(
                    "release-thm conclusion {conclusion_index} target aliases changed `{proposition}` to `{projected_through_source_parameters}`"
                ));
            }
            let proof = if theorem_target == proposition {
                direct_proof
            } else {
                render_fact_proof_across_exact_predicate_arguments_with_source_bridges(
                    &source_conclusion,
                    &source_conclusion,
                    &theorem_conclusion_context,
                    &conclusion_rendering_context,
                    &direct_proof,
                    &application_to_target_bridges,
                )?
            };
            conclusions.push(CompiledTheoremApplicationConclusionProofBody {
                retained_fact_id: *fact_id,
                fact: conclusion.clone(),
                proposition,
                proof_expression: proof,
            });
        }
        Ok(Some(conclusions))
    }
}
