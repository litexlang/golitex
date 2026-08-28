//! Known universal fact instantiation.

use super::super::*;
use super::result_alignment::facts_align_by_anonymous_function_beta_normalization_for_result_compiler;

impl StmtResultToLeanCompiler {
    /// `Combine`: resolve the retained source forall by its exact FactId,
    /// compile each parameter/domain requirement from its recursive Result,
    /// and apply the already-emitted Lean theorem. The fresh Runtime below is
    /// used only as the kernel's stateless syntax-substitution utility; it has
    /// no executed environment and cannot rediscover a proof or FactId.
    pub(in super::super) fn construct_lean_known_forall_instantiation_from_result(
        &mut self,
        target: &Fact,
        result: &SuccessInstantiateKnownForallResult,
    ) -> Result<Option<String>, String> {
        let source_fact = &result.source_fact;
        let Fact::ForallFact(source_forall) = source_fact else {
            return Err("known-forall Result cited a non-forall fact".into());
        };
        let source_fact_id = result.source_fact_id;
        let source_theorem =
            resolve_fact_citation(&source_fact_id, source_fact, &self.environment_stack)?;
        let source_parameters = source_forall
            .typed_parameters
            .collect_param_bindings_with_types();
        if source_parameters.len() != result.instantiation.len() {
            return Err("known-forall Result changed its argument arity".into());
        }
        if result.requirements.len() != source_parameters.len() + source_forall.dom_facts.len() {
            return Err(
                "known-forall Result changed its parameter/domain requirement arity".into(),
            );
        }

        let arguments = result
            .instantiation
            .iter()
            .zip(source_parameters.iter())
            .map(|(item, (binding, _))| {
                if item.param != binding.name() || item.arg != item.arg_obj.to_string() {
                    return Err(
                        "known-forall Result changed its retained parameter order or argument"
                            .to_string(),
                    );
                }
                Ok(item.arg_obj.clone())
            })
            .collect::<Result<Vec<_>, String>>()?;
        let substitutions = source_forall
            .typed_parameters
            .param_defs_and_args_to_param_to_arg_map(&arguments);
        let mut substitution_runtime = Runtime::default();
        substitution_runtime.ensure_execution_frame_for_parse();

        let mut application_terms = vec![source_theorem];
        let mut source_application_context = self.environment_stack.clone();
        let mut uses_exact_refined_numeric_parameter = false;
        for (parameter_index, (((_, parameter_type), argument), requirement)) in source_parameters
            .iter()
            .zip(arguments.iter())
            .zip(result.requirements.iter().take(source_parameters.len()))
            .enumerate()
        {
            if requirement.kind != KnownForallRequirementKind::ParameterType {
                return Err(format!(
                    "known-forall parameter requirement {parameter_index} changed its kind"
                ));
            }
            let requirement_result = requirement.result.factual_success().ok_or_else(|| {
                format!("known-forall parameter requirement {parameter_index} is not factual")
            })?;
            if requirement_result.fact().to_string() != requirement.stmt.to_string() {
                return Err(format!(
                    "known-forall parameter requirement {parameter_index} changed its fact"
                ));
            }
            validate_scoped_fact_check_result(
                requirement_result,
                &requirement.stmt,
                &format!("known-forall parameter requirement {parameter_index}"),
            )?;

            let native_integer_parameter = matches!(
                parameter_type,
                ParamType::Obj(Obj::StandardSet(StandardSet::Z))
            );
            let exact_refined_numeric_parameter = matches!(
                parameter_type,
                ParamType::Obj(set) if forall_parameter_uses_exact_refined_numeric_carrier(set)
            );
            uses_exact_refined_numeric_parameter |= exact_refined_numeric_parameter;
            let rendered_application_argument = if native_integer_parameter {
                render_integer_obj(argument, &self.environment_stack)?
            } else {
                render_obj(argument, &self.environment_stack)?
            };
            source_application_context.symbol_names.insert(
                source_parameters[parameter_index].0.id(),
                rendered_application_argument.clone(),
            );
            if !exact_refined_numeric_parameter {
                application_terms.push(rendered_application_argument.clone());
            }
            let requirement_needs_proof = match parameter_type {
                ParamType::Set(_) => {
                    let Fact::AtomicFact(AtomicFact::IsSetFact(sethood)) = &requirement.stmt else {
                        return Err(
                            "known-forall set argument retained a non-set requirement".into()
                        );
                    };
                    if obj_equality_key(&sethood.set) != obj_equality_key(argument) {
                        return Err("known-forall set requirement changed its argument".into());
                    }
                    false
                }
                ParamType::Obj(source_set) => {
                    let instantiated_set = substitution_runtime
                        .inst_obj(source_set, &substitutions, SubstitutionMode::Exact)
                        .map_err(|error| {
                            format!("known-forall parameter substitution failed: {error:?}")
                        })?;
                    let (requirement_argument, requirement_set) =
                        membership_parts(&requirement.stmt)?;
                    if obj_equality_key(requirement_argument) != obj_equality_key(argument)
                        || obj_equality_key(requirement_set) != obj_equality_key(&instantiated_set)
                    {
                        return Err(
                            "known-forall object requirement changed its argument or carrier"
                                .into(),
                        );
                    }
                    !native_integer_parameter
                }
                ParamType::NonemptySet(_) => {
                    let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(property)) =
                        &requirement.stmt
                    else {
                        return Err(
                            "known-forall nonempty-set argument retained different evidence".into(),
                        );
                    };
                    if obj_equality_key(&property.set) != obj_equality_key(argument) {
                        return Err(
                            "known-forall nonempty-set requirement changed its argument".into()
                        );
                    }
                    true
                }
                ParamType::FiniteSet(_) => {
                    let Fact::AtomicFact(AtomicFact::IsFiniteSetFact(property)) = &requirement.stmt
                    else {
                        return Err(
                            "known-forall finite-set argument retained different evidence".into(),
                        );
                    };
                    if obj_equality_key(&property.set) != obj_equality_key(argument) {
                        return Err(
                            "known-forall finite-set requirement changed its argument".into()
                        );
                    }
                    true
                }
            };
            if requirement_needs_proof {
                let Some(mut proof) =
                    self.construct_lean_proof_from_direct_fact_result(requirement_result)?
                else {
                    return Ok(None);
                };
                if let (Some(fact_id), ParamType::Obj(set)) =
                    (requirement_result.store.fact_id, parameter_type)
                {
                    let expected_proposition =
                        render_fact(&requirement.stmt, &self.environment_stack)?;
                    if let Some(actual_proposition) = self
                        .environment_stack
                        .fact_lean_propositions
                        .get(&fact_id)
                        .filter(|actual| *actual != &expected_proposition)
                    {
                        let exact_argument = render_exact_predicate_argument(
                            argument,
                            set,
                            &self.environment_stack,
                        )?;
                        let rendered_set = render_obj(set, &self.environment_stack)?;
                        let exact_proposition = format!("Litex.In {exact_argument} {rendered_set}");
                        if actual_proposition != &exact_proposition {
                            return Err(format!(
                                "known-forall parameter proof `{fact_id}` has unrelated Lean proposition `{actual_proposition}`; expected `{expected_proposition}` or `{exact_proposition}`"
                            ));
                        }
                        let exact_to_source = render_exact_predicate_argument_same_to_source(
                            argument,
                            set,
                            &self.environment_stack,
                        )?;
                        proof = format!(
                            "(Litex.In.congr ({exact_to_source}) {rendered_set}).mp ({proof})"
                        );
                    }
                }
                if exact_refined_numeric_parameter {
                    let ParamType::Obj(set) = parameter_type else {
                        unreachable!("exact refined numeric parameter is an object")
                    };
                    let lowered_argument = LeanTargetObjectRepresentation::lower(argument)?;
                    let exact_real = render_real_target_object_representation(
                        &lowered_argument,
                        &self.environment_stack,
                    )?;
                    let mut positive_carriers = self
                        .environment_stack
                        .exact_positive_real_carriers
                        .values()
                        .cloned()
                        .collect::<Vec<_>>();
                    positive_carriers.sort();
                    positive_carriers.dedup();
                    let positivity_premises = positive_carriers
                        .iter()
                        .enumerate()
                        .map(|(index, carrier)| {
                            format!(
                                "have __exact_positive{index} : 0 < (({carrier}).val : ℝ) := ({carrier}).property"
                            )
                        })
                        .collect::<Vec<_>>();
                    let positivity_proof = if let LeanTargetObjectRepresentation::BuiltinApp {
                        operator: LeanTargetBuiltinObjectOperator::Div,
                        arguments,
                        ..
                    } = &lowered_argument
                    {
                        let numerator = render_real_target_object_representation(
                            &arguments[0],
                            &self.environment_stack,
                        )?;
                        let numerator_carrier = self
                            .environment_stack
                            .exact_positive_real_carriers
                            .iter()
                            .filter_map(|(symbol_id, carrier)| {
                                (self.environment_stack.numeric_real_values.get(symbol_id)
                                    == Some(&numerator))
                                .then_some(carrier.clone())
                            })
                            .min();
                        if let Some(numerator_carrier) = numerator_carrier {
                            format!(
                                "by\n  exact div_pos ({numerator_carrier}).property (by positivity)"
                            )
                        } else if positivity_premises.is_empty() {
                            "by positivity".to_string()
                        } else {
                            format!("by\n  {}\n  positivity", positivity_premises.join("\n  "))
                        }
                    } else if positivity_premises.is_empty() {
                        "by positivity".to_string()
                    } else {
                        format!("by\n  {}\n  positivity", positivity_premises.join("\n  "))
                    };
                    let exact_argument = match &lowered_argument {
                        LeanTargetObjectRepresentation::Symbol { symbol_id, .. } => self
                            .environment_stack
                            .exact_positive_real_carriers
                            .get(symbol_id)
                            .cloned()
                            .unwrap_or_else(|| {
                                format!("(⟨{exact_real}, {positivity_proof}⟩ : Litex.RPos.Carrier)")
                            }),
                        _ => format!("(⟨{exact_real}, {positivity_proof}⟩ : Litex.RPos.Carrier)"),
                    };
                    application_terms.push(exact_argument.clone());
                    application_terms.push(format!(
                        "(Litex.In.own {} {exact_argument})",
                        render_obj(set, &self.environment_stack)?
                    ));
                    source_application_context.symbol_names.insert(
                        source_parameters[parameter_index].0.id(),
                        exact_argument.clone(),
                    );
                    install_exact_predicate_carrier_value(
                        source_parameters[parameter_index].0.id(),
                        set,
                        &exact_argument,
                        &mut source_application_context,
                    )?;
                } else {
                    application_terms.push(format!("({proof})"));
                    if let ParamType::Obj(set) = parameter_type {
                        let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
                        let selected = if native_integer_parameter
                            || matches!(
                                lowered_set,
                                LeanTargetObjectRepresentation::StandardSet(
                                    LeanTargetStandardSet::Complex
                                )
                            ) {
                            rendered_application_argument.clone()
                        } else {
                            format!("(Litex.In.rep {rendered_application_argument} ({proof}))")
                        };
                        install_exact_predicate_carrier_value(
                            source_parameters[parameter_index].0.id(),
                            set,
                            &selected,
                            &mut source_application_context,
                        )?;
                        install_numeric_representations_from_membership(
                            source_parameters[parameter_index].0.id(),
                            &lowered_set,
                            &rendered_application_argument,
                            &format!("({proof})"),
                            &mut source_application_context,
                        );
                        if let (Some(numeric), Some(selected_to_numeric)) = (
                            exact_set_numeric_value(&lowered_set, &selected),
                            exact_set_numeric_equality(&lowered_set, &selected),
                        ) {
                            source_application_context
                                .numeric_representations
                                .insert(source_parameters[parameter_index].0.id(), numeric);
                            source_application_context
                                .numeric_representation_equalities
                                .insert(
                                    source_parameters[parameter_index].0.id(),
                                    format!(
                                        "Litex.Same.trans (Litex.In.same_rep {rendered_application_argument} ({proof})) ({selected_to_numeric})"
                                    ),
                                );
                        }
                    }
                }
            } else if let ParamType::Obj(set) = parameter_type {
                install_exact_predicate_carrier_value(
                    source_parameters[parameter_index].0.id(),
                    set,
                    &rendered_application_argument,
                    &mut source_application_context,
                )?;
            }
        }

        for (domain_index, (source_domain, requirement)) in source_forall
            .dom_facts
            .iter()
            .zip(result.requirements.iter().skip(source_parameters.len()))
            .enumerate()
        {
            if requirement.kind != KnownForallRequirementKind::Domain {
                return Err(format!(
                    "known-forall domain requirement {domain_index} changed its kind"
                ));
            }
            let expected_domain = substitution_runtime
                .inst_fact(source_domain, &substitutions, SubstitutionMode::Exact, None)
                .map_err(|error| format!("known-forall domain substitution failed: {error:?}"))?;
            let requirement_result = requirement.result.factual_success().ok_or_else(|| {
                format!("known-forall domain requirement {domain_index} is not factual")
            })?;
            if requirement.stmt.to_string() != expected_domain.to_string()
                || requirement_result.fact().to_string() != expected_domain.to_string()
            {
                return Err(format!(
                    "known-forall domain requirement {domain_index} changed its instantiated fact"
                ));
            }
            validate_scoped_fact_check_result(
                requirement_result,
                &expected_domain,
                &format!("known-forall domain requirement {domain_index}"),
            )?;
            let Some(proof) =
                self.construct_lean_proof_from_direct_fact_result(requirement_result)?
            else {
                return Ok(None);
            };
            application_terms.push(format!("({proof})"));
        }

        let then_fact_index = result.source_conclusion_location.then_fact_index();
        let source_then_fact = source_forall
            .then_facts
            .get(then_fact_index)
            .ok_or_else(|| "known-forall Result selected a missing then fact".to_string())?;
        let (source_conclusion, component_projection) = match result.source_conclusion_location {
            ForallConclusionLocation::DirectThenFact(_) => {
                (source_then_fact.clone().to_fact(), None)
            }
            ForallConclusionLocation::AndFactComponent(location) => {
                let ExistOrAndChainAtomicFact::AndFact(and_fact) = source_then_fact else {
                    return Err(
                        "known-forall Result selected an and component from a non-and conclusion"
                            .into(),
                    );
                };
                let component = and_fact
                    .facts
                    .get(location.component_index)
                    .ok_or_else(|| {
                        "known-forall Result selected a missing and component".to_string()
                    })?;
                (
                    Fact::from(component.clone()),
                    Some((location.component_index, and_fact.facts.len())),
                )
            }
            ForallConclusionLocation::ChainFactComponent(location) => {
                let ExistOrAndChainAtomicFact::ChainFact(chain_fact) = source_then_fact else {
                    return Err(
                            "known-forall Result selected a chain component from a non-chain conclusion"
                                .into(),
                        );
                };
                let components = chain_fact
                    .facts()
                    .map_err(|error| format!("known-forall source chain is invalid: {error:?}"))?;
                let component = components.get(location.component_index).ok_or_else(|| {
                    "known-forall Result selected a missing chain component".to_string()
                })?;
                (
                    Fact::from(component.clone()),
                    Some((location.component_index, components.len())),
                )
            }
        };
        let instantiated_conclusion = substitution_runtime
            .inst_fact(
                &source_conclusion,
                &substitutions,
                SubstitutionMode::Exact,
                None,
            )
            .map_err(|error| format!("known-forall conclusion substitution failed: {error:?}"))?;
        let mut application = format!("({})", application_terms.join(" "));
        let then_projection =
            conjunction_selector(then_fact_index, source_forall.then_facts.len())?;
        application.push_str(&then_projection);
        if let Some((component_index, component_count)) = component_projection {
            application.push_str(&conjunction_selector(component_index, component_count)?);
        }
        if instantiated_conclusion.to_string() == target.to_string() {
            let transported = if facts_require_exact_predicate_argument_transport(
                &source_conclusion,
                target,
                &self.environment_stack,
            ) {
                render_fact_proof_across_exact_predicate_arguments(
                    &source_conclusion,
                    target,
                    &source_application_context,
                    &self.environment_stack,
                    &application,
                )?
            } else {
                application.clone()
            };
            return Ok(Some(
                if uses_exact_refined_numeric_parameter && transported == application {
                    format!(
                    "(by\n  simpa [Litex.abs, Complex.ext_iff, Real.norm_eq_abs] using {application})"
                )
                } else {
                    transported
                },
            ));
        }
        if membership_facts_are_equal_up_to_nested_binder_alpha(&instantiated_conclusion, target)
            || equality_facts_are_equal_up_to_nested_binder_alpha(&instantiated_conclusion, target)
            || subset_facts_are_equal_up_to_nested_binder_alpha(&instantiated_conclusion, target)
            || nonempty_facts_are_equal_up_to_nested_binder_alpha(&instantiated_conclusion, target)
            || normal_atomic_facts_are_equal_up_to_nested_binder_alpha(
                &instantiated_conclusion,
                target,
            )
        {
            return Ok(Some(application));
        }
        if elementwise_forall_is_set_inclusion(&instantiated_conclusion, target)
            || elementwise_forall_is_set_inclusion(target, &instantiated_conclusion)
        {
            return Ok(Some(application));
        }
        if one_witness_existentials_are_alpha_equal(
            &instantiated_conclusion,
            target,
            &self.environment_stack,
        )
        .map_err(|error| format!("known-forall existential alpha comparison: {error}"))?
        {
            return Ok(Some(if uses_exact_refined_numeric_parameter {
                format!(
                    "(by\n  simpa [Litex.abs, Complex.ext_iff, Real.norm_eq_abs] using {application})"
                )
            } else {
                application
            }));
        }
        if facts_align_by_anonymous_function_beta_normalization_for_result_compiler(
            &instantiated_conclusion,
            target,
        )? {
            render_fact(target, &self.environment_stack)?;
            return Ok(Some(format!("(by\n  simpa using {application})")));
        }
        if facts_align_by_nested_rational_normalization_for_result_compiler(
            &instantiated_conclusion,
            target,
        ) {
            render_fact(target, &self.environment_stack)?;
            return Ok(Some(format!(
                "(by\n  convert {application} using 1 <;> norm_num)"
            )));
        }
        Err(format!(
            "known-forall instance `{instantiated_conclusion}` does not match target `{target}`"
        ))
    }
}
