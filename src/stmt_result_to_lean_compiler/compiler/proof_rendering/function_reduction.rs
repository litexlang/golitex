//! Checked identity, integer, and real function reduction.

use super::super::*;

pub(in super::super) fn render_checked_identity_function_reduction_from_fact(
    target: &Fact,
    defining_equality_fact_id: crate::fact::id::FactId,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let binding = context
        .named_function_definitions
        .get(&defining_equality_fact_id)
        .ok_or_else(|| {
            format!(
                "checked function reduction references unavailable defining FactId `{defining_equality_fact_id}`"
            )
    })?;
    let (target_left, target_right) = equality_parts(target)?;
    let application_object = target_left;
    let LeanTargetObjectRepresentation::FunctionApplication(application) =
        LeanTargetObjectRepresentation::lower(application_object)?
    else {
        return Err("checked function reduction retained a non-application side".into());
    };
    if application.argument_layers.len() != 1
        || application.source_argument_layers.len() != 1
        || application.argument_layers[0].len() != binding.function.parameters.len()
        || application.source_argument_layers[0].len() != binding.function.parameters.len()
    {
        return Err("checked function reduction changed its one-layer parameter telescope".into());
    }
    let LeanTargetObjectRepresentation::Symbol {
        symbol_id: head_symbol_id,
        ..
    } = application.head.as_ref()
    else {
        return Err("checked function reduction requires a named head".into());
    };
    if *head_symbol_id != binding.symbol_id {
        return Err("checked function reduction changed its checked substitution".into());
    }

    let application_context = resolve_function_application_result_context(&application, context)?;
    let [application_layer] = application_context.layers.as_slice() else {
        return Err(
            "checked function reduction requires one Result-owned application layer".into(),
        );
    };
    let requirements = &application_layer.requirements;
    if requirements.len() != binding.function.parameters.len() + binding.function.domain_facts.len()
    {
        return Err(
            "checked function reduction changed its exact application requirement count".into(),
        );
    }
    let mut definition_context = context.clone();
    definition_context.well_definedness = Some(binding.well_definedness.clone());
    let mut argument_evidence = HashMap::new();
    for (parameter_index, ((parameter, source_argument), local_premise)) in binding
        .function
        .parameters
        .iter()
        .zip(application.source_argument_layers[0].iter())
        .zip(binding.parameter_premises.iter())
        .enumerate()
    {
        let matches = requirements
            .iter()
            .filter(|requirement| {
                requirement.role
                    == (WellDefinednessRequirementRole::FunctionArgumentMembership {
                        layer_index: 0,
                        parameter_index,
                    })
            })
            .collect::<Vec<_>>();
        let [argument_requirement] = matches.as_slice() else {
            return Err(format!(
                "checked function reduction requires one argument-membership WD edge for parameter {parameter_index}"
            ));
        };
        let argument = render_obj(source_argument, context)?;
        let argument_membership =
            render_function_application_requirement_proof(argument_requirement, context)?;
        let expected_membership = format!(
            "Litex.In {argument} {}",
            render_lean_source_for_target_set_representation(&parameter.set, &definition_context)?
        );
        let retained_membership = render_fact(&argument_requirement.expected_proposition, context)?;
        if retained_membership != expected_membership {
            return Err(format!(
                "checked function reduction parameter {parameter_index} expected `{expected_membership}`, retained `{retained_membership}`"
            ));
        }
        definition_context
            .symbol_names
            .insert(parameter.symbol_id, argument.clone());
        definition_context
            .fact_names
            .insert(local_premise.fact_id, argument_membership.clone());
        definition_context
            .fact_propositions
            .insert(local_premise.fact_id, local_premise.fact.clone());
        if let Some(real) = membership_real_value(&parameter.set, &argument, &argument_membership) {
            definition_context
                .numeric_real_values
                .insert(parameter.symbol_id, real);
        }
        if let Some(integer) =
            membership_integer_value(&parameter.set, &argument, &argument_membership)
        {
            definition_context
                .numeric_integer_values
                .insert(parameter.symbol_id, integer);
        }
        if let Some(rational) =
            membership_rational_value(&parameter.set, &argument, &argument_membership)
        {
            definition_context
                .numeric_rational_values
                .insert(parameter.symbol_id, rational);
        }
        if let Some(representation) =
            membership_numeric_value(&parameter.set, &argument, &argument_membership)
        {
            definition_context
                .numeric_representations
                .insert(parameter.symbol_id, representation);
        }
        if let Some(proof) =
            membership_numeric_proof(&parameter.set, &argument, &argument_membership)
        {
            definition_context
                .numeric_representation_memberships
                .insert(parameter.symbol_id, proof);
        }
        argument_evidence.insert(
            parameter.symbol_id,
            CheckedNamedFunctionReductionArgumentEvidence {
                source_argument: source_argument.clone(),
                rendered_source_argument: argument,
                membership_proof: argument_membership,
                parameter_set: parameter.set.clone(),
                native_integer_argument: if parameter.set
                    == LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer)
                {
                    Some(render_integer_obj(source_argument, context)?)
                } else {
                    None
                },
                native_real_argument: if binding.function.parameters.len() == 1
                    && parameter.set
                        == LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real)
                    && matches!(source_argument, Obj::Number(_))
                {
                    Some(render_real_obj(source_argument, context)?)
                } else {
                    None
                },
                closed_positive_natural_argument: closed_positive_natural_value_from_fact_proof(
                    argument_requirement.verification.as_ref(),
                )?,
            },
        );
    }
    let mut source_domain_definition_context = definition_context.clone();
    for (symbol_id, evidence) in &argument_evidence {
        source_domain_definition_context
            .numeric_representations
            .insert(*symbol_id, evidence.rendered_source_argument.clone());
    }
    for (domain_index, (source_fact, local_premise)) in binding
        .function
        .domain_facts
        .iter()
        .zip(binding.domain_premises.iter())
        .enumerate()
    {
        let matches = requirements
            .iter()
            .filter(|requirement| {
                requirement.role
                    == (WellDefinednessRequirementRole::FunctionDomain {
                        layer_index: 0,
                        domain_index,
                    })
            })
            .collect::<Vec<_>>();
        let [domain_requirement] = matches.as_slice() else {
            return Err(format!(
                "checked function reduction requires one domain WD edge for clause {domain_index}"
            ));
        };
        let expected_domain = render_fact(source_fact, &source_domain_definition_context)?;
        let retained_domain = render_fact(&domain_requirement.expected_proposition, context)?;
        if retained_domain != expected_domain {
            return Err(format!(
                "checked function reduction domain {domain_index} expected `{expected_domain}`, retained `{retained_domain}`"
            ));
        }
        definition_context.fact_names.insert(
            local_premise.fact_id,
            render_function_application_requirement_proof(domain_requirement, context)?,
        );
        definition_context
            .fact_propositions
            .insert(local_premise.fact_id, local_premise.fact.clone());
    }
    let application_term = render_function_application(&application, context)?;
    let expected_application = render_obj(application_object, context)?;
    if expected_application != application_term {
        return Err("checked identity reduction changed its rendered equality sides".into());
    }
    let exact_single_carrier_application = binding.function.domain_facts.is_empty()
        && binding.function.parameters.len() == 1
        && match (
            binding.native_body_carrier,
            &binding.function.parameters[0].set,
        ) {
            (
                NativeFunctionBodyCarrier::Integer,
                LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer),
            )
            | (
                NativeFunctionBodyCarrier::Real,
                LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real),
            ) => true,
            (
                NativeFunctionBodyCarrier::Real,
                LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural),
            ) => argument_evidence
                .get(&binding.function.parameters[0].symbol_id)
                .is_some_and(|evidence| evidence.closed_positive_natural_argument.is_some()),
            _ => false,
        };
    let apply = if exact_single_carrier_application {
        "Litex.fnApplyCarrier"
    } else if function_uses_telescope(&binding.function) {
        "Litex.fnTelescopeApplyOwn"
    } else if binding.function.domain_facts.is_empty() {
        "Litex.fnApplyOwn"
    } else {
        "Litex.fnApplyWhereOwn"
    };
    let other_object = target_right;
    let rendered_other = render_obj(other_object, context)?;
    if binding.native_body_carrier != NativeFunctionBodyCarrier::None {
        // Native carrier functions use their concrete numeric observer.  The
        // no-observation ABI is reserved for dependent telescope functions;
        // ordinary `FnWhere`/`Fn` applications remain observable even when a
        // surrounding proof later transports an endpoint through a generic
        // carrier.
        let observation_free = function_uses_telescope(&binding.function);
        let body_same = match binding.native_body_carrier {
            NativeFunctionBodyCarrier::Real => render_real_function_body_same_with_parameters_mode(
                &binding.body,
                &argument_evidence,
                context,
                observation_free,
            )?,
            NativeFunctionBodyCarrier::Integer => {
                let proof = render_integer_function_body_same_with_parameters(
                    &binding.body,
                    &argument_evidence,
                    context,
                )?;
                if observation_free {
                    format!("Litex.Same.withoutObservation ({proof})")
                } else {
                    proof
                }
            }
            NativeFunctionBodyCarrier::None => unreachable!("guarded native body carrier"),
        };
        return Ok(format!(
            "(by\n  unfold {apply} {}\n  exact {body_same})",
            binding.name,
        ));
    }
    // A telescope function returning a predicate-defined carrier is
    // intentionally heterogeneous.  Its body is selected by `In.rep`, so
    // the reduction proof must stay in the no-observation Same ABI and bridge
    // the concrete real source body only at the final endpoint.  Asking Lean
    // to infer an observed subtype observer through the opaque Set.Carrier
    // projection is both brittle and, for a generic parameter, unsound.
    if let LeanTargetObjectRepresentation::SetBuilder(builder) = &*binding.function.return_set {
        if *builder.set == LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real)
        {
            // The ordinary definition context renders a numeric application
            // argument in its source/Complex view. A set-builder return,
            // however, selects the function parameter's exact real carrier;
            // install that native view before rendering the substituted body.
            let mut real_body_context = definition_context.clone();
            for (symbol_id, evidence) in &argument_evidence {
                if let Some(real) = evidence.native_real_argument.as_ref() {
                    real_body_context
                        .symbol_names
                        .insert(*symbol_id, real.clone());
                    real_body_context
                        .numeric_real_values
                        .insert(*symbol_id, real.clone());
                }
            }
            let real_body = render_real_obj(&binding.source_body, &real_body_context)?;
            return Ok(format!(
                "(by\n  unfold {apply} {}\n  exact Litex.Same.symmNoObservation (Litex.Same.transNoObservation (Litex.Same.complexRealNoObservation ({real_body})) (Litex.Same.withoutObservation (Litex.In.same_rep ({real_body}) _))))",
                binding.name,
            ));
        }
    }
    // The defining Result already proved that this source body belongs to its
    // declared return carrier. Reduction only needs the body after exact
    // argument substitution; it must not reconstruct that proof from the old
    // compatibility statement IR.
    let source_body = render_obj(&binding.source_body, &definition_context)?;
    if rendered_other != source_body {
        return Err(format!(
            "checked function reduction changed the substituted source body: expected `{source_body}`, retained `{rendered_other}`"
        ));
    }
    Ok(format!(
        "(by\n  unfold {apply} {}\n  exact Litex.Same.transNoObservation (Litex.Same.symmNoObservation (Litex.In.same_rep _ _)) (Litex.Same.reflNoObservation _))",
        binding.name,
    ))
}

pub(in super::super) fn render_integer_function_body_same_with_parameters(
    body: &LeanTargetObjectRepresentation,
    argument_evidence: &HashMap<SymbolId, CheckedNamedFunctionReductionArgumentEvidence>,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match body {
        LeanTargetObjectRepresentation::Symbol { symbol_id, .. }
            if argument_evidence.contains_key(symbol_id) =>
        {
            let evidence = &argument_evidence[symbol_id];
            if evidence.parameter_set
                != LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer)
            {
                return Err(
                    "checked integer function reduction retained a non-integer parameter".into(),
                );
            }
            if let Some(native_integer_argument) = &evidence.native_integer_argument {
                return Ok(format!(
                    "Litex.Same.intComplexOfEq (z := ({native_integer_argument})) (by norm_cast)"
                ));
            }
            let argument = &evidence.rendered_source_argument;
            let argument_membership = &evidence.membership_proof;
            let rendered_target_argument = render_numeric_obj(&evidence.source_argument, context)?;
            let selected_integer = membership_integer_value(
                &evidence.parameter_set,
                argument,
                argument_membership,
            )
            .ok_or_else(|| {
                "checked integer function reduction lost its selected integer representative"
                    .to_string()
            })?;
            if rendered_target_argument == selected_integer {
                Ok(format!("Litex.Same.refl ({selected_integer})"))
            } else if rendered_target_argument == *argument {
                Ok(format!(
                    "Litex.Same.symm (Litex.In.same_rep {argument} ({argument_membership}))"
                ))
            } else {
                Err(format!(
                    "checked integer function reduction target uses unrelated argument representation `{rendered_target_argument}`"
                ))
            }
        }
        LeanTargetObjectRepresentation::Number { normalized_value }
            if normalized_value.parse::<i128>().is_ok() =>
        {
            Ok(format!(
                "Litex.Same.intComplexOfEq (z := ({normalized_value} : ℤ)) (by norm_num)"
            ))
        }
        LeanTargetObjectRepresentation::BuiltinApp {
            operator,
            arguments,
            ..
        } if arguments.len() == 2
            && matches!(
                operator,
                LeanTargetBuiltinObjectOperator::Add
                    | LeanTargetBuiltinObjectOperator::Sub
                    | LeanTargetBuiltinObjectOperator::Mul
            ) =>
        {
            let left = render_integer_function_body_same_with_parameters(
                &arguments[0],
                argument_evidence,
                context,
            )?;
            let right = render_integer_function_body_same_with_parameters(
                &arguments[1],
                argument_evidence,
                context,
            )?;
            let theorem = match operator {
                LeanTargetBuiltinObjectOperator::Add => "Litex.Same.intAddComplex",
                LeanTargetBuiltinObjectOperator::Sub => "Litex.Same.intSubComplex",
                LeanTargetBuiltinObjectOperator::Mul => "Litex.Same.intMulComplex",
                _ => unreachable!("guarded integer binary operator"),
            };
            Ok(format!("{theorem} ({left}) ({right})"))
        }
        other => Err(format!(
            "checked integer function reduction does not support body {other:?}"
        )),
    }
}

fn render_real_function_body_same_with_parameters_mode(
    body: &LeanTargetObjectRepresentation,
    argument_evidence: &HashMap<SymbolId, CheckedNamedFunctionReductionArgumentEvidence>,
    context: &StmtResultToLeanCompilerEnvironmentStack,
    observation_free: bool,
) -> Result<String, String> {
    match body {
        LeanTargetObjectRepresentation::Symbol { symbol_id, .. }
            if argument_evidence.contains_key(symbol_id) =>
        {
            let evidence = &argument_evidence[symbol_id];
            let argument = &evidence.rendered_source_argument;
            let argument_membership = &evidence.membership_proof;
            let rendered_target_argument = render_numeric_obj(&evidence.source_argument, context)?;
            let selected_numeric_representation =
                membership_numeric_value(&evidence.parameter_set, argument, argument_membership)
                    .ok_or_else(|| {
                        "checked real function reduction parameter has no numeric representation"
                            .to_string()
                    })?;
            let target_uses_selected_representation =
                rendered_target_argument == selected_numeric_representation;
            let target_uses_exact_source_representation =
                match LeanTargetObjectRepresentation::lower(&evidence.source_argument)? {
                    LeanTargetObjectRepresentation::Symbol { symbol_id, .. } => context
                        .numeric_representations
                        .get(&symbol_id)
                        .is_some_and(|representation| representation == &rendered_target_argument),
                    _ => false,
                };
            if !target_uses_selected_representation
                && !target_uses_exact_source_representation
                && rendered_target_argument != *argument
            {
                return Err(format!(
                    "checked real function reduction target uses unrelated argument representation `{rendered_target_argument}`"
                ));
            }
            match &evidence.parameter_set {
                LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
                    if let Some(native_real_argument) = &evidence.native_real_argument {
                        let proof = if matches!(&evidence.source_argument, Obj::Number(_)) {
                            format!(
                                "(by\n  convert (Litex.Same.realComplex ({native_real_argument})) using 1\n  · exact Litex.In.rep_exact ({native_real_argument}) (Litex.In.own Litex.R ({native_real_argument}))\n  · norm_num)"
                            )
                        } else {
                            format!("Litex.Same.realComplex ({native_real_argument})")
                        };
                        if observation_free {
                            Ok(format!("Litex.Same.withoutObservation ({proof})"))
                        } else {
                            Ok(proof)
                        }
                    } else if target_uses_exact_source_representation {
                        // The source argument already inhabits the exact R
                        // carrier, but the function body is still defined
                        // through `In.rep`.  Force `Same.ofEq` to the native
                        // real observer and lift `rep_exact` through the
                        // carrier-to-real coercion; leaving the type implicit
                        // makes Lean choose the carrier's default observer.
                        let proof = format!(
                            "Litex.Same.trans (@Litex.Same.ofEq ℝ inferInstance (Litex.In.rep {argument} ({argument_membership}) : ℝ) ({argument} : ℝ) (congrArg (fun x : Litex.R.Carrier => (x : ℝ)) (Litex.In.rep_exact {argument} ({argument_membership})))) (Litex.Same.realComplex ({argument} : ℝ))"
                        );
                        if observation_free {
                            Ok(format!("Litex.Same.withoutObservation ({proof})"))
                        } else {
                            Ok(proof)
                        }
                    } else if target_uses_selected_representation {
                        let selected_real = membership_real_value(
                            &evidence.parameter_set,
                            argument,
                            argument_membership,
                        )
                        .ok_or_else(|| {
                            "checked real function reduction lost its selected real representative"
                                .to_string()
                        })?;
                        let proof = format!("Litex.Same.realComplex ({selected_real})");
                        if observation_free {
                            Ok(format!("Litex.Same.withoutObservation ({proof})"))
                        } else {
                            Ok(proof)
                        }
                    } else {
                        if observation_free {
                            Ok(format!(
                                "Litex.Same.symmWithoutObservation (Litex.In.same_rep {argument} ({argument_membership}))"
                            ))
                        } else {
                            Ok(format!(
                                "Litex.Same.symm (Litex.In.same_rep {argument} ({argument_membership}))"
                            ))
                        }
                    }
                }
                LeanTargetObjectRepresentation::StandardSet(
                    LeanTargetStandardSet::PositiveNatural,
                ) => {
                    if let Some(value) = &evidence.closed_positive_natural_argument {
                        let carrier =
                            format!("(⟨{value}, by norm_num⟩ : Litex.NPos.Carrier)");
                        let proof = format!(
                            "(by\n  have __selected := Litex.In.rep_exact {carrier} (Litex.In.own Litex.NPos {carrier})\n  convert (Litex.Same.realComplex ({value} : ℝ)) using 1\n  · exact congrArg (fun value : Litex.NPos.Carrier => (((value.val : ℕ) : ℝ))) __selected\n  · norm_num)"
                        );
                        if observation_free {
                            Ok(format!("Litex.Same.withoutObservation ({proof})"))
                        } else {
                            Ok(proof)
                        }
                    } else if target_uses_selected_representation {
                        let selected_real = membership_real_value(
                            &evidence.parameter_set,
                            argument,
                            argument_membership,
                        )
                        .ok_or_else(|| {
                            "checked positive-natural reduction lost its selected real representative"
                                .to_string()
                        })?;
                        let proof = format!("Litex.Same.realComplex ({selected_real})");
                        if observation_free {
                            Ok(format!("Litex.Same.withoutObservation ({proof})"))
                        } else {
                            Ok(proof)
                        }
                    } else {
                        Err("checked positive-natural reduction cannot recover an observed numeric equality from generic membership".into())
                    }
                }
                other => Err(format!(
                    "checked real function reduction has no source-to-real bridge for parameter set {other:?}"
                )),
            }
        }
        LeanTargetObjectRepresentation::Number { normalized_value }
            if !normalized_value.is_empty()
                && normalized_value
                    .chars()
                    .all(|character| character.is_ascii_digit()) =>
        {
            let proof = format!("Litex.Same.realComplex ({normalized_value} : ℝ)");
            if observation_free {
                Ok(format!("Litex.Same.withoutObservation ({proof})"))
            } else {
                Ok(proof)
            }
        }
        LeanTargetObjectRepresentation::BuiltinApp {
            operator,
            arguments,
            ..
        } if arguments.len() == 2
            && matches!(
                operator,
                LeanTargetBuiltinObjectOperator::Add
                    | LeanTargetBuiltinObjectOperator::Sub
                    | LeanTargetBuiltinObjectOperator::Mul
                    | LeanTargetBuiltinObjectOperator::Div
            ) =>
        {
            let left = render_real_function_body_same_with_parameters_mode(
                &arguments[0],
                argument_evidence,
                context,
                observation_free,
            )?;
            let right = render_real_function_body_same_with_parameters_mode(
                &arguments[1],
                argument_evidence,
                context,
                observation_free,
            )?;
            let theorem = match (operator, observation_free) {
                (LeanTargetBuiltinObjectOperator::Add, false) => "Litex.Same.realAddComplex",
                (LeanTargetBuiltinObjectOperator::Sub, false) => "Litex.Same.realSubComplex",
                (LeanTargetBuiltinObjectOperator::Mul, false) => "Litex.Same.realMulComplex",
                (LeanTargetBuiltinObjectOperator::Div, false) => "Litex.Same.realDivComplex",
                (LeanTargetBuiltinObjectOperator::Add, true) => {
                    "Litex.Same.realAddComplexNoObservation"
                }
                (LeanTargetBuiltinObjectOperator::Sub, true) => {
                    "Litex.Same.realSubComplexNoObservation"
                }
                (LeanTargetBuiltinObjectOperator::Mul, true) => {
                    "Litex.Same.realMulComplexNoObservation"
                }
                (LeanTargetBuiltinObjectOperator::Div, true) => {
                    "Litex.Same.realDivComplexNoObservation"
                }
                _ => unreachable!("guarded real binary operator"),
            };
            Ok(format!("{theorem} ({left}) ({right})"))
        }
        other => Err(format!(
            "checked real function reduction does not support body {other:?}"
        )),
    }
}
