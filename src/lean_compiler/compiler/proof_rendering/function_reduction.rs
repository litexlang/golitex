//! Checked identity, integer, and real function reduction.

use super::super::*;

pub(in super::super) fn render_checked_identity_function_reduction_from_fact(
    target: &Fact,
    defining_equality_fact_id: crate::fact::id::FactId,
    application_side: LeanEqualityApplicationSide,
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
    let application_object = match application_side {
        LeanEqualityApplicationSide::Left => target_left,
        LeanEqualityApplicationSide::Right => target_right,
    };
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

    let result_context = context.well_definedness.as_ref().ok_or_else(|| {
        "checked function reduction has no active Result-owned WD context".to_string()
    })?;
    let application_context = result_context
        .function_applications
        .get(&application.source_occurrence_id)
        .ok_or_else(|| {
            "checked function reduction has no exact function-application Result context"
                .to_string()
        })?;
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
    let apply = if binding.native_body_carrier == NativeFunctionBodyCarrier::Integer
        && binding.function.domain_facts.is_empty()
    {
        "Litex.fnApplyCarrier"
    } else if function_uses_telescope(&binding.function) {
        "Litex.fnTelescopeApplyOwn"
    } else if binding.function.domain_facts.is_empty() {
        "Litex.fnApplyOwn"
    } else {
        "Litex.fnApplyWhereOwn"
    };
    if binding.native_body_carrier != NativeFunctionBodyCarrier::None {
        let body_same = match binding.native_body_carrier {
            NativeFunctionBodyCarrier::Real => render_real_function_body_same_with_parameters(
                &binding.body,
                &argument_evidence,
                context,
            )?,
            NativeFunctionBodyCarrier::Integer => {
                render_integer_function_body_same_with_parameters(
                    &binding.body,
                    &argument_evidence,
                    context,
                )?
            }
            NativeFunctionBodyCarrier::None => unreachable!("guarded native body carrier"),
        };
        let proof = if application_side == LeanEqualityApplicationSide::Left {
            body_same
        } else {
            format!("Litex.Same.symm ({body_same})")
        };
        return Ok(format!(
            "(by\n  unfold {apply} {}\n  exact {proof})",
            binding.name,
        ));
    }
    // The defining Result already proved that this source body belongs to its
    // declared return carrier. Reduction only needs the body after exact
    // argument substitution; it must not reconstruct that proof from the old
    // compatibility statement IR.
    let source_body = render_obj(&binding.source_body, &definition_context)?;
    let other_object = match application_side {
        LeanEqualityApplicationSide::Left => target_right,
        LeanEqualityApplicationSide::Right => target_left,
    };
    let rendered_other = render_obj(other_object, context)?;
    if rendered_other != source_body {
        return Err(format!(
            "checked function reduction changed the substituted source body: expected `{source_body}`, retained `{rendered_other}`"
        ));
    }
    let proof = if application_side == LeanEqualityApplicationSide::Left {
        "apply Litex.Same.symm\n  apply Litex.In.same_rep"
    } else {
        "apply Litex.In.same_rep"
    };
    Ok(format!(
        "(by\n  unfold {apply} {}\n  {proof})",
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

pub(in super::super) fn render_real_function_body_same_with_parameters(
    body: &LeanTargetObjectRepresentation,
    argument_evidence: &HashMap<SymbolId, CheckedNamedFunctionReductionArgumentEvidence>,
    context: &StmtResultToLeanCompilerEnvironmentStack,
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
            if !target_uses_selected_representation && rendered_target_argument != *argument {
                return Err(format!(
                    "checked real function reduction target uses unrelated argument representation `{rendered_target_argument}`"
                ));
            }
            match &evidence.parameter_set {
                LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
                    if target_uses_selected_representation {
                        let selected_real = membership_real_value(
                            &evidence.parameter_set,
                            argument,
                            argument_membership,
                        )
                        .ok_or_else(|| {
                            "checked real function reduction lost its selected real representative"
                                .to_string()
                        })?;
                        Ok(format!("Litex.Same.realComplex ({selected_real})"))
                    } else {
                        Ok(format!(
                            "Litex.Same.symm (Litex.In.same_rep {argument} ({argument_membership}))"
                        ))
                    }
                }
                LeanTargetObjectRepresentation::StandardSet(
                    LeanTargetStandardSet::PositiveNatural,
                ) => {
                    let representative =
                        format!("(Litex.In.rep {argument} ({argument_membership}))");
                    if target_uses_selected_representation {
                        Ok(format!(
                            "Litex.Same.trans (Litex.Same.symm (Litex.AsReal.nat ({representative}).val)) (Litex.Same.natComplex ({representative}).val)"
                        ))
                    } else {
                        Ok(format!(
                            "Litex.Same.symm (Litex.Same.trans (Litex.In.same_rep {argument} ({argument_membership})) (Litex.Same.trans (Litex.Same.subtype {representative}) (Litex.AsReal.nat ({representative}).val)))"
                        ))
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
            Ok(format!("Litex.Same.realComplex ({normalized_value} : ℝ)"))
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
            let left = render_real_function_body_same_with_parameters(
                &arguments[0],
                argument_evidence,
                context,
            )?;
            let right = render_real_function_body_same_with_parameters(
                &arguments[1],
                argument_evidence,
                context,
            )?;
            let theorem = match operator {
                LeanTargetBuiltinObjectOperator::Add => "Litex.Same.realAddComplex",
                LeanTargetBuiltinObjectOperator::Sub => "Litex.Same.realSubComplex",
                LeanTargetBuiltinObjectOperator::Mul => "Litex.Same.realMulComplex",
                LeanTargetBuiltinObjectOperator::Div => "Litex.Same.realDivComplex",
                _ => unreachable!("guarded real binary operator"),
            };
            Ok(format!("{theorem} ({left}) ({right})"))
        }
        other => Err(format!(
            "checked real function reduction does not support body {other:?}"
        )),
    }
}
