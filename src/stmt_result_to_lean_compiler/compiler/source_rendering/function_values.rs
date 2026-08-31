//! Named and anonymous function value rendering.

use super::super::*;

/// Render the target value for a direct named-function Result.
/// Binder names are the same names installed by the parent Result compiler's
/// child environment, so the nesting of the generated Lean term mirrors the
/// nesting of `SuccessVerifyFunctionDefinitionResult`. A reviewed native
/// numeric return can be represented directly; every other return carrier is selected from
/// the exact recursive membership proof retained by that Result.
pub(in super::super) fn render_named_function_value_from_result(
    function: &LeanTargetFunctionTypeRepresentation,
    body: &LeanTargetObjectRepresentation,
    source_body: &Obj,
    return_proof: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(String, NativeFunctionBodyCarrier), String> {
    let real_signature = function.parameters.iter().all(|parameter| {
        parameter.set == LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real)
    }) && function.return_set.as_ref()
        == &LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real);
    let integer_signature = function.parameters.iter().all(|parameter| {
        parameter.set == LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer)
    }) && function.return_set.as_ref()
        == &LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer);
    let native_body_carrier = if real_signature {
        NativeFunctionBodyCarrier::Real
    } else if integer_signature {
        NativeFunctionBodyCarrier::Integer
    } else {
        NativeFunctionBodyCarrier::None
    };
    if function_uses_telescope(function) {
        validate_function_type(function)?;
        let mut binders = Vec::with_capacity(function.parameters.len() + 1);
        let mut parameter_representations = HashMap::new();
        for (index, parameter) in function.parameters.iter().enumerate() {
            let suffix = index + 1;
            let alpha = format!("__alpha{suffix}");
            let argument = format!("__arg{suffix}");
            let membership = format!("__arg{suffix}_in");
            let domain = render_lean_source_for_target_set_representation(&parameter.set, context)?;
            binders.push(format!(
                "fun {{{alpha} : Type}} ({argument} : {alpha}) ({membership} : Litex.In {argument} {domain}) => "
            ));
            parameter_representations.insert(
                parameter.symbol_id,
                format!("Litex.In.rep {argument} {membership}"),
            );
        }
        if !function.domain_facts.is_empty() {
            binders.push("fun __arg_domain => ".into());
        }
        let body = match native_body_carrier {
            NativeFunctionBodyCarrier::Real => render_real_function_body_with_parameters(
                body,
                &parameter_representations,
                context,
            )?,
            NativeFunctionBodyCarrier::Integer => render_integer_function_body_with_parameters(
                body,
                &parameter_representations,
                context,
            )?,
            NativeFunctionBodyCarrier::None => {
                let rendered_source_body = render_obj(source_body, context)?;
                format!("Litex.In.rep {rendered_source_body} ({return_proof})")
            }
        };
        return Ok((
            format!("{}ULift.up ({body})", binders.concat()),
            native_body_carrier,
        ));
    }

    validate_unary_function_type(function)?;
    let rendered_body = match native_body_carrier {
        NativeFunctionBodyCarrier::Real => render_real_function_body(
            body,
            function.parameters[0].symbol_id,
            "Litex.In.rep __arg __arg_in",
            context,
        )?,
        NativeFunctionBodyCarrier::Integer => render_integer_function_body_with_parameters(
            body,
            &HashMap::from([(
                function.parameters[0].symbol_id,
                "Litex.In.rep __arg __arg_in".to_string(),
            )]),
            context,
        )?,
        NativeFunctionBodyCarrier::None => {
            let rendered_source_body = render_obj(source_body, context)?;
            format!("Litex.In.rep {rendered_source_body} ({return_proof})")
        }
    };
    if function.domain_facts.is_empty() {
        if native_body_carrier == NativeFunctionBodyCarrier::Integer {
            let own_body = render_integer_function_body_with_parameters(
                body,
                &HashMap::from([(function.parameters[0].symbol_id, "__arg".to_string())]),
                context,
            )?;
            return Ok((
                format!(
                    "{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in => {rendered_body}, callOwn := fun (__arg : ℤ) => {own_body} }}"
                ),
                native_body_carrier,
            ));
        }
        Ok((
            format!("{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in => {rendered_body} }}"),
            native_body_carrier,
        ))
    } else {
        Ok((
            format!(
                "{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in __arg_domain => {rendered_body} }}"
            ),
            native_body_carrier,
        ))
    }
}

pub(in super::super) fn render_integer_function_body_with_parameters(
    body: &LeanTargetObjectRepresentation,
    parameter_representations: &HashMap<SymbolId, String>,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match body {
        LeanTargetObjectRepresentation::Symbol { symbol_id, .. }
            if parameter_representations.contains_key(symbol_id) =>
        {
            Ok(parameter_representations[symbol_id].clone())
        }
        LeanTargetObjectRepresentation::Number { normalized_value }
            if normalized_value.parse::<i128>().is_ok() =>
        {
            Ok(format!("({normalized_value} : ℤ)"))
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
            let left = render_integer_function_body_with_parameters(
                &arguments[0],
                parameter_representations,
                context,
            )?;
            let right = render_integer_function_body_with_parameters(
                &arguments[1],
                parameter_representations,
                context,
            )?;
            let operator = match operator {
                LeanTargetBuiltinObjectOperator::Add => "+",
                LeanTargetBuiltinObjectOperator::Sub => "-",
                LeanTargetBuiltinObjectOperator::Mul => "*",
                _ => unreachable!("guarded integer binary operator"),
            };
            Ok(format!("({left} {operator} {right})"))
        }
        LeanTargetObjectRepresentation::Symbol { .. } => render_ir_symbol(body, context),
        other => Err(format!(
            "compiler integer named-function body does not support {other:?}"
        )),
    }
}

pub(in super::super) fn render_real_function_body(
    body: &LeanTargetObjectRepresentation,
    parameter_symbol_id: SymbolId,
    parameter_representation: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    render_real_function_body_with_parameters(
        body,
        &HashMap::from([(parameter_symbol_id, parameter_representation.to_string())]),
        context,
    )
}

pub(in super::super) fn render_real_function_body_with_parameters(
    body: &LeanTargetObjectRepresentation,
    parameter_representations: &HashMap<SymbolId, String>,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match body {
        LeanTargetObjectRepresentation::Symbol { symbol_id, .. }
            if parameter_representations.contains_key(symbol_id) =>
        {
            Ok(parameter_representations[symbol_id].clone())
        }
        LeanTargetObjectRepresentation::Number { normalized_value }
            if !normalized_value.is_empty()
                && normalized_value
                    .chars()
                    .all(|character| character.is_ascii_digit()) =>
        {
            Ok(format!("({normalized_value} : ℝ)"))
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
            let left = render_real_function_body_with_parameters(
                &arguments[0],
                parameter_representations,
                context,
            )?;
            let right = render_real_function_body_with_parameters(
                &arguments[1],
                parameter_representations,
                context,
            )?;
            let operator = match operator {
                LeanTargetBuiltinObjectOperator::Add => "+",
                LeanTargetBuiltinObjectOperator::Sub => "-",
                LeanTargetBuiltinObjectOperator::Mul => "*",
                LeanTargetBuiltinObjectOperator::Div => "/",
                _ => unreachable!("guarded real binary operator"),
            };
            Ok(format!("({left} {operator} {right})"))
        }
        LeanTargetObjectRepresentation::Symbol { .. } => render_ir_symbol(body, context),
        other => Err(format!(
            "compiler real named-function body does not support {other:?}"
        )),
    }
}

pub(in super::super) fn render_anonymous_function(
    function: &LeanTargetAnonymousFunctionRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let result_context = context
        .well_definedness
        .as_ref()
        .ok_or_else(|| "anonymous function has no active Result-owned WD context".to_string())?;
    let synthetic_occurrence = function.source_occurrence_id.is_none();
    let occurrence = if let Some(occurrence) = function.source_occurrence_id {
        occurrence
    } else {
        let mut owners = result_context
            .anonymous_functions
            .iter()
            .filter_map(|(owner, certificate)| {
                (obj_equality_key(&certificate.source_function) == function.semantic_key)
                    .then_some(*owner)
            })
            .collect::<Vec<_>>();
        owners.sort_by_key(|owner| owner.value());
        let [owner] = owners.as_slice() else {
            return Err(format!(
                "synthetic anonymous function has {} alpha-equivalent Result owners",
                owners.len()
            ));
        };
        *owner
    };
    let owner_occurrence = result_context
        .anonymous_function_occurrence_aliases
        .get(&occurrence)
        .copied()
        .unwrap_or(occurrence);
    let anonymous_context = result_context
        .anonymous_functions
        .get(&owner_occurrence)
        .ok_or_else(|| {
            let equivalent_owners = result_context
                .anonymous_functions
                .iter()
                .filter_map(|(candidate, certificate)| {
                    (obj_equality_key(&certificate.source_function) == function.semantic_key)
                        .then_some(candidate.value().to_string())
                })
                .collect::<Vec<_>>()
                .join(", ");
            let aliases = result_context
                .anonymous_function_occurrence_aliases
                .iter()
                .map(|(source, owner)| format!("{}->{}", source.value(), owner.value()))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "anonymous function occurrence {} has no exact recursive Result context; alpha-equivalent Result owners [{}]; installed aliases [{}]",
                occurrence.value(), equivalent_owners, aliases
            )
        })?;
    if obj_equality_key(&anonymous_context.source_function) != function.semantic_key {
        return Err(
            "anonymous function Result context changed its source body or signature".into(),
        );
    }
    // Keep the current source occurrence.  An alpha-equivalent Result owner
    // supplies the binder/closure certificate, but its stored source object
    // may have been produced by substitution and therefore lack parser-owned
    // occurrence identities on nested applications.  Replacing the current
    // object with that synthetic owner would discard exactly the identities
    // needed to select nested WD certificates.
    let function = function.clone();
    validate_function_type(&function.function)?;

    let mut nested = context.clone();
    let uses_telescope = function_uses_telescope(&function.function);
    let mut binders = Vec::with_capacity(function.function.parameters.len());
    let mut parameter_values = HashMap::new();
    for (parameter_index, parameter) in function.function.parameters.iter().enumerate() {
        let mut parameter_premises = anonymous_context
            .parameters
            .iter()
            .filter_map(|premise| {
                let WellDefinedBinderPremiseRole::ParameterMembership {
                    parameter_group_index,
                    parameter_index,
                } = premise.role
                else {
                    return None;
                };
                Some(((parameter_group_index, parameter_index), premise))
            })
            .collect::<Vec<_>>();
        parameter_premises.sort_by_key(|(position, _)| *position);
        let parameter_premise = parameter_premises
            .get(parameter_index)
            .map(|(_, premise)| *premise)
            .ok_or_else(|| {
                format!(
                    "anonymous function has no ordered membership premise for parameter {parameter_index}"
                )
            })?;
        if !synthetic_occurrence
            && owner_occurrence == occurrence
            && parameter_premise.symbol_id != Some(parameter.symbol_id)
        {
            return Err(format!(
                "anonymous function parameter {parameter_index} changed its exact SymbolId"
            ));
        }
        let suffix = if uses_telescope {
            (parameter_index + 1).to_string()
        } else {
            String::new()
        };
        let argument = format!("__arg{suffix}");
        let membership = format!("__arg{suffix}_in");
        let domain = render_lean_source_for_target_set_representation(&parameter.set, &nested)?;
        if uses_telescope {
            binders.push(format!(
                "fun {{__alpha{} : Type}} ({argument} : __alpha{}) ({membership} : Litex.In {argument} {domain}) => ",
                parameter_index + 1,
                parameter_index + 1,
            ));
        }
        nested
            .symbol_names
            .insert(parameter.symbol_id, argument.clone());
        if synthetic_occurrence || owner_occurrence != occurrence {
            let owner_symbol_id = parameter_premise.symbol_id.ok_or_else(|| {
                format!("anonymous function owner has no SymbolId for parameter {parameter_index}")
            })?;
            nested
                .symbol_names
                .insert(owner_symbol_id, argument.clone());
            install_numeric_representations_from_membership(
                owner_symbol_id,
                &parameter.set,
                &argument,
                &membership,
                &mut nested,
            );
        }
        nested
            .fact_names
            .insert(parameter_premise.fact_id, membership.clone());
        nested.fact_propositions.insert(
            parameter_premise.fact_id,
            parameter_premise.proposition.clone(),
        );
        install_rendered_parameter_aliases(
            parameter.symbol_id,
            &format!("Litex.In {argument} {domain}"),
            &membership,
            None,
            &mut nested,
        )
        .map_err(|error| {
            format!("anonymous function parameter {parameter_index} aliases failed: {error}")
        })?;
        if let Some(real) = membership_real_value(&parameter.set, &argument, &membership) {
            nested.numeric_real_values.insert(parameter.symbol_id, real);
        }
        if let Some(integer) = membership_integer_value(&parameter.set, &argument, &membership) {
            nested
                .numeric_integer_values
                .insert(parameter.symbol_id, integer);
        }
        if let Some(rational) = membership_rational_value(&parameter.set, &argument, &membership) {
            nested
                .numeric_rational_values
                .insert(parameter.symbol_id, rational);
        }
        if let Some(representation) =
            membership_numeric_value(&parameter.set, &argument, &membership)
        {
            nested
                .numeric_representations
                .insert(parameter.symbol_id, representation);
        }
        if let Some(proof) = membership_numeric_proof(&parameter.set, &argument, &membership) {
            nested
                .numeric_representation_memberships
                .insert(parameter.symbol_id, proof);
        }
        parameter_values.insert(parameter.symbol_id, (argument, membership));
    }

    let domain_premises = &anonymous_context.domains;
    if domain_premises.len() != function.function.domain_facts.len() {
        return Err("anonymous function binder scope changed its domain-premise count".into());
    }
    for (index, premise) in domain_premises.iter().enumerate() {
        let selector = conjunction_selector(index, domain_premises.len())?;
        let name = if domain_premises.len() == 1 {
            "__arg_domain".into()
        } else {
            format!("__arg_domain{selector}")
        };
        nested.fact_names.insert(premise.fact_id, name);
        nested
            .fact_propositions
            .insert(premise.fact_id, premise.proposition.clone());
    }
    if uses_telescope && !domain_premises.is_empty() {
        binders.push("fun __arg_domain => ".into());
    }

    let mut inferred_lets = Vec::new();
    for step in &anonymous_context.compiled_inference_fact_proof_steps {
        inferred_lets.push(format!("{}; ", step.render_as_local_let_statement()));
        nested
            .fact_names
            .insert(step.fact_id, step.local_lean_name.clone());
        nested
            .fact_propositions
            .insert(step.fact_id, step.fact.clone());
    }

    let closure = &anonymous_context.closure;
    let selected_return = match closure.role {
        WellDefinednessRequirementRole::AnonymousFunctionBodyMembership => {
            let (body, return_set) = membership_parts(&closure.expected_proposition)?;
            let owner_body_changed = if !synthetic_occurrence && owner_occurrence == occurrence {
                obj_equality_key(body) != obj_equality_key(&function.source_body)
            } else {
                false
            };
            if owner_body_changed
                || LeanTargetObjectRepresentation::lower(return_set).map_err(|error| {
                    format!("anonymous function return carrier failed to lower: {error}")
                })? != *function.function.return_set
            {
                return Err(
                    "anonymous function return closure changed its exact body or carrier".into(),
                );
            }
            match function.function.return_set.as_ref() {
                LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
                    render_real_source_object(&function.source_body, &nested).map_err(|error| {
                        format!("anonymous function real body failed to render: {error}")
                    })?
                }
                LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer) => {
                    render_integer_obj(&function.source_body, &nested).map_err(|error| {
                        format!("anonymous function integer body failed to render: {error}")
                    })?
                }
                _ => format!(
                    "Litex.In.rep {} ({})",
                    render_obj(&function.source_body, &nested)?,
                    closure.proof_expression.as_ref().ok_or_else(|| {
                        "anonymous function body-membership Result was not compiled".to_string()
                    })?
                ),
            }
        }
        WellDefinednessRequirementRole::AnonymousFunctionBoundParameterSubset {
            parameter_group_index: _,
            parameter_index,
        } => {
            let parameter = function
                .function
                .parameters
                .get(parameter_index)
                .ok_or_else(|| {
                    "anonymous subset closure changed its bound parameter index".to_string()
                })?;
            let (argument, membership) =
                parameter_values.get(&parameter.symbol_id).ok_or_else(|| {
                    "anonymous subset closure lost its parameter evidence".to_string()
                })?;
            format!("Litex.In.rep {argument} {membership}")
        }
        _ => return Err("anonymous function retained an unsupported return-closure route".into()),
    };
    let checked_body = format!("{}{}", inferred_lets.concat(), selected_return);
    let value = if uses_telescope {
        format!("{}ULift.up ({checked_body})", binders.concat())
    } else if function.function.domain_facts.is_empty() {
        let exact_unary_integer = function.function.parameters.len() == 1
            && function.function.parameters[0].set
                == LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer)
            && function.function.return_set.as_ref()
                == &LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer);
        if exact_unary_integer {
            let mut own_context = context.clone();
            install_structured_induction_native_integer_symbol(
                function.function.parameters[0].symbol_id,
                "__arg",
                &mut own_context,
            );
            let own_body = render_integer_obj(&function.source_body, &own_context)?;
            format!(
                "{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in => {checked_body}, callOwn := fun (__arg : ℤ) => {own_body} }}"
            )
        } else {
            format!("{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in => {checked_body} }}")
        }
    } else {
        format!(
            "{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in __arg_domain => {checked_body} }}"
        )
    };
    Ok(format!(
        "({value} : {})",
        render_function_type(&function.function, context)?
    ))
}
