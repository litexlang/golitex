//! Result-owned function application certificates and rendering.

use super::super::*;

pub(in super::super) fn matches_directly_or_after_one_transparent_definition_pass(
    source: &Obj,
    target: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<bool, String> {
    if obj_equality_key(source) == obj_equality_key(target) {
        return Ok(true);
    }
    let substitutions = context
        .transparent_object_definitions
        .iter()
        .map(|(symbol_id, definition)| (symbol_id.substitution_key(), definition.value.clone()))
        .collect::<HashMap<_, _>>();
    if substitutions.is_empty() {
        return Ok(false);
    }
    let reduced = Runtime::default()
        .inst_obj(source, &substitutions, SubstitutionMode::Exact)
        .map_err(|error| {
            format!(
                "compiler could not replay transparent definition source alignment: {}",
                error.trace_message()
            )
        })?;
    Ok(obj_equality_key(&reduced) == obj_equality_key(target))
}

pub(in super::super) fn matches_result_owned_application_source(
    certified: &Obj,
    replayed: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<bool, String> {
    if matches_directly_or_after_one_transparent_definition_pass(certified, replayed, context)? {
        return Ok(true);
    }
    // A quantified definition replay may alpha-rename its binder after the
    // function-application Result was frozen.  Once both objects carry the
    // same parser-owned occurrence, that occurrence is the evidence join key;
    // permit only the corresponding identifier-erased source shape.  This
    // does not perform a text-based certificate lookup.
    Ok(certified.source_occurrence_id().is_some()
        && certified.source_occurrence_id() == replayed.source_occurrence_id()
        && source_display_without_symbol_ids(&certified.to_string())
            == source_display_without_symbol_ids(&replayed.to_string()))
}

pub(in super::super) fn install_result_owned_application_alpha_aliases(
    certified: &Obj,
    replayed: &Obj,
    current_context: &StmtResultToLeanCompilerEnvironmentStack,
    result_context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<bool, String> {
    if obj_equality_key(certified) == obj_equality_key(replayed) {
        return Ok(true);
    }
    // A transparent-definition certificate may retain the application before
    // the verifier's one checked substitution pass, while the replayed object
    // is already reduced.  Align the reduced, verifier-owned source before
    // installing alpha aliases; this uses exactly the same stored definitions
    // as the occurrence match above and does not normalize arbitrary facts.
    let substitutions = current_context
        .transparent_object_definitions
        .iter()
        .map(|(symbol_id, definition)| (symbol_id.substitution_key(), definition.value.clone()))
        .collect::<HashMap<_, _>>();
    if !substitutions.is_empty() {
        let reduced = Runtime::default()
            .inst_obj(certified, &substitutions, SubstitutionMode::Exact)
            .map_err(|error| {
                format!(
                    "compiler could not replay transparent definition alpha alignment: {}",
                    error.trace_message()
                )
            })?;
        if obj_equality_key(&reduced) != obj_equality_key(certified) {
            return install_result_owned_application_alpha_aliases(
                &reduced,
                replayed,
                current_context,
                result_context,
            );
        }
    }
    if let (Obj::Atom(certified_atom), Obj::Atom(replayed_atom)) = (certified, replayed) {
        let (Some(certified_symbol), Some(_replayed_symbol)) =
            (certified_atom.symbol_ref(), replayed_atom.symbol_ref())
        else {
            return Ok(false);
        };
        if source_display_without_symbol_ids(&certified.to_string())
            != source_display_without_symbol_ids(&replayed.to_string())
        {
            return Ok(false);
        }
        let replayed_name = render_obj(replayed, current_context)?;
        if let Some(previous) = result_context
            .symbol_names
            .insert(certified_symbol.id(), replayed_name.clone())
        {
            if previous != replayed_name {
                return Err(format!(
                    "Result-owned application alpha alias for `{certified}` is inconsistent"
                ));
            }
        }
        return Ok(true);
    }
    Runtime::same_shape_and_corresponding_args_match(
        certified,
        replayed,
        &mut |certified_child, replayed_child| {
            install_result_owned_application_alpha_aliases(
                certified_child,
                replayed_child,
                current_context,
                result_context,
            )
        },
    )
}

pub(in super::super) fn function_application_result_certificate_key(
    application: &StmtResultFunctionApplicationWellDefinednessToLeanCompilationContext,
) -> String {
    let anonymous_head = application
        .anonymous_function_head
        .as_ref()
        .map(obj_equality_key)
        .unwrap_or_default();
    let layers = application
        .layers
        .iter()
        .map(|layer| {
            let intrinsic_result_set = layer
                .intrinsic_result_set
                .as_ref()
                .map(obj_equality_key)
                .unwrap_or_default();
            let requirements = layer
                .requirements
                .iter()
                .map(|requirement| {
                    format!(
                        "{:?}:{}",
                        requirement.role, requirement.expected_proposition
                    )
                })
                .collect::<Vec<_>>()
                .join(";");
            format!(
                "{}:{:?}:{}:[{}]",
                obj_equality_key(&layer.source_prefix),
                layer.function_contracts,
                intrinsic_result_set,
                requirements
            )
        })
        .collect::<Vec<_>>()
        .join("|");
    format!(
        "{}:{:?}:{}:[{}]",
        obj_equality_key(&application.source_application),
        application.function_contracts,
        anonymous_head,
        layers
    )
}

pub(in super::super) fn resolve_function_application_result_context<'a>(
    application: &LeanTargetFunctionApplicationRepresentation,
    context: &'a StmtResultToLeanCompilerEnvironmentStack,
) -> Result<&'a StmtResultFunctionApplicationWellDefinednessToLeanCompilationContext, String> {
    let result_context = context
        .well_definedness
        .as_ref()
        .ok_or_else(|| "function application has no active Result-owned WD context".to_string())?;
    if let Some(exact) = result_context
        .function_applications
        .get(&application.source_occurrence_id)
    {
        return Ok(exact);
    }

    // A proof chain can repeat the identical source application in several
    // adjacent facts. Each parser occurrence is distinct, while a child
    // Result may retain only the occurrence used by its own fact. Reuse is
    // sound only when every matching active Result has the same complete
    // verifier certificate.
    let mut equivalent = Vec::new();
    for (occurrence_id, candidate) in &result_context.function_applications {
        if matches_directly_or_after_one_transparent_definition_pass(
            &candidate.source_application,
            &application.source_application,
            context,
        )? {
            equivalent.push((*occurrence_id, candidate));
        }
    }
    equivalent.sort_by_key(|(occurrence_id, _)| occurrence_id.value());
    let Some((_, first)) = equivalent.first().copied() else {
        let available_occurrences = result_context
            .function_applications
            .iter()
            .map(|(source_occurrence_id, application)| {
                format!(
                    "{}:{}",
                    source_occurrence_id.value(),
                    application.source_application
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        return Err(format!(
            "function application occurrence {} (`{}`) has no exact recursive Result context; active child occurrences are [{}]",
            application.source_occurrence_id.value(),
            application.source_application,
            available_occurrences,
        ));
    };
    let expected_certificate = function_application_result_certificate_key(first);
    if equivalent.iter().any(|(_, candidate)| {
        function_application_result_certificate_key(candidate) != expected_certificate
    }) {
        return Err(format!(
            "function application occurrence {} has multiple structurally matching but evidence-distinct Result contexts",
            application.source_occurrence_id.value()
        ));
    }
    Ok(first)
}

pub(in super::super) fn function_application_return_set_from_result(
    application: &LeanTargetFunctionApplicationRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<LeanTargetObjectRepresentation, String> {
    let application_context = resolve_function_application_result_context(application, context)?;
    let mut function = match application.head.as_ref() {
        LeanTargetObjectRepresentation::Symbol { .. } => {
            let [WellDefinedFunctionContract::StoredMembershipFact(contract_fact_id)] =
                application_context.function_contracts.as_slice()
            else {
                return Err(
                    "named real application requires one verifier-selected membership FactId"
                        .into(),
                );
            };
            context
                .function_bindings
                .get(contract_fact_id)
                .ok_or_else(|| {
                    let mut visible = context
                        .function_bindings
                        .keys()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>();
                    visible.sort();
                    format!(
                        "unavailable function membership FactId `{contract_fact_id}` for application `{}`; visible function contracts: [{}]",
                        application.source_application,
                        visible.join(", ")
                    )
                })?
                .function
                .clone()
        }
        LeanTargetObjectRepresentation::AnonymousFunction(anonymous) => {
            if !application_context.function_contracts.is_empty() {
                return Err(
                    "anonymous real application retained an unexpected named contract".into(),
                );
            }
            anonymous.function.clone()
        }
        _ => return Err("real application requires a named or anonymous function head".into()),
    };
    if application.argument_layers.len() != application_context.layers.len() {
        return Err("real application changed its Result-owned layer count".into());
    }
    for (layer_index, arguments) in application.argument_layers.iter().enumerate() {
        validate_function_type(&function)?;
        if arguments.len() != function.parameters.len() {
            return Err(format!(
                "real application layer {layer_index} changed its parameter arity"
            ));
        }
        if layer_index + 1 == application.argument_layers.len() {
            return Ok(function.return_set.as_ref().clone());
        }
        let LeanTargetObjectRepresentation::FunctionSet {
            function: next_function,
        } = function.return_set.as_ref()
        else {
            return Err(format!(
                "real application layer {layer_index} does not return its next callable layer"
            ));
        };
        function = next_function.as_ref().clone();
    }
    Err("real application retained no argument layers".into())
}

pub(in super::super) fn render_function_application(
    application: &LeanTargetFunctionApplicationRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if application.argument_layers.is_empty()
        || application.argument_layers.len() != application.source_argument_layers.len()
        || application
            .argument_layers
            .iter()
            .zip(application.source_argument_layers.iter())
            .any(|(arguments, source_arguments)| {
                arguments.is_empty() || arguments.len() != source_arguments.len()
            })
    {
        return Err(
            "compiler function application changed a retained source argument layer".into(),
        );
    }
    let Obj::FnObj(source_application) = &application.source_application else {
        return Err("function application retained a non-application source object".into());
    };
    let application_context = resolve_function_application_result_context(application, context)?;
    if !matches_result_owned_application_source(
        &application_context.source_application,
        &application.source_application,
        context,
    )? {
        return Err("function application Result context changed its source occurrence".into());
    }
    let mut result_owned_context = context.clone();
    if !install_result_owned_application_alpha_aliases(
        &application_context.source_application,
        &application.source_application,
        context,
        &mut result_owned_context,
    )? {
        return Err(
            "function application Result context could not align its alpha-renamed source".into(),
        );
    }

    let layer_count = application.argument_layers.len();
    if application_context.layers.len() != layer_count {
        return Err("function application Result context changed its layer count".into());
    }
    for (layer_index, layer_context) in application_context.layers.iter().enumerate() {
        let source_prefix = source_application.prefix_obj(layer_index + 1);
        if !matches_result_owned_application_source(
            &layer_context.source_prefix,
            &source_prefix,
            context,
        )? {
            return Err(format!(
                "application layer {layer_index} changed its verifier-owned source prefix"
            ));
        }
    }

    let root_contracts = application_context.function_contracts.clone();
    let (mut function, mut head, mut membership_proof, mut direct) = match application.head.as_ref()
    {
        LeanTargetObjectRepresentation::Symbol {
            symbol_id: head_symbol_id,
            ..
        } => {
            let [WellDefinedFunctionContract::StoredMembershipFact(contract_fact_id)] =
                root_contracts.as_slice()
            else {
                return Err(
                    "named application requires one verifier-selected membership FactId".into(),
                );
            };
            let binding = context
                .function_bindings
                .get(contract_fact_id)
                .ok_or_else(|| {
                    let mut visible = context
                        .function_bindings
                        .keys()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>();
                    visible.sort();
                    format!(
                        "unavailable function membership FactId `{contract_fact_id}` for application `{source_application}`; visible function contracts: [{}]",
                        visible.join(", ")
                    )
                })?;
            if *head_symbol_id != binding.symbol_id {
                let definition = context
                    .transparent_object_definitions
                    .get(head_symbol_id)
                    .ok_or_else(|| {
                        "function membership FactId belongs to another head symbol".to_string()
                    })?;
                let retained_fact = context
                    .fact_propositions
                    .get(&definition.defining_equality_fact_id)
                    .ok_or_else(|| {
                        "transparent callable alias lost its defining equality FactId".to_string()
                    })?;
                if retained_fact.to_string() != definition.defining_equality.to_string()
                    || !context
                        .fact_names
                        .contains_key(&definition.defining_equality_fact_id)
                {
                    return Err(
                        "transparent callable alias changed its defining equality citation".into(),
                    );
                }
                let lowered_definition = LeanTargetObjectRepresentation::lower(&definition.value)?;
                if !matches!(
                    lowered_definition,
                    LeanTargetObjectRepresentation::Symbol { symbol_id, .. }
                        if symbol_id == binding.symbol_id
                ) {
                    return Err(
                        "transparent callable alias does not reduce once to the selected function contract"
                            .into(),
                    );
                }
            }
            if binding.direct {
                let exact_head = context
                    .exact_carrier_values
                    .get(&binding.symbol_id)
                    .cloned()
                    .unwrap_or(render_ir_symbol(application.head.as_ref(), context)?);
                let function_set = render_function_set(&binding.function, context)?;
                (
                    binding.function.clone(),
                    exact_head.clone(),
                    format!("(Litex.In.own {function_set} {exact_head})"),
                    true,
                )
            } else {
                (
                    binding.function.clone(),
                    render_ir_symbol(application.head.as_ref(), context)?,
                    binding.membership_proof_name.clone(),
                    binding.direct,
                )
            }
        }
        LeanTargetObjectRepresentation::AnonymousFunction(anonymous) => {
            if !root_contracts.is_empty() {
                return Err("anonymous application retained an unexpected named contract".into());
            }
            let head_object = application_context
                .anonymous_function_head
                .as_ref()
                .ok_or_else(|| {
                    "anonymous application requires one exact FunctionHead child Result".to_string()
                })?;
            if obj_equality_key(head_object) != anonymous.semantic_key {
                return Err("anonymous application changed its verifier-owned head".into());
            }
            let head = render_anonymous_function(anonymous, context)?;
            let function_set = render_function_set(&anonymous.function, context)?;
            (
                anonymous.function.clone(),
                head.clone(),
                format!("(Litex.In.own {function_set} {head})"),
                true,
            )
        }
        _ => return Err("compiler function application requires a named or anonymous head".into()),
    };
    let mut layer_lets = Vec::new();
    for layer_index in 0..layer_count {
        validate_function_type(&function)?;
        let layer_context = &application_context.layers[layer_index];
        if layer_context.function_contracts != root_contracts {
            return Err(format!(
                "application layer {layer_index} changed its root function contract"
            ));
        }
        if function.parameters.len() != application.argument_layers[layer_index].len() {
            return Err(format!(
                "application layer {layer_index} expected {} parameters, retained {} arguments",
                function.parameters.len(),
                application.argument_layers[layer_index].len()
            ));
        }
        for (source_argument, retained_argument) in application.source_argument_layers[layer_index]
            .iter()
            .zip(application.argument_layers[layer_index].iter())
        {
            if LeanTargetObjectRepresentation::lower(source_argument)? != *retained_argument {
                return Err(format!(
                    "application layer {layer_index} changed its retained argument IR"
                ));
            }
        }

        let mut argument_requirements = vec![None; function.parameters.len()];
        let mut domain_requirements = vec![None; function.domain_facts.len()];
        for requirement in &layer_context.requirements {
            match requirement.role {
                WellDefinednessRequirementRole::FunctionArgumentMembership {
                    layer_index: retained_layer_index,
                    parameter_index,
                } if retained_layer_index == layer_index
                    && parameter_index < argument_requirements.len() =>
                {
                    if argument_requirements[parameter_index]
                        .replace(requirement)
                        .is_some()
                    {
                        return Err(format!(
                            "application layer {layer_index} retained duplicate argument-membership requirement {parameter_index}"
                        ));
                    }
                }
                WellDefinednessRequirementRole::FunctionDomain {
                    layer_index: retained_layer_index,
                    domain_index,
                } if retained_layer_index == layer_index
                    && domain_index < domain_requirements.len() =>
                {
                    if domain_requirements[domain_index]
                        .replace(requirement)
                        .is_some()
                    {
                        return Err(format!(
                            "application layer {layer_index} retained duplicate domain requirement {domain_index}"
                        ));
                    }
                }
                role => {
                    return Err(format!(
                        "application layer {layer_index} retained an unexpected target requirement {role:?}"
                    ));
                }
            }
        }
        if argument_requirements.iter().any(Option::is_none) {
            return Err(format!(
                "application layer {layer_index} lost a checked argument-membership requirement"
            ));
        }
        if domain_requirements.iter().any(Option::is_none) {
            return Err(format!(
                "application layer {layer_index} lost a checked source-domain requirement"
            ));
        }
        let mut nested = context.clone();
        // Domain verification in Result is about the original source
        // arguments. The target telescope may separately observe a
        // heterogeneous parameter through its membership proof, so keep a
        // source-facing rendering context for exact Result validation.
        let mut source_domain_nested = context.clone();
        let mut arguments = Vec::with_capacity(function.parameters.len());
        let mut argument_memberships = Vec::with_capacity(function.parameters.len());
        for (_parameter_index, ((parameter, source_argument), requirement)) in function
            .parameters
            .iter()
            .zip(application.source_argument_layers[layer_index].iter())
            .zip(argument_requirements.into_iter())
            .enumerate()
        {
            let requirement = requirement.expect("argument requirements checked above");
            let argument = render_obj(source_argument, context)?;
            let expected_argument_membership = format!(
                "Litex.In {argument} {}",
                render_lean_source_for_target_set_representation(&parameter.set, &nested)?
            );
            let retained_argument_membership =
                render_fact(&requirement.expected_proposition, &result_owned_context)?;
            if retained_argument_membership != expected_argument_membership {
                return Err(format!(
                    "application layer {layer_index} expected `{expected_argument_membership}`, retained `{retained_argument_membership}`"
                ));
            }
            let argument_membership =
                render_function_application_requirement_proof(requirement, &result_owned_context)?;
            let (call_argument, call_membership) = if parameter.set
                == LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer)
            {
                let integer = render_integer_obj(source_argument, context).or_else(|_| {
                    membership_integer_value(&parameter.set, &argument, &argument_membership)
                        .ok_or_else(|| {
                            "integer function argument lost its exact representative".to_string()
                        })
                })?;
                (integer.clone(), format!("Litex.In.own Litex.Z {integer}"))
            } else {
                (argument.clone(), argument_membership.clone())
            };
            arguments.push(call_argument);
            argument_memberships.push(call_membership);
            nested
                .symbol_names
                .insert(parameter.symbol_id, argument.clone());
            source_domain_nested
                .symbol_names
                .insert(parameter.symbol_id, argument.clone());
            source_domain_nested
                .numeric_representations
                .insert(parameter.symbol_id, argument.clone());
            if let Some(real) = membership_real_value(
                &parameter.set,
                arguments.last().expect("argument was just retained"),
                &argument_membership,
            ) {
                nested.numeric_real_values.insert(parameter.symbol_id, real);
            }
            if let Some(integer) = membership_integer_value(
                &parameter.set,
                arguments.last().expect("argument was just retained"),
                &argument_membership,
            ) {
                nested
                    .numeric_integer_values
                    .insert(parameter.symbol_id, integer);
            }
            if let Some(rational) = membership_rational_value(
                &parameter.set,
                arguments.last().expect("argument was just retained"),
                &argument_membership,
            ) {
                nested
                    .numeric_rational_values
                    .insert(parameter.symbol_id, rational);
            }
            if let Some(representation) = membership_numeric_value(
                &parameter.set,
                arguments.last().expect("argument was just retained"),
                &argument_membership,
            ) {
                nested
                    .numeric_representations
                    .insert(parameter.symbol_id, representation);
            }
            if let Some(proof) = membership_numeric_proof(
                &parameter.set,
                arguments.last().expect("argument was just retained"),
                &argument_membership,
            ) {
                nested
                    .numeric_representation_memberships
                    .insert(parameter.symbol_id, proof);
            }
        }
        let mut domain_proofs = Vec::with_capacity(domain_requirements.len());
        for (_domain_index, (source_fact, requirement)) in function
            .domain_facts
            .iter()
            .zip(domain_requirements.into_iter())
            .enumerate()
        {
            let requirement = requirement.expect("domain requirements checked above");
            let expected_source = render_fact(source_fact, &source_domain_nested)?;
            let expected_selected = render_fact(source_fact, &nested)?;
            let retained = render_fact(&requirement.expected_proposition, &result_owned_context)?;
            if expected_source != retained && expected_selected != retained {
                return Err(format!(
                    "application layer {layer_index} expected domain clause {expected_source} (or exact selected-carrier form {expected_selected}), retained {retained}"
                ));
            }
            let retained_proof =
                render_function_application_requirement_proof(requirement, &result_owned_context)?;
            if positive_natural_parameter_less_equal_natural_bound(&function, source_fact)?
                .is_some()
            {
                domain_proofs.push(format!(
                    "Litex.positiveNaturalParameterLessEqualNaturalBoundOfComplex ({retained_proof})"
                ));
            } else {
                domain_proofs.push(retained_proof);
            }
        }

        let application_term = if !function_uses_telescope(&function) {
            let exact_integer_argument = function.domain_facts.is_empty()
                && function.parameters.len() == 1
                && function.parameters[0].set
                    == LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer);
            if exact_integer_argument {
                let apply = if direct {
                    "Litex.fnApplyCarrier"
                } else {
                    "Litex.fnApplySelectedCarrier"
                };
                format!("({apply} {head} {membership_proof} {})", arguments[0])
            } else {
                let apply = match (direct, domain_proofs.is_empty()) {
                    (true, true) => "Litex.fnApplyOwn",
                    (false, true) => "Litex.fnApply",
                    (true, false) => "Litex.fnApplyWhereOwn",
                    (false, false) => "Litex.fnApplyWhere",
                };
                let argument = &arguments[0];
                let argument_membership = &argument_memberships[0];
                if domain_proofs.is_empty() {
                    format!(
                        "({apply} {head} {membership_proof} {argument} ({argument_membership}))"
                    )
                } else {
                    let domain_proof = if domain_proofs.len() == 1 {
                        domain_proofs[0].clone()
                    } else {
                        format!("⟨{}⟩", domain_proofs.join(", "))
                    };
                    format!(
                    "({apply} {head} {membership_proof} {argument} ({argument_membership}) ({domain_proof}))"
                )
                }
            }
        } else {
            let apply = if direct {
                "Litex.fnTelescopeApplyOwn"
            } else {
                "Litex.fnTelescopeApply"
            };
            let mut term = format!("({apply} {head} {membership_proof})");
            for (argument, argument_membership) in arguments.iter().zip(argument_memberships.iter())
            {
                term = format!("({term} {argument} ({argument_membership}))");
            }
            if !domain_proofs.is_empty() {
                let domain_proof = if domain_proofs.len() == 1 {
                    domain_proofs[0].clone()
                } else {
                    format!("⟨{}⟩", domain_proofs.join(", "))
                };
                term = format!("({term} ({domain_proof}))");
            }
            format!("({term}).down")
        };

        if layer_index + 1 == layer_count {
            head = application_term;
            continue;
        }
        let LeanTargetObjectRepresentation::FunctionSet {
            function: next_function,
        } = function.return_set.as_ref()
        else {
            return Err(format!(
                "application layer {layer_index} does not return the next function set"
            ));
        };
        let retained_result_set = layer_context.intrinsic_result_set.as_ref().ok_or_else(|| {
            format!("application layer {layer_index} lost its Result-owned intrinsic result set")
        })?;
        if LeanTargetObjectRepresentation::lower(retained_result_set)? != *function.return_set {
            return Err(format!(
                "application layer {layer_index} lost its exact verifier-owned result set"
            ));
        }
        let next_function_set = render_function_set(next_function, context)?;
        let layer_name = format!("__fn_layer{}", layer_index + 1);
        layer_lets.push(format!("(let {layer_name} := {application_term}; "));
        head = layer_name;
        membership_proof = format!("(Litex.In.own {next_function_set} {head})");
        function = next_function.as_ref().clone();
        direct = true;
    }
    Ok(format!(
        "{}{}{}",
        layer_lets.concat(),
        head,
        ")".repeat(layer_lets.len())
    ))
}
