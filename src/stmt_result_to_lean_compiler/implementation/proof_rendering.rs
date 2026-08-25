use super::*;

pub(super) fn construct_lean_source_parts_for_abstract_predicate_definition(
    source_name: &str,
    parameter_names: &[String],
    declarations: &mut Vec<String>,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    if context.predicate_bindings.contains_key(source_name) {
        return Err(format!(
            "duplicate compiler predicate definition `{}`",
            source_name
        ));
    }
    let name = lean_identifier(source_name);
    let mut universe_names = Vec::with_capacity(parameter_names.len());
    let mut binders = Vec::with_capacity(parameter_names.len() * 2);
    for (index, parameter_name) in parameter_names.iter().enumerate() {
        let suffix = index + 1;
        let universe = format!("u__{name}_{suffix}");
        let carrier = format!("__abstract_carrier{suffix}");
        universe_names.push(universe.clone());
        binders.push(format!("{{{carrier} : Type {universe}}}"));
        binders.push(format!("({} : {carrier})", lean_identifier(parameter_name)));
    }
    let universe_declaration = if universe_names.is_empty() {
        String::new()
    } else {
        format!("universe {}\n", universe_names.join(" "))
    };
    let binder_suffix = if binders.is_empty() {
        String::new()
    } else {
        format!(" {}", binders.join(" "))
    };
    declarations.push(format!(
        "{universe_declaration}axiom {name}{binder_suffix} : Prop"
    ));
    context.predicate_bindings.insert(
        source_name.to_string(),
        PredicateBinding {
            lean_name: name,
            parameter_count: parameter_names.len(),
            requirement_count: 0,
            clause_count: 0,
            definition: None,
        },
    );
    Ok(())
}

pub(super) fn object_is_symbol(object: &Obj, symbol_id: SymbolId) -> bool {
    matches!(object, Obj::Atom(atom) if atom.symbol_ref().is_some_and(|symbol| symbol.id() == symbol_id))
}

pub(super) fn indexed_tuple_value_is_complex(
    object: &LeanTargetObjectRepresentation,
    index: SymbolId,
) -> bool {
    match object {
        LeanTargetObjectRepresentation::Number { .. }
        | LeanTargetObjectRepresentation::Constant(_) => true,
        LeanTargetObjectRepresentation::Symbol { symbol_id, .. } => *symbol_id == index,
        LeanTargetObjectRepresentation::BuiltinApp {
            operator,
            arguments,
            ..
        } if matches!(
            operator,
            LeanTargetBuiltinObjectOperator::Add
                | LeanTargetBuiltinObjectOperator::Sub
                | LeanTargetBuiltinObjectOperator::Mul
                | LeanTargetBuiltinObjectOperator::Div
        ) =>
        {
            arguments
                .iter()
                .all(|argument| indexed_tuple_value_is_complex(argument, index))
        }
        _ => false,
    }
}

pub(super) fn render_set_definition_value(
    value: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match value {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
            Ok("Litex.R".into())
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Complex) => {
            Ok("Litex.C".into())
        }
        LeanTargetObjectRepresentation::SetBuilder(_) => {
            render_lean_source_for_target_set_representation(value, context)
        }
        LeanTargetObjectRepresentation::FunctionSet { .. } => {
            render_lean_source_for_target_set_representation(value, context)
        }
        _ => Err(format!(
            "unsupported compiler named set definition value `{value:?}`"
        )),
    }
}

pub(super) fn render_forall_fact_type(
    forall: &ForallFact,
    outer_context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let mut context = outer_context.clone();
    let mut binders = Vec::new();
    for (index, (binding, param_type)) in forall
        .typed_parameters
        .collect_param_bindings_with_types()
        .iter()
        .enumerate()
    {
        let name = format!("__p{}", index + 1);
        context.symbol_names.insert(binding.id(), name.clone());
        if matches!(param_type, ParamType::Set(_)) {
            binders.push(format!("({name} : Litex.Set)"));
            continue;
        }
        if matches!(
            param_type,
            ParamType::NonemptySet(_) | ParamType::FiniteSet(_)
        ) {
            binders.push(format!("({name} : Litex.Set)"));
            let property = match param_type {
                ParamType::NonemptySet(_) => "Litex.Set.Nonempty",
                ParamType::FiniteSet(_) => "Litex.Set.Finite",
                _ => unreachable!("refined-set branch checked above"),
            };
            binders.push(format!("(__type{} : {property} {name})", index + 1));
            let expected = match param_type {
                ParamType::NonemptySet(_) => {
                    format!("Litex.Set.Nonempty {name}")
                }
                ParamType::FiniteSet(_) => format!("Litex.Set.Finite {name}"),
                _ => unreachable!("refined-set branch checked above"),
            };
            install_rendered_parameter_aliases(
                binding.id(),
                &expected,
                &format!("__type{}", index + 1),
                None,
                &mut context,
            )?;
            install_result_owned_forall_parameter_fact_alias(
                binding.id(),
                &expected,
                &format!("__type{}", index + 1),
                &mut context,
            )?;
            continue;
        }

        let set = parameter_set(param_type)?;
        let carrier = format!("__carrier{}", index + 1);
        match set {
            Obj::FnSet(_) => {
                binders.push(format!("{{{carrier} : Type 1}}"));
                binders.push(format!("({name} : {carrier})"));
            }
            set if set_requires_heterogeneous_carrier(set) => {
                binders.push(format!("{{{carrier} : Type}}"));
                binders.push(format!("({name} : {carrier})"));
            }
            _ => binders.push(format!("({name} : ℂ)")),
        }
        binders.push(format!(
            "(__type{} : Litex.In {name} {})",
            index + 1,
            render_obj(set, &context)?
        ));
        let expected = format!("Litex.In {name} {}", render_obj(set, &context)?);
        install_rendered_parameter_aliases(
            binding.id(),
            &expected,
            &format!("__type{}", index + 1),
            match set {
                Obj::FnSet(function) => {
                    Some(LeanTargetFunctionTypeRepresentation::lower(function)?)
                }
                _ => None,
            },
            &mut context,
        )?;
        install_result_owned_forall_parameter_fact_alias(
            binding.id(),
            &expected,
            &format!("__type{}", index + 1),
            &mut context,
        )?;
        let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
        if let Some(real) =
            membership_real_value(&lowered_set, &name, &format!("__type{}", index + 1))
        {
            context.numeric_real_values.insert(binding.id(), real);
        }
        if let Some(integer) =
            membership_integer_value(&lowered_set, &name, &format!("__type{}", index + 1))
        {
            context.numeric_integer_values.insert(binding.id(), integer);
        }
        if let Some(rational) =
            membership_rational_value(&lowered_set, &name, &format!("__type{}", index + 1))
        {
            context
                .numeric_rational_values
                .insert(binding.id(), rational);
        }
        if let Some(representation) =
            membership_numeric_value(&lowered_set, &name, &format!("__type{}", index + 1))
        {
            context
                .numeric_representations
                .insert(binding.id(), representation);
        }
        if let Some(equality) =
            membership_numeric_equality(&lowered_set, &name, &format!("__type{}", index + 1))
        {
            context
                .numeric_representation_equalities
                .insert(binding.id(), equality);
        }
        if let Some(proof) =
            membership_numeric_proof(&lowered_set, &name, &format!("__type{}", index + 1))
        {
            context
                .numeric_representation_memberships
                .insert(binding.id(), proof);
        }
    }
    for (index, premise) in forall.dom_facts.iter().enumerate() {
        binders.push(format!(
            "(__domain{} : {})",
            index + 1,
            render_fact(premise, &context)?
        ));
    }
    let conclusions = forall
        .then_facts
        .iter()
        .map(|conclusion| render_fact(&conclusion.clone().to_fact(), &context))
        .collect::<Result<Vec<_>, _>>()?;
    if conclusions.is_empty() {
        return Err("forall citation retained no conclusions".into());
    }
    Ok(format!(
        "∀ {}, {}",
        binders.join(" "),
        conjunction(&conclusions)
    ))
}

/// While rendering a nested forall type, connect the textual binder
/// hypothesis to the exact parameter FactId retained by the recursive WD
/// Result. The Result context can contain aliases from several lexical
/// binders, so SymbolId is the structural discriminator; no proposition-based
/// environment lookup is performed.
pub(super) fn install_result_owned_forall_parameter_fact_alias(
    symbol_id: SymbolId,
    expected_rendered_proposition: &str,
    proof_name: &str,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let aliases = context
        .well_definedness
        .as_ref()
        .map(|well_definedness| {
            well_definedness
                .parameter_fact_aliases
                .iter()
                .filter(|alias| alias.symbol_id == symbol_id)
                .cloned()
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    for alias in aliases {
        let rendered = render_fact(&alias.proposition, context)?;
        if rendered != expected_rendered_proposition {
            return Err(format!(
                "forall parameter SymbolId `{symbol_id:?}` changed its Result-owned proposition from `{rendered}` to `{expected_rendered_proposition}`"
            ));
        }
        context
            .fact_names
            .insert(alias.fact_id, proof_name.to_string());
        context
            .fact_propositions
            .insert(alias.fact_id, alias.proposition);
    }
    Ok(())
}

pub(super) fn install_parameter_fact_aliases(
    symbol_id: SymbolId,
    proposition: &Fact,
    proof_name: &str,
    set: &Obj,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let function = match set {
        Obj::FnSet(function) => Some(LeanTargetFunctionTypeRepresentation::lower(function)?),
        _ => None,
    };
    let expected = render_fact(proposition, context)?;
    install_rendered_parameter_aliases(symbol_id, &expected, proof_name, function, context)?;

    // Integer-only target operators cannot be applied to the ordinary
    // Complex view used by Litex arithmetic. Retain the exact representative
    // selected by this parameter's membership proof in the current compiler
    // frame; child lexical frames inherit it and pop discards it.
    let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
    let source_name = context
        .symbol_names
        .get(&symbol_id)
        .cloned()
        .ok_or_else(|| "parameter alias has no visible compiler symbol".to_string())?;
    if let Some(real) = membership_real_value(&lowered_set, &source_name, proof_name) {
        context.numeric_real_values.insert(symbol_id, real);
    }
    if let Some(integer) = membership_integer_value(&lowered_set, &source_name, proof_name) {
        context.numeric_integer_values.insert(symbol_id, integer);
    }
    if let Some(rational) = membership_rational_value(&lowered_set, &source_name, proof_name) {
        context.numeric_rational_values.insert(symbol_id, rational);
    }
    if let Some(representation) = membership_numeric_value(&lowered_set, &source_name, proof_name) {
        context
            .numeric_representations
            .insert(symbol_id, representation);
    }
    if let Some(equality) = membership_numeric_equality(&lowered_set, &source_name, proof_name) {
        context
            .numeric_representation_equalities
            .insert(symbol_id, equality);
    }
    if let Some(proof) = membership_numeric_proof(&lowered_set, &source_name, proof_name) {
        context
            .numeric_representation_memberships
            .insert(symbol_id, proof);
    }
    Ok(())
}

pub(super) fn install_numeric_representations_from_membership(
    symbol_id: SymbolId,
    set: &LeanTargetObjectRepresentation,
    source_name: &str,
    proof_name: &str,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) {
    if let Some(real) = membership_real_value(set, source_name, proof_name) {
        context.numeric_real_values.insert(symbol_id, real);
    }
    if let Some(integer) = membership_integer_value(set, source_name, proof_name) {
        context.numeric_integer_values.insert(symbol_id, integer);
    }
    if let Some(rational) = membership_rational_value(set, source_name, proof_name) {
        context.numeric_rational_values.insert(symbol_id, rational);
    }
    if let Some(representation) = membership_numeric_value(set, source_name, proof_name) {
        context
            .numeric_representations
            .insert(symbol_id, representation);
    }
    if let Some(equality) = membership_numeric_equality(set, source_name, proof_name) {
        context
            .numeric_representation_equalities
            .insert(symbol_id, equality);
    }
    if let Some(proof) = membership_numeric_proof(set, source_name, proof_name) {
        context
            .numeric_representation_memberships
            .insert(symbol_id, proof);
    }
}

pub(super) fn install_rendered_parameter_aliases(
    symbol_id: SymbolId,
    expected: &str,
    proof_name: &str,
    function: Option<LeanTargetFunctionTypeRepresentation>,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let aliases = context
        .well_definedness
        .as_ref()
        .map(|result_context| result_context.parameter_fact_aliases.clone())
        .unwrap_or_default();
    for alias in aliases {
        if alias.symbol_id != symbol_id || render_fact(&alias.proposition, context)? != expected {
            continue;
        }
        context
            .fact_names
            .insert(alias.fact_id, proof_name.to_string());
        context
            .fact_propositions
            .insert(alias.fact_id, alias.proposition.clone());
        if let Some(function) = &function {
            context.function_bindings.insert(
                alias.fact_id,
                FunctionBinding {
                    symbol_id,
                    function: function.clone(),
                    membership_proof_name: proof_name.to_string(),
                    direct: false,
                },
            );
        }
    }
    Ok(())
}

pub(super) fn facts_align_by_nested_rational_normalization_for_result_compiler(
    source: &Fact,
    target: &Fact,
) -> bool {
    let (Fact::AtomicFact(source), Fact::AtomicFact(target)) = (source, target) else {
        return false;
    };
    if source.key() != target.key()
        || source.has_positive_polarity() != target.has_positive_polarity()
    {
        return false;
    }
    let source_arguments = source.args_ref();
    let target_arguments = target.args_ref();
    source_arguments.len() == target_arguments.len()
        && source_arguments
            .iter()
            .zip(target_arguments.iter())
            .all(|(source, target)| {
                objects_align_by_nested_rational_normalization_for_result_compiler(source, target)
            })
}

pub(super) fn objects_align_by_nested_rational_normalization_for_result_compiler(
    source: &Obj,
    target: &Obj,
) -> bool {
    if objs_equal_by_rational_expression_evaluation(source, target) {
        return true;
    }
    let comparison: Result<bool, ()> = Runtime::same_shape_and_corresponding_args_match(
        source,
        target,
        &mut |source_argument, target_argument| {
            Ok(
                objects_align_by_nested_rational_normalization_for_result_compiler(
                    source_argument,
                    target_argument,
                ),
            )
        },
    );
    comparison.unwrap_or(false)
}

pub(super) fn render_checked_identity_function_reduction_from_fact(
    target: &Fact,
    defining_equality_fact_id: crate::common::fact_id::FactId,
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
    let apply = if function_uses_telescope(&binding.function) {
        "Litex.fnTelescopeApplyOwn"
    } else if binding.function.domain_facts.is_empty() {
        "Litex.fnApplyOwn"
    } else {
        "Litex.fnApplyWhereOwn"
    };
    if binding.uses_native_real_body {
        let body_same = render_real_function_body_same_with_parameters(
            &binding.body,
            &argument_evidence,
            context,
        )?;
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

pub(super) fn render_real_function_body_same_with_parameters(
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

pub(super) fn instantiated_predicate_components(
    source: &Fact,
    binding: &PredicateBinding,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<Vec<String>, String> {
    let definition = binding
        .definition
        .as_ref()
        .ok_or_else(|| "an abstract predicate has no reducible definition".to_string())?;
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(source)) = source else {
        return Err("concrete predicate component expansion requires a predicate fact".into());
    };
    if source.predicate.to_string() != definition.name
        || source.body.len() != binding.parameter_count
    {
        return Err("concrete predicate component expansion changed its application".into());
    }
    let mut nested = context.clone();
    let mut argument_index = 0;
    for group in &definition.typed_parameters.groups {
        for parameter in &group.params {
            nested.symbol_names.insert(
                parameter.id(),
                render_obj(&source.body[argument_index], context)?,
            );
            argument_index += 1;
        }
    }
    let mut components = Vec::new();
    argument_index = 0;
    for group in &definition.typed_parameters.groups {
        for _ in &group.params {
            match &group.param_type {
                ParamType::Set(_) => components.push("True".to_string()),
                ParamType::Obj(set) => {
                    let argument = render_obj(&source.body[argument_index], context)?;
                    components.push(format!("Litex.In {argument} {}", render_obj(set, &nested)?));
                }
                unsupported => {
                    return Err(format!(
                        "concrete predicate component compiler does not support parameter type `{unsupported}`"
                    ));
                }
            }
            argument_index += 1;
        }
    }
    components.extend(
        definition
            .iff_facts
            .iter()
            .map(|fact| render_fact(fact, &nested))
            .collect::<Result<Vec<_>, _>>()?,
    );
    Ok(components)
}

pub(super) fn conjunction_selector(index: usize, count: usize) -> Result<String, String> {
    if count == 0 || index >= count {
        return Err("invalid conjunction projection index".into());
    }
    if count == 1 {
        return Ok(String::new());
    }
    if index == 0 {
        return Ok(".1".into());
    }
    if index == count - 1 {
        return Ok(".2".repeat(index));
    }
    Ok(format!("{}.1", ".2".repeat(index)))
}

pub(super) fn render_set_builder_membership_from_fact_and_proofs(
    target: &Fact,
    premises: &[(Fact, String)],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (_, target_set) = membership_parts(target)?;
    let set_builder = LeanTargetObjectRepresentation::lower(target_set)?;
    let LeanTargetObjectRepresentation::SetBuilder(builder) = set_builder else {
        return Err("set-builder membership retained a non-builder object".into());
    };
    if premises.len() != builder.facts.len() + 1 {
        return Err("set-builder membership lost its base or predicate premises".into());
    }
    let (element, _) = membership_parts(target)?;
    let (base_element, base_set) = membership_parts(&premises[0].0)?;
    if obj_equality_key(element) != obj_equality_key(base_element)
        || LeanTargetObjectRepresentation::lower(base_set)? != *builder.set
    {
        return Err("set-builder membership changed its base-membership premise".into());
    }
    let base_proof = premises[0].1.clone();
    let rendered_element = render_obj(element, context)?;
    let representative = format!("Litex.In.rep {rendered_element} ({base_proof})");
    let mut nested = context.clone();
    nested
        .symbol_names
        .insert(builder.symbol_id, representative.clone());

    let mut predicate_proofs = Vec::with_capacity(builder.facts.len());
    let mut source = context.clone();
    source
        .symbol_names
        .insert(builder.symbol_id, rendered_element.clone());
    let representative_same = format!("Litex.In.same_rep {rendered_element} ({base_proof})");
    for (index, fact) in builder.facts.iter().enumerate() {
        let premise = &premises[index + 1];
        if render_fact(fact, &source)? != render_fact(&premise.0, context)? {
            return Err(
                "set-builder predicate premise changed its checked binder substitution".into(),
            );
        }
        let source_proof = premise.1.clone();
        let proof = match fact {
            Fact::AtomicFact(AtomicFact::EqualFact(equality)) => {
                render_equality_across_representative(
                    equality,
                    &source,
                    &nested,
                    &rendered_element,
                    &representative,
                    &representative_same,
                    &source_proof,
                )?
            }
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(predicate)) => {
                if predicate.body.len() != 1 {
                    return Err(
                        "set-builder concrete predicate transport requires one argument".into(),
                    );
                }
                let predicate_name = predicate.predicate.to_string();
                let binding = context
                    .predicate_bindings
                    .get(&predicate_name)
                    .ok_or_else(|| {
                        format!("unavailable concrete set-builder predicate {predicate_name}")
                    })?;
                if binding.parameter_count != 1 || binding.requirement_count != 1 {
                    return Err(
                        "set-builder concrete predicate transport requires one member parameter"
                            .into(),
                    );
                }
                let argument_source = render_obj(&predicate.body[0], &source)?;
                let argument_target = render_obj(&predicate.body[0], &nested)?;
                if argument_source != rendered_element || argument_target != representative {
                    return Err("set-builder concrete predicate changed its binder argument".into());
                }
                let definition = binding.definition.as_ref().ok_or_else(|| {
                    "abstract set-builder predicates have no transport definition".to_string()
                })?;
                let group = definition
                    .typed_parameters
                    .groups
                    .first()
                    .ok_or_else(|| "concrete predicate lost its parameter group".to_string())?;
                let [definition_parameter] = group.params.as_slice() else {
                    return Err(
                        "set-builder concrete predicate requires one definition parameter".into(),
                    );
                };
                let set = parameter_set(&group.param_type)?;
                let component_count = binding.requirement_count + definition.iff_facts.len();
                let membership_selector = conjunction_selector(0, component_count)?;
                let rendered_set = render_obj(set, context)?;
                let mut component_proofs = vec![format!(
                    "(Litex.In.congr ({representative_same}) {rendered_set}).mp (__source{membership_selector})"
                )];
                let mut clause_source = context.clone();
                clause_source
                    .symbol_names
                    .insert(definition_parameter.id(), rendered_element.clone());
                let mut clause_target = context.clone();
                clause_target
                    .symbol_names
                    .insert(definition_parameter.id(), representative.clone());
                for (clause_index, clause) in definition.iff_facts.iter().enumerate() {
                    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = clause else {
                        return Err(
                            "set-builder concrete predicate currently transports equality clauses"
                                .into(),
                        );
                    };
                    let selector = conjunction_selector(
                        binding.requirement_count + clause_index,
                        component_count,
                    )?;
                    component_proofs.push(render_equality_across_representative(
                        equality,
                        &clause_source,
                        &clause_target,
                        &rendered_element,
                        &representative,
                        &representative_same,
                        &format!("__source{selector}"),
                    )?);
                }
                format!(
                    "(by\n  have __source := {source_proof}\n  unfold {} at __source ⊢\n  exact ⟨{}⟩)",
                    binding.lean_name,
                    component_proofs.join(", ")
                )
            }
            _ => {
                return Err(
                    "compiler set-builder membership currently transports equality clauses or one-parameter concrete predicates"
                        .into(),
                );
            }
        };
        predicate_proofs.push(proof);
    }
    let predicate_proof = if predicate_proofs.len() == 1 {
        predicate_proofs[0].clone()
    } else {
        format!("⟨{}⟩", predicate_proofs.join(", "))
    };
    Ok(format!(
        "Litex.Rules.inSetBuilder (Litex.In.same_rep {rendered_element} ({base_proof})) ({predicate_proof})"
    ))
}

pub(super) fn render_equality_across_representative(
    equality: &EqualFact,
    source: &StmtResultToLeanCompilerEnvironmentStack,
    target: &StmtResultToLeanCompilerEnvironmentStack,
    source_value: &str,
    target_value: &str,
    source_same_target: &str,
    source_proof: &str,
) -> Result<String, String> {
    let source_left = render_obj(&equality.left, source)?;
    let source_right = render_obj(&equality.right, source)?;
    let target_left = render_obj(&equality.left, target)?;
    let target_right = render_obj(&equality.right, target)?;
    let left_changed = source_left == source_value && target_left == target_value;
    let right_changed = source_right == source_value && target_right == target_value;
    match (left_changed, right_changed) {
        (true, true) => Ok(format!("Litex.Same.refl ({target_value})")),
        (true, false) if source_right == target_right => Ok(format!(
            "Litex.Same.trans (Litex.Same.symm ({source_same_target})) ({source_proof})"
        )),
        (false, true) if source_left == target_left => Ok(format!(
            "Litex.Same.trans ({source_proof}) ({source_same_target})"
        )),
        (false, false) if source_left == target_left && source_right == target_right => {
            Ok(source_proof.into())
        }
        _ => Err(
            "compiler equality transport requires the changing value as a whole equality side"
                .into(),
        ),
    }
}

pub(super) fn render_set_builder_predicate_projection_from_fact_and_proof(
    target: &Fact,
    clause_index: usize,
    source: &Fact,
    source_proof: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (_, source_set) = membership_parts(source)?;
    let set_builder = LeanTargetObjectRepresentation::lower(source_set)?;
    let LeanTargetObjectRepresentation::SetBuilder(builder) = set_builder else {
        return Err("set-builder predicate projection retained a non-builder object".into());
    };
    let clause = builder
        .facts
        .get(clause_index)
        .ok_or_else(|| "set-builder predicate projection index is out of range".to_string())?;
    let (element, _) = membership_parts(source)?;
    let rendered_element = render_obj(element, context)?;
    let predicate_selector = conjunction_selector(clause_index, builder.facts.len())?;
    if let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = clause {
        let mut representative_context = context.clone();
        representative_context
            .symbol_names
            .insert(builder.symbol_id, "__rep".into());
        let mut element_context = context.clone();
        element_context
            .symbol_names
            .insert(builder.symbol_id, rendered_element.clone());
        if render_fact(clause, &element_context)? != render_fact(target, context)? {
            return Err("set-builder equality projection changed its instantiated clause".into());
        }
        let transported = render_equality_across_representative(
            equality,
            &representative_context,
            &element_context,
            "__rep",
            &rendered_element,
            "Litex.Same.symm __same",
            "__selected",
        )?;
        return Ok(format!(
            "(by\n  rcases Litex.Rules.inSetBuilder_iff.mp ({source_proof}) with ⟨__rep, __predicate, __same⟩\n  have __selected := __predicate{predicate_selector}\n  exact {transported})"
        ));
    }
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(predicate)) = clause else {
        return Err(
            "set-builder predicate projection currently supports equality or concrete predicate clauses"
                .into(),
        );
    };
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(target_predicate)) = target else {
        return Err("set-builder concrete predicate projected to another fact family".into());
    };
    if predicate.predicate.to_string() != target_predicate.predicate.to_string()
        || predicate.body.len() != 1
        || target_predicate.body.len() != 1
    {
        return Err("set-builder concrete predicate projection changed its application".into());
    }
    let predicate_name = predicate.predicate.to_string();
    let binding = context
        .predicate_bindings
        .get(&predicate_name)
        .ok_or_else(|| format!("unavailable concrete set-builder predicate {predicate_name}"))?;
    if binding.parameter_count != 1 || binding.requirement_count != 1 {
        return Err(
            "set-builder predicate projection requires one concrete member parameter".into(),
        );
    }
    let definition = binding.definition.as_ref().ok_or_else(|| {
        "abstract set-builder predicates have no projection definition".to_string()
    })?;
    let group = definition
        .typed_parameters
        .groups
        .first()
        .ok_or_else(|| "concrete predicate lost its parameter group".to_string())?;
    let [definition_parameter] = group.params.as_slice() else {
        return Err("set-builder concrete predicate requires one definition parameter".into());
    };
    let set = parameter_set(&group.param_type)?;
    let component_count = binding.requirement_count + definition.iff_facts.len();
    let membership_selector = conjunction_selector(0, component_count)?;
    let rendered_set = render_obj(set, context)?;
    let mut component_proofs = vec![format!(
        "(Litex.In.congr __same {rendered_set}).mpr (__selected{membership_selector})"
    )];
    let mut representative_context = context.clone();
    representative_context
        .symbol_names
        .insert(definition_parameter.id(), "__rep".into());
    let mut element_context = context.clone();
    element_context
        .symbol_names
        .insert(definition_parameter.id(), rendered_element.clone());
    for (definition_clause_index, definition_clause) in definition.iff_facts.iter().enumerate() {
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = definition_clause else {
            return Err(
                "set-builder concrete predicate projection currently transports equality clauses"
                    .into(),
            );
        };
        let selector = conjunction_selector(
            binding.requirement_count + definition_clause_index,
            component_count,
        )?;
        component_proofs.push(render_equality_across_representative(
            equality,
            &representative_context,
            &element_context,
            "__rep",
            &rendered_element,
            "Litex.Same.symm __same",
            &format!("__selected{selector}"),
        )?);
    }
    Ok(format!(
        "(by\n  rcases Litex.Rules.inSetBuilder_iff.mp ({}) with ⟨__rep, __predicate, __same⟩\n  have __selected := __predicate{predicate_selector}\n  unfold {} at __selected ⊢\n  exact ⟨{}⟩)",
        source_proof,
        binding.lean_name,
        component_proofs.join(", ")
    ))
}

pub(super) fn resolve_fact_citation(
    source_fact_id: &FactId,
    expected: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let retained = context
        .fact_propositions
        .get(source_fact_id)
        .ok_or_else(|| {
            let mut visible_fact_ids = context
                .fact_propositions
                .keys()
                .copied()
                .collect::<Vec<_>>();
            visible_fact_ids.sort();
            let visible_fact_ids = visible_fact_ids
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "unavailable cited fact `{source_fact_id}` for expected proposition `{expected}`; visible exact FactIds: [{visible_fact_ids}]"
            )
        })?;
    let same_proposition = if retained.to_string() == expected.to_string() {
        true
    } else if membership_facts_are_equal_up_to_nested_binder_alpha(retained, expected) {
        true
    } else if equality_facts_are_equal_up_to_nested_binder_alpha(retained, expected) {
        true
    } else if let (Fact::ForallFact(retained), Fact::ForallFact(expected)) = (retained, expected) {
        render_forall_fact_type(retained, context)? == render_forall_fact_type(expected, context)?
    } else if matches!(
        (retained, expected),
        (Fact::ExistFact(_), Fact::ExistFact(_))
    ) {
        one_witness_existentials_are_alpha_equal(retained, expected, context)?
    } else {
        false
    };
    if !same_proposition {
        return Err(format!(
            "cited FactId `{source_fact_id}` changed proposition from `{retained}` to `{expected}`"
        ));
    }
    if let Some(name) = context.fact_names.get(source_fact_id) {
        return Ok(name.clone());
    }
    let binding = context
        .forall_conclusion_bindings
        .get(source_fact_id)
        .ok_or_else(|| format!("cited FactId `{source_fact_id}` has no emitted Lean proof"))?;
    render_forall_conclusion_citation(binding, context)
}

pub(super) fn equality_facts_are_equal_up_to_nested_binder_alpha(
    left: &Fact,
    right: &Fact,
) -> bool {
    match (left, right) {
        (
            Fact::AtomicFact(AtomicFact::EqualFact(left)),
            Fact::AtomicFact(AtomicFact::EqualFact(right)),
        ) => {
            objs_equal_with_nested_binder_alpha_equivalence(&left.left, &right.left)
                && objs_equal_with_nested_binder_alpha_equivalence(&left.right, &right.right)
        }
        _ => false,
    }
}

pub(super) fn membership_facts_are_equal_up_to_nested_binder_alpha(
    left: &Fact,
    right: &Fact,
) -> bool {
    match (left, right) {
        (
            Fact::AtomicFact(AtomicFact::InFact(left)),
            Fact::AtomicFact(AtomicFact::InFact(right)),
        ) => {
            objs_equal_with_nested_binder_alpha_equivalence(&left.element, &right.element)
                && objs_equal_with_nested_binder_alpha_equivalence(&left.set, &right.set)
        }
        _ => false,
    }
}

pub(super) fn render_forall_conclusion_citation(
    binding: &ForallConclusionBinding,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let parameters = binding
        .forall
        .typed_parameters
        .collect_param_bindings_with_types();
    if parameters.len() != binding.parameter_premises.len()
        || binding.forall.dom_facts.len() != binding.premises.len()
    {
        return Err("stored forall conclusion binding changed its premise arity".into());
    }
    let mut terms = vec![binding.theorem_name.clone()];
    for ((parameter, param_type), premise) in
        parameters.iter().zip(binding.parameter_premises.iter())
    {
        let argument = context
            .symbol_names
            .get(&parameter.id())
            .cloned()
            .ok_or_else(|| {
                format!(
                    "stored forall conclusion cannot resolve parameter `{}`",
                    parameter.name()
                )
            })?;
        terms.push(argument);
        if !matches!(param_type, ParamType::Set(_)) {
            terms.push(format!(
                "({})",
                resolve_fact_citation(&premise.fact_id, &premise.fact, context)?
            ));
        }
    }
    for premise in &binding.premises {
        terms.push(format!(
            "({})",
            resolve_fact_citation(&premise.fact_id, &premise.fact, context)?
        ));
    }
    let application = format!("({})", terms.join(" "));
    conjunction_projection(
        &application,
        binding.conclusion_index,
        binding.conclusion_count,
    )
}

pub(super) fn render_closed_numeric_membership_from_result(
    proposition: &Fact,
    evidence_target_set: StandardSet,
    evaluation: &SuccessEvaluateObjResult,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (element, set) = membership_parts(proposition)?;
    let Obj::StandardSet(target_set) = set else {
        return Err("closed-numeric-membership certificate targets a nonstandard set".into());
    };
    if *target_set != evidence_target_set
        || obj_equality_key(element) != obj_equality_key(&evaluation.expression)
    {
        return Err(
            "closed-numeric-membership certificate changed its expression or target set".into(),
        );
    }
    let reevaluated = evaluation
        .expression
        .evaluate_to_normalized_decimal_number()
        .ok_or_else(|| "closed-numeric-membership expression no longer evaluates".to_string())?;
    if reevaluated.normalized_value != evaluation.value.normalized_value {
        return Err("closed-numeric-membership normalized value was corrupted".into());
    }
    let source = render_obj(element, context)?;
    let normalized = &evaluation.value.normalized_value;
    match target_set {
        StandardSet::C => Ok(format!("Litex.Rules.complexInC {source}")),
        StandardSet::N
            if normalized
                .chars()
                .all(|character| character.is_ascii_digit()) =>
        {
            Ok(format!(
                "Litex.Rules.complexEqNatInN {source} {normalized} (by norm_num)"
            ))
        }
        StandardSet::NPos
            if normalized
                .chars()
                .all(|character| character.is_ascii_digit())
                && normalized.chars().any(|character| character != '0') =>
        {
            Ok(format!(
                "Litex.Rules.complexEqNatInNPos {source} {normalized} (by norm_num) (by norm_num)"
            ))
        }
        StandardSet::Z => Ok(format!(
            "Litex.Rules.complexEqIntInZ {source} {normalized} (by norm_num)"
        )),
        StandardSet::Q => Ok(format!(
            "Litex.Rules.complexEqRatInQ {source} {normalized} (by norm_num)"
        )),
        StandardSet::QPos => Ok(format!(
            "Litex.Rules.complexEqRatInQPos {source} ({normalized} : ℚ) (by norm_num) (by norm_num)"
        )),
        StandardSet::ZNeg => Ok(format!(
            "Litex.Rules.complexEqIntInZNeg {source} ({normalized} : ℤ) (by norm_num) (by norm_num)"
        )),
        StandardSet::QNeg => Ok(format!(
            "Litex.Rules.complexEqRatInQNeg {source} ({normalized} : ℚ) (by norm_num) (by norm_num)"
        )),
        StandardSet::R => render_closed_real_expression_membership(element, context),
        StandardSet::RPos => Ok(format!(
            "Litex.Rules.complexEqRealInRPos {source} ({normalized} : ℝ) (by norm_num) (by norm_num)"
        )),
        StandardSet::RNeg => Ok(format!(
            "Litex.Rules.complexEqRealInRNeg {source} ({normalized} : ℝ) (by norm_num) (by norm_num)"
        )),
        _ => Err(format!(
            "unsupported closed numeric membership in `{target_set}` with value `{normalized}`"
        )),
    }
}

pub(super) fn render_closed_real_expression_membership(
    element: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (left, right, theorem) = match element {
        Obj::Add(operation) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexAddInR",
        ),
        Obj::Sub(operation) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexSubInR",
        ),
        Obj::Mul(operation) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexMulInR",
        ),
        Obj::Div(operation) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexDivInR",
        ),
        Obj::Number(number) => {
            if number.normalized_value.parse::<i128>().is_err() {
                return Err(
                    "closed real-expression membership requires integral numeral leaves".into(),
                );
            }
            return Ok(format!(
                "Litex.Rules.complexRealInR ({} : ℝ)",
                number.normalized_value
            ));
        }
        _ => {
            return Err(format!(
                "closed real-expression membership has unsupported operand `{element}`"
            ));
        }
    };
    render_obj(element, context)?;
    Ok(format!(
        "Litex.Rules.{theorem} ({}) ({})",
        render_closed_real_expression_membership(left, context)?,
        render_closed_real_expression_membership(right, context)?
    ))
}

pub(super) fn render_closed_numeric_comparison_fact(
    fact: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !fact_is_closed_numeric_relation(fact) {
        return Err("closed numeric comparison changed its target".into());
    }
    let (left, right, theorem, strict, negated) = match fact {
        Fact::AtomicFact(AtomicFact::LessFact(order)) => {
            (&order.left, &order.right, "ltOfComplexReals", true, false)
        }
        Fact::AtomicFact(AtomicFact::GreaterFact(order)) => {
            (&order.right, &order.left, "ltOfComplexReals", true, false)
        }
        Fact::AtomicFact(AtomicFact::LessEqualFact(order)) => {
            (&order.left, &order.right, "leOfComplexReals", false, false)
        }
        Fact::AtomicFact(AtomicFact::GreaterEqualFact(order)) => {
            (&order.right, &order.left, "leOfComplexReals", false, false)
        }
        Fact::AtomicFact(AtomicFact::NotLessFact(order)) => {
            (&order.left, &order.right, "ltOfComplexReals", true, true)
        }
        Fact::AtomicFact(AtomicFact::NotGreaterFact(order)) => {
            (&order.right, &order.left, "ltOfComplexReals", true, true)
        }
        Fact::AtomicFact(AtomicFact::NotLessEqualFact(order)) => {
            (&order.left, &order.right, "leOfComplexReals", false, true)
        }
        Fact::AtomicFact(AtomicFact::NotGreaterEqualFact(order)) => {
            (&order.right, &order.left, "leOfComplexReals", false, true)
        }
        _ => {
            return Err(
                "compiler closed comparison requires an order relation; closed equality and disequality use separate semantic adapters"
                    .into()
            )
        }
    };
    render_obj(left, context)?;
    render_obj(right, context)?;
    if negated {
        return Ok("(by\n  norm_num [Litex.Lt, Litex.Le, Litex.OrderValue])".into());
    }
    if left.to_string() == "0" {
        let theorem = if strict {
            "positiveOfComplexReal"
        } else {
            "nonnegativeOfComplexReal"
        };
        return Ok(format!("Litex.OrderBridge.{theorem} (by norm_num)"));
    }
    Ok(format!("Litex.OrderBridge.{theorem} (by norm_num)"))
}

pub(super) fn validate_closed_numeric_comparison_builtin_rule_evidence(
    source_fact: &Fact,
    evidence: &ClosedNumericComparisonBuiltinRuleEvidence,
) -> Result<(), String> {
    if evidence.expected_target.to_string() != source_fact.to_string() {
        return Err("closed-numeric-comparison evidence changed its target".into());
    }
    validate_success_evaluate_obj_result(&evidence.left_evaluation)?;
    validate_success_evaluate_obj_result(&evidence.right_evaluation)?;

    let Fact::AtomicFact(source_atomic_fact) = source_fact else {
        return Err("closed-numeric-comparison evidence targets a non-atomic fact".into());
    };
    if let AtomicFact::NotEqualFact(not_equal) = source_atomic_fact {
        if obj_equality_key(&not_equal.left)
            != obj_equality_key(&evidence.left_evaluation.expression)
            || obj_equality_key(&not_equal.right)
                != obj_equality_key(&evidence.right_evaluation.expression)
        {
            return Err("closed numeric disequality changed an endpoint".into());
        }
        if evidence.left_evaluation.value.normalized_value
            == evidence.right_evaluation.value.normalized_value
        {
            return Err("closed numeric disequality retained equal normal forms".into());
        }
        return Ok(());
    }

    let Some((normalized_left, normalized_right, allow_equal)) =
        normalized_positive_order_operands(source_atomic_fact)
    else {
        return Err("closed numeric comparison retained a non-comparison target".into());
    };
    if obj_equality_key(normalized_left) != obj_equality_key(&evidence.left_evaluation.expression)
        || obj_equality_key(normalized_right)
            != obj_equality_key(&evidence.right_evaluation.expression)
    {
        return Err("closed numeric comparison changed a normalized endpoint".into());
    }
    let comparison = crate::verify::compare_number_strings(
        &evidence.left_evaluation.value.normalized_value,
        &evidence.right_evaluation.value.normalized_value,
    );
    let comparison_holds = matches!(comparison, crate::verify::NumberCompareResult::Less)
        || (allow_equal && matches!(comparison, crate::verify::NumberCompareResult::Equal));
    if !comparison_holds {
        return Err("closed numeric comparison retained a false normalized relation".into());
    }
    Ok(())
}

pub(super) fn construct_lean_order_reflexivity_from_result(
    source_fact: &Fact,
    evidence: &OrderReflexivityBuiltinRuleEvidence,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if evidence.expected_target.to_string() != source_fact.to_string() {
        return Err("order-reflexivity evidence changed its target".into());
    }
    let Fact::AtomicFact(source_atomic_fact) = source_fact else {
        return Err("order-reflexivity evidence targets a non-atomic fact".into());
    };
    let (left, right) = match source_atomic_fact {
        AtomicFact::LessEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::GreaterEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotLessFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotGreaterFact(fact) => (&fact.left, &fact.right),
        _ => return Err(
            "order-reflexivity evidence requires `x <= x`, `x >= x`, `not x < x`, or `not x > x`"
                .into(),
        ),
    };
    if obj_equality_key(left) != obj_equality_key(right)
        || obj_equality_key(left) != obj_equality_key(&evidence.repeated_object)
    {
        return Err("order-reflexivity evidence changed its repeated object".into());
    }

    construct_lean_order_reflexivity_from_typed_target(source_fact, context)
}

pub(super) fn construct_lean_order_reflexivity_from_typed_target(
    source_fact: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let Fact::AtomicFact(source_atomic_fact) = source_fact else {
        return Err("order-reflexivity target is not atomic".into());
    };
    let (left, right, weak_order) =
        match source_atomic_fact {
            AtomicFact::LessEqualFact(fact) => (&fact.left, &fact.right, true),
            AtomicFact::GreaterEqualFact(fact) => (&fact.left, &fact.right, true),
            AtomicFact::NotLessFact(fact) => (&fact.left, &fact.right, false),
            AtomicFact::NotGreaterFact(fact) => (&fact.left, &fact.right, false),
            _ => return Err(
                "order-reflexivity target requires `x <= x`, `x >= x`, `not x < x`, or `not x > x`"
                    .into(),
            ),
        };
    if obj_equality_key(left) != obj_equality_key(right) {
        return Err("order-reflexivity target changed its repeated object".into());
    }

    // Zero-ended order syntax has a dedicated existential real
    // representation in Lean, so use its already-reviewed numeric bridge.
    if matches!(left, Obj::Number(number) if number.normalized_value == "0") {
        return render_closed_numeric_comparison_fact(source_fact, context);
    }
    let repeated_object = render_numeric_obj(left, context)?;
    if weak_order {
        Ok(format!("Litex.Le.refl {repeated_object}"))
    } else {
        Ok(format!("Litex.Lt.irrefl {repeated_object}"))
    }
}

pub(super) fn construct_lean_registered_reflexive_predicate_from_result(
    source_fact: &Fact,
    evidence: &RegisteredReflexivePredicateBuiltinRuleEvidence,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if evidence.expected_target.to_string() != source_fact.to_string() {
        return Err("registered reflexive-predicate evidence changed its target".into());
    }
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(target)) = source_fact else {
        return Err("registered reflexive-predicate evidence targets a non-user predicate".into());
    };
    if target.predicate.to_string() != evidence.predicate_name || target.body.len() != 2 {
        return Err(
            "registered reflexive-predicate evidence changed its predicate or arity".into(),
        );
    }
    if obj_equality_key(&target.body[0]) != obj_equality_key(&target.body[1]) {
        return Err("registered reflexive-predicate evidence retained unequal arguments".into());
    }

    let binding = context
        .registered_reflexive_predicate_theorem_bindings
        .get(&evidence.predicate_name)
        .ok_or_else(|| {
            format!(
                "registered reflexivity theorem for `{}` is not visible in this compiler environment",
                evidence.predicate_name
            )
        })?;
    let parameters = binding
        .forall_fact
        .typed_parameters
        .collect_param_bindings_with_types();
    let [(parameter, ParamType::Set(_))] = parameters.as_slice() else {
        return Err(
            "direct registered reflexivity currently requires one set-valued parameter".into(),
        );
    };
    if !binding.forall_fact.dom_facts.is_empty() || binding.forall_fact.then_facts.len() != 1 {
        return Err("registered reflexivity theorem changed its forall shape".into());
    }
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(registered_conclusion)) =
        binding.forall_fact.then_facts[0].clone().to_fact()
    else {
        return Err("registered reflexivity theorem has a non-predicate conclusion".into());
    };
    let parameter_object: Obj =
        Identifier::new_bound(parameter.name().to_string(), parameter.as_ref()).into();
    if registered_conclusion.predicate.to_string() != evidence.predicate_name
        || registered_conclusion.body.len() != 2
        || registered_conclusion
            .body
            .iter()
            .any(|argument| obj_equality_key(argument) != obj_equality_key(&parameter_object))
    {
        return Err("registered reflexivity theorem changed its defining conclusion".into());
    }

    // Rendering the target also validates that the predicate definition and
    // target argument are visible in this exact compiler environment.
    render_fact(source_fact, context)?;
    let argument = render_obj(&target.body[0], context)?;
    Ok(format!("{} {argument}", binding.theorem_name))
}

pub(super) fn registered_predicate_property_parameter_objects(
    forall_fact: &ForallFact,
    property_name: &str,
) -> Result<Vec<Obj>, String> {
    let parameters = forall_fact
        .typed_parameters
        .collect_param_bindings_with_types();
    if parameters.len() < 2
        || parameters
            .iter()
            .any(|(_, parameter_type)| !matches!(parameter_type, ParamType::Set(_)))
    {
        return Err(format!(
            "registered {property_name} theorem changed its set-parameter shape"
        ));
    }
    Ok(parameters
        .iter()
        .map(|(parameter, _)| {
            Identifier::new_bound(parameter.name().to_string(), parameter.as_ref()).into()
        })
        .collect())
}

pub(super) fn registered_positive_user_predicate_fact<'a>(
    fact: &'a Fact,
    property_name: &str,
    role: &str,
) -> Result<&'a NormalAtomicFact, String> {
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(predicate)) = fact else {
        return Err(format!(
            "registered {property_name} theorem retained a non-predicate {role}"
        ));
    };
    Ok(predicate)
}

pub(super) fn registered_predicate_direct_parameter_keys(
    predicate: &NormalAtomicFact,
    parameter_objects: &[Obj],
    property_name: &str,
    role: &str,
) -> Result<Vec<String>, String> {
    if predicate.body.len() != parameter_objects.len() {
        return Err(format!(
            "registered {property_name} theorem changed its {role} arity"
        ));
    }
    let parameter_keys = parameter_objects
        .iter()
        .map(obj_equality_key)
        .collect::<HashSet<_>>();
    let argument_keys = predicate
        .body
        .iter()
        .map(obj_equality_key)
        .collect::<Vec<_>>();
    if argument_keys
        .iter()
        .any(|key| !parameter_keys.contains(key))
        || argument_keys.iter().collect::<HashSet<_>>().len() != parameter_objects.len()
    {
        return Err(format!(
            "registered {property_name} theorem {role} does not use every binder exactly once"
        ));
    }
    Ok(argument_keys)
}

pub(super) fn registered_symmetric_predicate_gather(
    forall_fact: &ForallFact,
    predicate_name: &str,
) -> Result<Vec<usize>, String> {
    let parameter_objects =
        registered_predicate_property_parameter_objects(forall_fact, "symmetry")?;
    let [domain] = forall_fact.dom_facts.as_slice() else {
        return Err("registered symmetry theorem changed its single-domain shape".into());
    };
    let [conclusion] = forall_fact.then_facts.as_slice() else {
        return Err("registered symmetry theorem changed its single-conclusion shape".into());
    };
    let domain = registered_positive_user_predicate_fact(domain, "symmetry", "domain")?;
    let conclusion_fact = conclusion.clone().to_fact();
    let conclusion =
        registered_positive_user_predicate_fact(&conclusion_fact, "symmetry", "conclusion")?;
    if domain.predicate.to_string() != predicate_name
        || conclusion.predicate.to_string() != predicate_name
    {
        return Err("registered symmetry theorem changed its predicate name".into());
    }
    let domain_keys = registered_predicate_direct_parameter_keys(
        domain,
        &parameter_objects,
        "symmetry",
        "domain",
    )?;
    let conclusion_keys = registered_predicate_direct_parameter_keys(
        conclusion,
        &parameter_objects,
        "symmetry",
        "conclusion",
    )?;
    let mut gather = Vec::with_capacity(conclusion_keys.len());
    for key in conclusion_keys {
        gather.push(
            domain_keys
                .iter()
                .position(|domain_key| domain_key == &key)
                .ok_or_else(|| {
                    "registered symmetry theorem conclusion escaped its domain binders".to_string()
                })?,
        );
    }
    if gather
        .iter()
        .enumerate()
        .all(|(index, source)| index == *source)
    {
        return Err("registered symmetry theorem retained the identity permutation".into());
    }
    Ok(gather)
}

pub(super) fn instantiate_registered_positive_user_predicate_pattern(
    pattern: &NormalAtomicFact,
    parameter_substitution: &HashMap<String, Obj>,
    predicate_name: &str,
    property_name: &str,
    role: &str,
) -> Result<Fact, String> {
    if pattern.predicate.to_string() != predicate_name {
        return Err(format!(
            "registered {property_name} theorem changed its {role} predicate"
        ));
    }
    let arguments = pattern
        .body
        .iter()
        .enumerate()
        .map(|(index, argument)| {
            parameter_substitution
                .get(&obj_equality_key(argument))
                .cloned()
                .ok_or_else(|| {
                    format!(
                        "registered {property_name} theorem {role} argument {index} is not a direct binder"
                    )
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(NormalAtomicFact::new(
        pattern.predicate.clone(),
        arguments,
        pattern.line_file.clone(),
    )
    .into())
}

pub(super) fn instantiate_registered_symmetric_predicate_transition(
    forall_fact: &ForallFact,
    predicate_name: &str,
    current_domain: &Fact,
) -> Result<(Fact, Vec<Obj>), String> {
    let parameter_objects =
        registered_predicate_property_parameter_objects(forall_fact, "symmetry")?;
    let [domain] = forall_fact.dom_facts.as_slice() else {
        return Err("registered symmetry theorem changed its single-domain shape".into());
    };
    let [conclusion] = forall_fact.then_facts.as_slice() else {
        return Err("registered symmetry theorem changed its single-conclusion shape".into());
    };
    let domain = registered_positive_user_predicate_fact(domain, "symmetry", "domain")?;
    let current_domain =
        registered_positive_user_predicate_fact(current_domain, "symmetry", "use premise")?;
    if domain.predicate.to_string() != predicate_name
        || current_domain.predicate.to_string() != predicate_name
        || domain.body.len() != current_domain.body.len()
    {
        return Err("registered symmetry theorem does not match its retained premise".into());
    }
    registered_predicate_direct_parameter_keys(domain, &parameter_objects, "symmetry", "domain")?;
    let mut substitution = HashMap::new();
    for (binder, argument) in domain.body.iter().zip(current_domain.body.iter()) {
        if substitution
            .insert(obj_equality_key(binder), argument.clone())
            .is_some()
        {
            return Err("registered symmetry theorem repeated a domain binder".into());
        }
    }
    let parameter_arguments = parameter_objects
        .iter()
        .map(|parameter| {
            substitution
                .get(&obj_equality_key(parameter))
                .cloned()
                .ok_or_else(|| {
                    "registered symmetry theorem lost a parameter substitution".to_string()
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let conclusion_fact = conclusion.clone().to_fact();
    let conclusion =
        registered_positive_user_predicate_fact(&conclusion_fact, "symmetry", "conclusion")?;
    let instantiated_conclusion = instantiate_registered_positive_user_predicate_pattern(
        conclusion,
        &substitution,
        predicate_name,
        "symmetry",
        "conclusion",
    )?;
    Ok((instantiated_conclusion, parameter_arguments))
}

pub(super) fn instantiate_registered_antisymmetric_predicate_application(
    forall_fact: &ForallFact,
    predicate_name: &str,
    target: &Fact,
) -> Result<(Vec<Obj>, Vec<Fact>), String> {
    let parameter_objects =
        registered_predicate_property_parameter_objects(forall_fact, "antisymmetry")?;
    if parameter_objects.len() != 2 || forall_fact.dom_facts.len() != 2 {
        return Err("registered antisymmetry theorem changed its binary domain shape".into());
    }
    let [conclusion] = forall_fact.then_facts.as_slice() else {
        return Err("registered antisymmetry theorem changed its single-conclusion shape".into());
    };
    let conclusion_fact = conclusion.clone().to_fact();
    let Fact::AtomicFact(AtomicFact::EqualFact(conclusion_equality)) = &conclusion_fact else {
        return Err("registered antisymmetry theorem retained a non-equality conclusion".into());
    };
    let Fact::AtomicFact(AtomicFact::EqualFact(target_equality)) = target else {
        return Err(
            "registered antisymmetric-predicate evidence targets a non-equality fact".into(),
        );
    };
    let parameter_keys = parameter_objects
        .iter()
        .map(obj_equality_key)
        .collect::<HashSet<_>>();
    let conclusion_keys = [
        obj_equality_key(&conclusion_equality.left),
        obj_equality_key(&conclusion_equality.right),
    ];
    if conclusion_keys[0] == conclusion_keys[1]
        || conclusion_keys
            .iter()
            .any(|key| !parameter_keys.contains(key))
    {
        return Err(
            "registered antisymmetry theorem conclusion does not use both binders exactly once"
                .into(),
        );
    }
    let mut substitution = HashMap::new();
    substitution.insert(conclusion_keys[0].clone(), target_equality.left.clone());
    substitution.insert(conclusion_keys[1].clone(), target_equality.right.clone());
    let parameter_arguments = parameter_objects
        .iter()
        .map(|parameter| {
            substitution
                .get(&obj_equality_key(parameter))
                .cloned()
                .ok_or_else(|| {
                    "registered antisymmetry theorem lost a parameter substitution".to_string()
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let expected_premises = forall_fact
        .dom_facts
        .iter()
        .enumerate()
        .map(|(index, premise)| {
            let premise = registered_positive_user_predicate_fact(
                premise,
                "antisymmetry",
                &format!("domain {index}"),
            )?;
            if premise.body.len() != 2 {
                return Err(format!(
                    "registered antisymmetry theorem changed domain {index} arity"
                ));
            }
            instantiate_registered_positive_user_predicate_pattern(
                premise,
                &substitution,
                predicate_name,
                "antisymmetry",
                &format!("domain {index}"),
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((parameter_arguments, expected_premises))
}

pub(super) fn instantiate_registered_transitive_predicate_application(
    forall_fact: &ForallFact,
    predicate_name: &str,
    left_premise: &Fact,
    right_premise: &Fact,
) -> Result<(Fact, Vec<Obj>), String> {
    let parameter_objects =
        registered_predicate_property_parameter_objects(forall_fact, "transitivity")?;
    if parameter_objects.len() != 3 || forall_fact.dom_facts.len() != 2 {
        return Err(
            "registered transitivity theorem changed its ternary binder/domain shape".into(),
        );
    }
    let [conclusion] = forall_fact.then_facts.as_slice() else {
        return Err("registered transitivity theorem changed its single-conclusion shape".into());
    };
    let domain_patterns = forall_fact
        .dom_facts
        .iter()
        .enumerate()
        .map(|(index, premise)| {
            registered_positive_user_predicate_fact(
                premise,
                "transitivity",
                &format!("domain {index}"),
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let actual_premises = [
        registered_positive_user_predicate_fact(left_premise, "transitivity", "left use premise")?,
        registered_positive_user_predicate_fact(
            right_premise,
            "transitivity",
            "right use premise",
        )?,
    ];
    let parameter_keys = parameter_objects
        .iter()
        .map(obj_equality_key)
        .collect::<HashSet<_>>();
    let mut substitution = HashMap::new();
    for (domain_index, (pattern, actual)) in domain_patterns
        .iter()
        .zip(actual_premises.iter())
        .enumerate()
    {
        if pattern.predicate.to_string() != predicate_name
            || actual.predicate.to_string() != predicate_name
            || pattern.body.len() != 2
            || actual.body.len() != 2
        {
            return Err(format!(
                "registered transitivity theorem changed domain {domain_index} predicate or arity"
            ));
        }
        for (argument_index, (binder, argument)) in
            pattern.body.iter().zip(actual.body.iter()).enumerate()
        {
            let binder_key = obj_equality_key(binder);
            if !parameter_keys.contains(&binder_key) {
                return Err(format!(
                    "registered transitivity domain {domain_index} argument {argument_index} is not a direct binder"
                ));
            }
            if let Some(previous) = substitution.get(&binder_key) {
                if obj_equality_key(previous) != obj_equality_key(argument) {
                    return Err(
                        "registered transitivity premises disagree at their shared binder".into(),
                    );
                }
            } else {
                substitution.insert(binder_key, argument.clone());
            }
        }
    }
    let parameter_arguments = parameter_objects
        .iter()
        .map(|parameter| {
            substitution
                .get(&obj_equality_key(parameter))
                .cloned()
                .ok_or_else(|| {
                    "registered transitivity theorem lost a parameter substitution".to_string()
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let conclusion_fact = conclusion.clone().to_fact();
    let conclusion_pattern =
        registered_positive_user_predicate_fact(&conclusion_fact, "transitivity", "conclusion")?;
    if conclusion_pattern.body.len() != 2 {
        return Err("registered transitivity theorem changed its conclusion arity".into());
    }
    let instantiated_conclusion = instantiate_registered_positive_user_predicate_pattern(
        conclusion_pattern,
        &substitution,
        predicate_name,
        "transitivity",
        "conclusion",
    )?;
    Ok((instantiated_conclusion, parameter_arguments))
}

pub(super) fn normalized_positive_order_operands(
    source_atomic_fact: &AtomicFact,
) -> Option<(&Obj, &Obj, bool)> {
    match source_atomic_fact {
        AtomicFact::LessFact(fact) => Some((&fact.left, &fact.right, false)),
        AtomicFact::GreaterFact(fact) => Some((&fact.right, &fact.left, false)),
        AtomicFact::LessEqualFact(fact) => Some((&fact.left, &fact.right, true)),
        AtomicFact::GreaterEqualFact(fact) => Some((&fact.right, &fact.left, true)),
        AtomicFact::NotLessFact(fact) => Some((&fact.right, &fact.left, true)),
        AtomicFact::NotGreaterFact(fact) => Some((&fact.left, &fact.right, true)),
        AtomicFact::NotLessEqualFact(fact) => Some((&fact.right, &fact.left, false)),
        AtomicFact::NotGreaterEqualFact(fact) => Some((&fact.left, &fact.right, false)),
        _ => None,
    }
}

pub(super) fn standard_set_membership_projection_theorem_chain(
    source_set: StandardSet,
    target_set: StandardSet,
) -> Result<&'static [&'static str], String> {
    match (source_set, target_set) {
        (StandardSet::NPos, StandardSet::N) => Ok(&["inNOfInNPos"]),
        (StandardSet::NPos, StandardSet::Z) => Ok(&["inNOfInNPos", "inZOfInN"]),
        (StandardSet::NPos, StandardSet::Q) => Ok(&["inNOfInNPos", "inZOfInN", "inQOfInZ"]),
        (StandardSet::NPos, StandardSet::R) => {
            Ok(&["inNOfInNPos", "inZOfInN", "inQOfInZ", "inROfInQ"])
        }
        (StandardSet::NPos, StandardSet::C) => Ok(&[
            "inNOfInNPos",
            "inZOfInN",
            "inQOfInZ",
            "inROfInQ",
            "inCOfInR",
        ]),
        (StandardSet::RPos, StandardSet::R) => Ok(&["inROfInRPos"]),
        (StandardSet::RPos, StandardSet::C) => Ok(&["inROfInRPos", "inCOfInR"]),
        (StandardSet::ZStar, StandardSet::Z) => Ok(&["inZOfInZStar"]),
        (StandardSet::ZStar, StandardSet::Q) => Ok(&["inZOfInZStar", "inQOfInZ"]),
        (StandardSet::ZStar, StandardSet::R) => Ok(&["inZOfInZStar", "inQOfInZ", "inROfInQ"]),
        (StandardSet::ZStar, StandardSet::C) => {
            Ok(&["inZOfInZStar", "inQOfInZ", "inROfInQ", "inCOfInR"])
        }
        (StandardSet::QStar, StandardSet::Q) => Ok(&["inQOfInQStar"]),
        (StandardSet::QStar, StandardSet::R) => Ok(&["inQOfInQStar", "inROfInQ"]),
        (StandardSet::QStar, StandardSet::C) => Ok(&["inQOfInQStar", "inROfInQ", "inCOfInR"]),
        (StandardSet::RStar, StandardSet::R) => Ok(&["inROfInRStar"]),
        (StandardSet::RStar, StandardSet::C) => Ok(&["inROfInRStar", "inCOfInR"]),
        (StandardSet::CStar, StandardSet::C) => Ok(&["inCOfInCStar"]),
        (StandardSet::ZStar, StandardSet::QStar) => Ok(&["inQStarOfInZStar"]),
        (StandardSet::ZStar, StandardSet::RStar) => Ok(&["inQStarOfInZStar", "inRStarOfInQStar"]),
        (StandardSet::ZStar, StandardSet::CStar) => {
            Ok(&["inQStarOfInZStar", "inRStarOfInQStar", "inCStarOfInRStar"])
        }
        (StandardSet::QStar, StandardSet::RStar) => Ok(&["inRStarOfInQStar"]),
        (StandardSet::QStar, StandardSet::CStar) => Ok(&["inRStarOfInQStar", "inCStarOfInRStar"]),
        (StandardSet::RStar, StandardSet::CStar) => Ok(&["inCStarOfInRStar"]),
        (StandardSet::N, StandardSet::Z) => Ok(&["inZOfInN"]),
        (StandardSet::N, StandardSet::Q) => Ok(&["inZOfInN", "inQOfInZ"]),
        (StandardSet::N, StandardSet::R) => Ok(&["inZOfInN", "inQOfInZ", "inROfInQ"]),
        (StandardSet::N, StandardSet::C) => Ok(&["inZOfInN", "inQOfInZ", "inROfInQ", "inCOfInR"]),
        (StandardSet::Z, StandardSet::Q) => Ok(&["inQOfInZ"]),
        (StandardSet::Z, StandardSet::R) => Ok(&["inQOfInZ", "inROfInQ"]),
        (StandardSet::Z, StandardSet::C) => Ok(&["inQOfInZ", "inROfInQ", "inCOfInR"]),
        (StandardSet::Q, StandardSet::R) => Ok(&["inROfInQ"]),
        (StandardSet::Q, StandardSet::C) => Ok(&["inROfInQ", "inCOfInR"]),
        (StandardSet::R, StandardSet::C) => Ok(&["inCOfInR"]),
        _ => Err(format!(
            "unsupported standard-set membership projection `{source_set}` to `{target_set}`"
        )),
    }
}

pub(super) fn render_base_set_builtin_rule_from_compiled_children(
    target: &Fact,
    rule: SetBuiltinRule,
    children: &[(Fact, String)],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    render_fact(target, context)?;
    match rule {
        SetBuiltinRule::SubsetReflexivity | SetBuiltinRule::SupersetReflexivity => {
            if !children.is_empty() {
                return Err("set-relation reflexivity retained child proofs".into());
            }
            render_set_relation_reflexivity(
                target,
                rule == SetBuiltinRule::SubsetReflexivity,
                context,
            )
        }
        SetBuiltinRule::UnionMembershipLeft | SetBuiltinRule::UnionMembershipRight => {
            let [(premise, proof)] = children else {
                return Err("union membership requires one selected child Result".into());
            };
            let (element, set) = membership_parts(target)?;
            let Obj::Union(union) = set else {
                return Err("union membership changed its target constructor".into());
            };
            let (premise_element, premise_set) = membership_parts(premise)?;
            let (selected_set, theorem) = if rule == SetBuiltinRule::UnionMembershipLeft {
                (union.left.as_ref(), "inUnionLeft")
            } else {
                (union.right.as_ref(), "inUnionRight")
            };
            if obj_equality_key(element) != obj_equality_key(premise_element)
                || obj_equality_key(selected_set) != obj_equality_key(premise_set)
            {
                return Err("union membership changed its selected side or element".into());
            }
            Ok(format!("Litex.SetRules.{theorem} ({proof})"))
        }
        SetBuiltinRule::IntersectMembershipBoth => {
            let [(left_fact, left_proof), (right_fact, right_proof)] = children else {
                return Err("intersection membership requires two ordered child Results".into());
            };
            let (element, set) = membership_parts(target)?;
            let Obj::Intersect(intersection) = set else {
                return Err("intersection membership changed its constructor".into());
            };
            for (premise, expected_set) in [
                (left_fact, intersection.left.as_ref()),
                (right_fact, intersection.right.as_ref()),
            ] {
                let (premise_element, premise_set) = membership_parts(premise)?;
                if obj_equality_key(element) != obj_equality_key(premise_element)
                    || obj_equality_key(expected_set) != obj_equality_key(premise_set)
                {
                    return Err("intersection membership changed its ordered side children".into());
                }
            }
            Ok(format!(
                "Litex.SetRules.inIntersect ({left_proof}) ({right_proof})"
            ))
        }
        SetBuiltinRule::IntersectNonMembershipLeft
        | SetBuiltinRule::IntersectNonMembershipRight => {
            let [(premise, proof)] = children else {
                return Err("intersection nonmembership requires one selected child Result".into());
            };
            let (element, set) = nonmembership_parts(target)?;
            let Obj::Intersect(intersection) = set else {
                return Err("intersection nonmembership changed its constructor".into());
            };
            let (premise_element, premise_set) = nonmembership_parts(premise)?;
            let (selected_set, theorem) = if rule == SetBuiltinRule::IntersectNonMembershipLeft {
                (intersection.left.as_ref(), "notInIntersectOfNotInLeft")
            } else {
                (intersection.right.as_ref(), "notInIntersectOfNotInRight")
            };
            if obj_equality_key(element) != obj_equality_key(premise_element)
                || obj_equality_key(selected_set) != obj_equality_key(premise_set)
            {
                return Err("intersection nonmembership changed its selected side".into());
            }
            Ok(format!("Litex.SetRules.{theorem} ({proof})"))
        }
        SetBuiltinRule::SetMinusMembership => {
            let [(left_fact, left_proof), (right_fact, right_proof)] = children else {
                return Err("set-minus membership requires two ordered child Results".into());
            };
            let (element, set) = membership_parts(target)?;
            let Obj::SetMinus(difference) = set else {
                return Err("set-minus membership changed its constructor".into());
            };
            let (left_element, left_set) = membership_parts(left_fact)?;
            let (right_element, right_set) = nonmembership_parts(right_fact)?;
            if obj_equality_key(element) != obj_equality_key(left_element)
                || obj_equality_key(element) != obj_equality_key(right_element)
                || obj_equality_key(difference.left.as_ref()) != obj_equality_key(left_set)
                || obj_equality_key(difference.right.as_ref()) != obj_equality_key(right_set)
            {
                return Err("set-minus membership changed its ordered children".into());
            }
            Ok(format!(
                "Litex.SetRules.inSetMinus ({left_proof}) ({right_proof})"
            ))
        }
        _ => Err("structural set rule reached base Result renderer".into()),
    }
}

pub(super) fn render_set_relation_reflexivity(
    fact: &Fact,
    expected_subset_spelling: bool,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (source, target, negated, subset_spelling) = normalized_set_relation_parts(fact)?;
    if negated
        || subset_spelling != expected_subset_spelling
        || obj_equality_key(source) != obj_equality_key(target)
    {
        return Err("set-relation reflexivity changed its spelling or endpoints".into());
    }
    render_fact(fact, context)?;
    Ok("(fun _x __membership => __membership)".into())
}

pub(super) fn render_extended_set_rule(
    fact: &Fact,
    rule: LeanSetBuiltinCompilationKind,
    premises: &[CompiledFactProofBody],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    render_fact(fact, context)?;
    match rule {
        LeanSetBuiltinCompilationKind::EmptySubset => {
            if !premises.is_empty() {
                return Err("empty-subset rule retained premises".into());
            }
            let (empty, target) = subset_parts(fact)?;
            if !matches!(empty, Obj::ListSet(set) if set.list.is_empty()) {
                return Err("empty-subset rule changed its empty left endpoint".into());
            }
            Ok(format!(
                "Litex.SetRules.emptySubset {}",
                render_obj(target, context)?
            ))
        }
        LeanSetBuiltinCompilationKind::SubsetUnionLeft
        | LeanSetBuiltinCompilationKind::SubsetUnionRight => {
            if !premises.is_empty() {
                return Err("subset-union inclusion retained premises".into());
            }
            let (source, target) = subset_parts(fact)?;
            let Obj::Union(union) = target else {
                return Err("subset-union inclusion changed its target constructor".into());
            };
            let (expected, theorem) = if rule == LeanSetBuiltinCompilationKind::SubsetUnionLeft {
                (union.left.as_ref(), "subsetUnionLeft")
            } else {
                (union.right.as_ref(), "subsetUnionRight")
            };
            if obj_equality_key(source) != obj_equality_key(expected) {
                return Err("subset-union inclusion changed its selected operand".into());
            }
            Ok(format!(
                "Litex.SetRules.{theorem} {} {}",
                render_obj(union.left.as_ref(), context)?,
                render_obj(union.right.as_ref(), context)?
            ))
        }
        LeanSetBuiltinCompilationKind::UnionSubset => {
            if premises.len() != 2 {
                return Err("union-subset rule requires two ordered subset premises".into());
            }
            let (source, target) = subset_parts(fact)?;
            let Obj::Union(union) = source else {
                return Err("union-subset rule changed its source constructor".into());
            };
            for (premise, operand) in premises.iter().zip([&union.left, &union.right]) {
                let (premise_source, premise_target) = subset_parts(&premise.fact)?;
                if obj_equality_key(premise_source) != obj_equality_key(operand.as_ref())
                    || obj_equality_key(premise_target) != obj_equality_key(target)
                {
                    return Err("union-subset rule changed its ordered premises".into());
                }
            }
            Ok(format!(
                "Litex.SetRules.unionSubset ({}) ({})",
                premises[0].proof_expression, premises[1].proof_expression
            ))
        }
        LeanSetBuiltinCompilationKind::IntersectSubsetLeft
        | LeanSetBuiltinCompilationKind::IntersectSubsetRight
        | LeanSetBuiltinCompilationKind::SetMinusSubsetLeft => {
            if !premises.is_empty() {
                return Err("constructor-subset rule retained premises".into());
            }
            let (source, target) = subset_parts(fact)?;
            let (left, right, expected, theorem) = match (rule, source) {
                (LeanSetBuiltinCompilationKind::IntersectSubsetLeft, Obj::Intersect(value)) => (
                    value.left.as_ref(),
                    value.right.as_ref(),
                    value.left.as_ref(),
                    "intersectSubsetLeft",
                ),
                (LeanSetBuiltinCompilationKind::IntersectSubsetRight, Obj::Intersect(value)) => (
                    value.left.as_ref(),
                    value.right.as_ref(),
                    value.right.as_ref(),
                    "intersectSubsetRight",
                ),
                (LeanSetBuiltinCompilationKind::SetMinusSubsetLeft, Obj::SetMinus(value)) => (
                    value.left.as_ref(),
                    value.right.as_ref(),
                    value.left.as_ref(),
                    "setMinusSubsetLeft",
                ),
                _ => return Err("constructor-subset rule changed its constructor".into()),
            };
            if obj_equality_key(target) != obj_equality_key(expected) {
                return Err("constructor-subset rule changed its projected operand".into());
            }
            Ok(format!(
                "Litex.SetRules.{theorem} {} {}",
                render_obj(left, context)?,
                render_obj(right, context)?
            ))
        }
        LeanSetBuiltinCompilationKind::UnionFinite
        | LeanSetBuiltinCompilationKind::IntersectFinite
        | LeanSetBuiltinCompilationKind::SetMinusFiniteLeft => {
            let target = finite_set_parts(fact)?;
            let (left, right, theorem, expected_premises) = match (rule, target) {
                (LeanSetBuiltinCompilationKind::UnionFinite, Obj::Union(value)) => {
                    (value.left.as_ref(), value.right.as_ref(), "unionFinite", 2)
                }
                (LeanSetBuiltinCompilationKind::IntersectFinite, Obj::Intersect(value)) => (
                    value.left.as_ref(),
                    value.right.as_ref(),
                    "intersectFinite",
                    2,
                ),
                (LeanSetBuiltinCompilationKind::SetMinusFiniteLeft, Obj::SetMinus(value)) => (
                    value.left.as_ref(),
                    value.right.as_ref(),
                    "setMinusFiniteLeft",
                    1,
                ),
                _ => return Err("finite-set rule changed its target constructor".into()),
            };
            if premises.len() != expected_premises
                || obj_equality_key(finite_set_parts(&premises[0].fact)?) != obj_equality_key(left)
                || (expected_premises == 2
                    && obj_equality_key(finite_set_parts(&premises[1].fact)?)
                        != obj_equality_key(right))
            {
                return Err("finite-set rule changed its ordered finiteness premises".into());
            }
            let mut terms = vec![
                format!("Litex.SetRules.{theorem}"),
                render_obj(left, context)?,
                render_obj(right, context)?,
                format!("({})", premises[0].proof_expression),
            ];
            if expected_premises == 2 && rule == LeanSetBuiltinCompilationKind::UnionFinite {
                terms.push(format!("({})", premises[1].proof_expression));
            }
            Ok(terms.join(" "))
        }
        LeanSetBuiltinCompilationKind::UnionNonemptyLeft
        | LeanSetBuiltinCompilationKind::UnionNonemptyRight => {
            if premises.len() != 1 {
                return Err("union nonemptiness requires one selected premise".into());
            }
            let target = nonempty_set_parts(fact)?;
            let Obj::Union(union) = target else {
                return Err("union nonemptiness changed its target constructor".into());
            };
            let (expected, theorem) = if rule == LeanSetBuiltinCompilationKind::UnionNonemptyLeft {
                (union.left.as_ref(), "unionNonemptyLeft")
            } else {
                (union.right.as_ref(), "unionNonemptyRight")
            };
            if obj_equality_key(nonempty_set_parts(&premises[0].fact)?)
                != obj_equality_key(expected)
            {
                return Err("union nonemptiness changed its selected operand".into());
            }
            Ok(format!(
                "Litex.SetRules.{theorem} {} {} ({})",
                render_obj(union.left.as_ref(), context)?,
                render_obj(union.right.as_ref(), context)?,
                premises[0].proof_expression
            ))
        }
        LeanSetBuiltinCompilationKind::PowerSetMembershipOfSubset => {
            if premises.len() != 1 {
                return Err("power-set membership requires one subset premise".into());
            }
            let (subset, target) = membership_parts(fact)?;
            let Obj::PowerSet(power) = target else {
                return Err("power-set membership changed its target constructor".into());
            };
            let (premise_subset, premise_base) = subset_parts(&premises[0].fact)?;
            if obj_equality_key(subset) != obj_equality_key(premise_subset)
                || obj_equality_key(power.set.as_ref()) != obj_equality_key(premise_base)
            {
                return Err("power-set membership changed its subset endpoints".into());
            }
            Ok(format!(
                "Litex.SetRules.inPowerSetOfSubset ({})",
                premises[0].proof_expression
            ))
        }
        LeanSetBuiltinCompilationKind::PowerSetNonempty => {
            if !premises.is_empty() {
                return Err("power-set nonemptiness retained premises".into());
            }
            let Obj::PowerSet(power) = nonempty_set_parts(fact)? else {
                return Err("power-set nonemptiness changed its constructor".into());
            };
            Ok(format!(
                "Litex.SetRules.powerSetNonempty {}",
                render_obj(power.set.as_ref(), context)?
            ))
        }
        LeanSetBuiltinCompilationKind::PowerSetFinite => {
            if premises.len() != 1 {
                return Err("power-set finiteness requires one base finiteness premise".into());
            }
            let Obj::PowerSet(power) = finite_set_parts(fact)? else {
                return Err("power-set finiteness changed its constructor".into());
            };
            if obj_equality_key(finite_set_parts(&premises[0].fact)?)
                != obj_equality_key(power.set.as_ref())
            {
                return Err("power-set finiteness changed its base premise".into());
            }
            Ok(format!(
                "Litex.SetRules.powerSetFinite {} ({})",
                render_obj(power.set.as_ref(), context)?,
                premises[0].proof_expression
            ))
        }
        LeanSetBuiltinCompilationKind::IntersectEqLeftOfSubset
        | LeanSetBuiltinCompilationKind::IntersectEqRightOfSubset => {
            if premises.len() != 1 {
                return Err("intersection absorption requires one subset premise".into());
            }
            let (left, right) = equality_parts(fact)?;
            let Obj::Intersect(intersection) = left else {
                return Err("intersection absorption changed its equality constructor".into());
            };
            let (premise_left, premise_right) = subset_parts(&premises[0].fact)?;
            let (expected_result, expected_left, expected_right, theorem) =
                if rule == LeanSetBuiltinCompilationKind::IntersectEqLeftOfSubset {
                    (
                        intersection.left.as_ref(),
                        intersection.left.as_ref(),
                        intersection.right.as_ref(),
                        "intersectEqLeftOfSubset",
                    )
                } else {
                    (
                        intersection.right.as_ref(),
                        intersection.right.as_ref(),
                        intersection.left.as_ref(),
                        "intersectEqRightOfSubset",
                    )
                };
            if obj_equality_key(right) != obj_equality_key(expected_result)
                || obj_equality_key(premise_left) != obj_equality_key(expected_left)
                || obj_equality_key(premise_right) != obj_equality_key(expected_right)
            {
                return Err("intersection absorption changed its operands".into());
            }
            Ok(format!(
                "Litex.SetRules.{theorem} ({})",
                premises[0].proof_expression
            ))
        }
        LeanSetBuiltinCompilationKind::IntersectUnionDistributive
        | LeanSetBuiltinCompilationKind::SetMinusIntersectDeMorgan
        | LeanSetBuiltinCompilationKind::SetMinusUnionDeMorgan => {
            if !premises.is_empty() {
                return Err("structural three-set equality retained premises".into());
            }
            render_three_set_equality(fact, rule, context)
        }
        LeanSetBuiltinCompilationKind::SetMinusRecoverSubset
        | LeanSetBuiltinCompilationKind::SubsetEqSetMinusRecovery => {
            if premises.len() != 1 {
                return Err("set-minus recovery requires one subset premise".into());
            }
            let (subset, left) = subset_parts(&premises[0].fact)?;
            let (equality_left, equality_right) = equality_parts(fact)?;
            let (difference, plain, reverse) =
                if rule == LeanSetBuiltinCompilationKind::SetMinusRecoverSubset {
                    (equality_left, equality_right, false)
                } else {
                    (equality_right, equality_left, true)
                };
            let Obj::SetMinus(outer) = difference else {
                return Err("set-minus recovery changed its outer constructor".into());
            };
            let Obj::SetMinus(inner) = outer.right.as_ref() else {
                return Err("set-minus recovery changed its inner constructor".into());
            };
            if obj_equality_key(plain) != obj_equality_key(subset)
                || obj_equality_key(outer.left.as_ref()) != obj_equality_key(left)
                || obj_equality_key(inner.left.as_ref()) != obj_equality_key(left)
                || obj_equality_key(inner.right.as_ref()) != obj_equality_key(subset)
            {
                return Err("set-minus recovery changed its subset operands".into());
            }
            let proof = format!(
                "Litex.SetRules.setMinusRecoverSubset ({})",
                premises[0].proof_expression
            );
            Ok(if reverse {
                format!("Litex.Same.symm ({proof})")
            } else {
                proof
            })
        }
        _ => Err("base set rule reached extended set-rule renderer".into()),
    }
}

pub(super) fn render_three_set_equality(
    fact: &Fact,
    rule: LeanSetBuiltinCompilationKind,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (left, right) = equality_parts(fact)?;
    let (first, second, third, theorem) = match rule {
        LeanSetBuiltinCompilationKind::IntersectUnionDistributive => {
            let Obj::Intersect(left_intersection) = left else {
                return Err("intersection distributivity changed its left constructor".into());
            };
            let Obj::Union(left_union) = left_intersection.right.as_ref() else {
                return Err("intersection distributivity changed its inner union".into());
            };
            let Obj::Union(right_union) = right else {
                return Err("intersection distributivity changed its right constructor".into());
            };
            let (Obj::Intersect(right_left), Obj::Intersect(right_right)) =
                (right_union.left.as_ref(), right_union.right.as_ref())
            else {
                return Err("intersection distributivity changed its result intersections".into());
            };
            let first = left_intersection.left.as_ref();
            let second = left_union.left.as_ref();
            let third = left_union.right.as_ref();
            if obj_equality_key(right_left.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(right_left.right.as_ref()) != obj_equality_key(second)
                || obj_equality_key(right_right.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(right_right.right.as_ref()) != obj_equality_key(third)
            {
                return Err("intersection distributivity changed its repeated operands".into());
            }
            (first, second, third, "intersectUnionDistributive")
        }
        LeanSetBuiltinCompilationKind::SetMinusIntersectDeMorgan => {
            let Obj::SetMinus(left_difference) = left else {
                return Err("intersection De Morgan changed its left difference".into());
            };
            let Obj::Intersect(excluded) = left_difference.right.as_ref() else {
                return Err("intersection De Morgan changed its excluded intersection".into());
            };
            let Obj::Union(result) = right else {
                return Err("intersection De Morgan changed its result union".into());
            };
            let (Obj::SetMinus(result_left), Obj::SetMinus(result_right)) =
                (result.left.as_ref(), result.right.as_ref())
            else {
                return Err("intersection De Morgan changed its result differences".into());
            };
            let first = left_difference.left.as_ref();
            let second = excluded.left.as_ref();
            let third = excluded.right.as_ref();
            if obj_equality_key(result_left.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(result_left.right.as_ref()) != obj_equality_key(second)
                || obj_equality_key(result_right.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(result_right.right.as_ref()) != obj_equality_key(third)
            {
                return Err("intersection De Morgan changed its repeated operands".into());
            }
            (first, second, third, "setMinusIntersectDeMorgan")
        }
        LeanSetBuiltinCompilationKind::SetMinusUnionDeMorgan => {
            let Obj::SetMinus(left_difference) = left else {
                return Err("union De Morgan changed its left difference".into());
            };
            let Obj::Union(excluded) = left_difference.right.as_ref() else {
                return Err("union De Morgan changed its excluded union".into());
            };
            let Obj::Intersect(result) = right else {
                return Err("union De Morgan changed its result intersection".into());
            };
            let (Obj::SetMinus(result_left), Obj::SetMinus(result_right)) =
                (result.left.as_ref(), result.right.as_ref())
            else {
                return Err("union De Morgan changed its result differences".into());
            };
            let first = left_difference.left.as_ref();
            let second = excluded.left.as_ref();
            let third = excluded.right.as_ref();
            if obj_equality_key(result_left.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(result_left.right.as_ref()) != obj_equality_key(second)
                || obj_equality_key(result_right.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(result_right.right.as_ref()) != obj_equality_key(third)
            {
                return Err("union De Morgan changed its repeated operands".into());
            }
            (first, second, third, "setMinusUnionDeMorgan")
        }
        _ => return Err("non-three-set rule reached structural renderer".into()),
    };
    Ok(format!(
        "Litex.SetRules.{theorem} {} {} {}",
        render_obj(first, context)?,
        render_obj(second, context)?,
        render_obj(third, context)?
    ))
}

pub(super) fn render_structural_set_equality(
    fact: &Fact,
    rule: LeanSetBuiltinCompilationKind,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (left, right) = equality_parts(fact)?;
    render_fact(fact, context)?;
    let symmetric = |proof: String| format!("Litex.Same.symm ({proof})");
    match rule {
        LeanSetBuiltinCompilationKind::UnionCommutative => {
            let (Obj::Union(left_union), Obj::Union(right_union)) = (left, right) else {
                return Err("union commutativity changed its constructors".into());
            };
            if obj_equality_key(left_union.left.as_ref())
                != obj_equality_key(right_union.right.as_ref())
                || obj_equality_key(left_union.right.as_ref())
                    != obj_equality_key(right_union.left.as_ref())
            {
                return Err("union commutativity changed its swapped operands".into());
            }
            Ok(format!(
                "Litex.SetRules.unionCommutative {} {}",
                render_obj(left_union.left.as_ref(), context)?,
                render_obj(left_union.right.as_ref(), context)?
            ))
        }
        LeanSetBuiltinCompilationKind::UnionAssociative => {
            if let (Obj::Union(left_outer), Obj::Union(right_outer)) = (left, right) {
                if let Obj::Union(left_inner) = left_outer.left.as_ref() {
                    if obj_equality_key(left_inner.left.as_ref())
                        == obj_equality_key(right_outer.left.as_ref())
                    {
                        if let Obj::Union(right_inner) = right_outer.right.as_ref() {
                            if obj_equality_key(left_inner.right.as_ref())
                                == obj_equality_key(right_inner.left.as_ref())
                                && obj_equality_key(left_outer.right.as_ref())
                                    == obj_equality_key(right_inner.right.as_ref())
                            {
                                return Ok(format!(
                                    "Litex.SetRules.unionAssociative {} {} {}",
                                    render_obj(left_inner.left.as_ref(), context)?,
                                    render_obj(left_inner.right.as_ref(), context)?,
                                    render_obj(left_outer.right.as_ref(), context)?
                                ));
                            }
                        }
                    }
                }
            }
            let reversed: Fact =
                EqualFact::new(right.clone(), left.clone(), fact.line_file()).into();
            Ok(symmetric(render_structural_set_equality(
                &reversed, rule, context,
            )?))
        }
        LeanSetBuiltinCompilationKind::UnionIdempotent => {
            if let Obj::Union(union) = left {
                if obj_equality_key(union.left.as_ref()) == obj_equality_key(union.right.as_ref())
                    && obj_equality_key(union.left.as_ref()) == obj_equality_key(right)
                {
                    return Ok(format!(
                        "Litex.SetRules.unionIdempotent {}",
                        render_obj(right, context)?
                    ));
                }
            }
            if let Obj::Union(union) = right {
                if obj_equality_key(union.left.as_ref()) == obj_equality_key(union.right.as_ref())
                    && obj_equality_key(union.left.as_ref()) == obj_equality_key(left)
                {
                    return Ok(symmetric(format!(
                        "Litex.SetRules.unionIdempotent {}",
                        render_obj(left, context)?
                    )));
                }
            }
            Err("union idempotence changed its repeated operand".into())
        }
        LeanSetBuiltinCompilationKind::UnionEmptyIdentity => {
            for (union_side, plain_side, reverse) in [(left, right, false), (right, left, true)] {
                let Obj::Union(union) = union_side else {
                    continue;
                };
                let left_empty =
                    matches!(union.left.as_ref(), Obj::ListSet(set) if set.list.is_empty());
                let right_empty =
                    matches!(union.right.as_ref(), Obj::ListSet(set) if set.list.is_empty());
                let operand = if left_empty {
                    union.right.as_ref()
                } else if right_empty {
                    union.left.as_ref()
                } else {
                    continue;
                };
                if obj_equality_key(operand) != obj_equality_key(plain_side) {
                    continue;
                }
                let theorem = if left_empty {
                    "unionEmptyLeft"
                } else {
                    "unionEmptyRight"
                };
                let proof = format!(
                    "Litex.SetRules.{theorem} {}",
                    render_obj(plain_side, context)?
                );
                return Ok(if reverse { symmetric(proof) } else { proof });
            }
            Err("union empty identity changed its empty or retained operand".into())
        }
        LeanSetBuiltinCompilationKind::IntersectCommutative => {
            let (Obj::Intersect(left_intersection), Obj::Intersect(right_intersection)) =
                (left, right)
            else {
                return Err("intersection commutativity changed its constructors".into());
            };
            if obj_equality_key(left_intersection.left.as_ref())
                != obj_equality_key(right_intersection.right.as_ref())
                || obj_equality_key(left_intersection.right.as_ref())
                    != obj_equality_key(right_intersection.left.as_ref())
            {
                return Err("intersection commutativity changed its swapped operands".into());
            }
            Ok(format!(
                "Litex.SetRules.intersectCommutative {} {}",
                render_obj(left_intersection.left.as_ref(), context)?,
                render_obj(left_intersection.right.as_ref(), context)?
            ))
        }
        LeanSetBuiltinCompilationKind::IntersectAssociative => {
            if let (Obj::Intersect(left_outer), Obj::Intersect(right_outer)) = (left, right) {
                if let Obj::Intersect(left_inner) = left_outer.left.as_ref() {
                    if obj_equality_key(left_inner.left.as_ref())
                        == obj_equality_key(right_outer.left.as_ref())
                    {
                        if let Obj::Intersect(right_inner) = right_outer.right.as_ref() {
                            if obj_equality_key(left_inner.right.as_ref())
                                == obj_equality_key(right_inner.left.as_ref())
                                && obj_equality_key(left_outer.right.as_ref())
                                    == obj_equality_key(right_inner.right.as_ref())
                            {
                                return Ok(format!(
                                    "Litex.SetRules.intersectAssociative {} {} {}",
                                    render_obj(left_inner.left.as_ref(), context)?,
                                    render_obj(left_inner.right.as_ref(), context)?,
                                    render_obj(left_outer.right.as_ref(), context)?
                                ));
                            }
                        }
                    }
                }
            }
            let reversed: Fact =
                EqualFact::new(right.clone(), left.clone(), fact.line_file()).into();
            Ok(symmetric(render_structural_set_equality(
                &reversed, rule, context,
            )?))
        }
        _ => Err("non-equality set rule reached structural equality renderer".into()),
    }
}

pub(super) fn render_list_set_membership_elimination_from_fact_and_proof(
    target: &Fact,
    source_membership: &Fact,
    source_proof: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (element, set) = membership_parts(source_membership)?;
    let Obj::ListSet(list_set) = set else {
        return Err("list-set membership elimination cites another set constructor".into());
    };
    if list_set.list.is_empty() {
        return Err("empty list-set membership cannot produce an equality branch".into());
    }
    let target_components = if list_set.list.len() == 1 {
        vec![target.clone()]
    } else {
        disjunction_components(target)?
    };
    if target_components.len() != list_set.list.len() {
        return Err("list-set membership inference changed its branch count".into());
    }
    for (component, item) in target_components.iter().zip(list_set.list.iter()) {
        let (left, right) = equality_parts(component)?;
        if obj_equality_key(left) != obj_equality_key(element)
            || obj_equality_key(right) != obj_equality_key(item.as_ref())
        {
            return Err(
                "list-set membership inference changed its ordered equality branches".into(),
            );
        }
    }
    render_fact(target, context)?;
    let item_terms = list_set
        .list
        .iter()
        .map(|item| render_obj(item.as_ref(), context))
        .collect::<Result<Vec<_>, _>>()?;
    let mut lines = vec![
        "(by".to_string(),
        format!("  rcases ({source_proof}) with ⟨__member, __same⟩"),
    ];
    render_list_set_elimination_cases(&item_terms, 0, "__member", "  ", &mut lines);
    lines.push(")".into());
    Ok(lines.join("\n"))
}

pub(super) fn render_list_set_elimination_cases(
    item_terms: &[String],
    index: usize,
    member: &str,
    indent: &str,
    lines: &mut Vec<String>,
) {
    let head = format!("__head{index}");
    let tail = format!("__tail{index}");
    lines.push(format!("{indent}cases {member} with"));
    lines.push(format!("{indent}| inl {head} =>"));
    lines.push(format!("{indent}  cases {head}"));
    let (_, representation) = render_list_set_representation_bridge(&item_terms[index], index);
    let equality = format!("Litex.Same.trans __same (Litex.Same.symm ({representation}))");
    lines.push(format!(
        "{indent}  exact {}",
        inject_disjunction_branch(equality, index, item_terms.len())
    ));
    lines.push(format!("{indent}| inr {tail} =>"));
    if index + 1 == item_terms.len() {
        lines.push(format!("{indent}  exact PEmpty.elim {tail}"));
    } else {
        render_list_set_elimination_cases(
            item_terms,
            index + 1,
            &tail,
            &format!("{indent}  "),
            lines,
        );
    }
}

pub(super) fn inject_disjunction_branch(
    mut proof: String,
    selected_index: usize,
    branch_count: usize,
) -> String {
    if branch_count == 1 {
        return proof;
    }
    if selected_index + 1 < branch_count {
        proof = format!("Or.inl ({proof})");
    }
    for _ in 0..selected_index {
        proof = format!("Or.inr ({proof})");
    }
    proof
}

pub(super) fn render_list_set_representation_bridge(
    selected_term: &str,
    selected_index: usize,
) -> (String, String) {
    let mut witness = "Litex.SingletonCarrier.element".to_string();
    let mut representation = format!("Litex.Same.singleton {selected_term}");
    representation =
        format!("Litex.Same.trans ({representation}) (Litex.Same.sumLeft ({witness}))");
    witness = format!("Sum.inl ({witness})");
    for _ in 0..selected_index {
        representation =
            format!("Litex.Same.trans ({representation}) (Litex.Same.sumRight ({witness}))");
        witness = format!("Sum.inr ({witness})");
    }
    (witness, representation)
}

pub(super) fn infer_rule_has_direct_compiler_environment_consumer(rule: &InferRule) -> bool {
    match rule {
        InferRule::NaturalMembershipImpliesNonnegative => true,
        InferRule::PositiveStandardSetMembershipImpliesPositive(rule) => {
            matches!(
                rule.source_set,
                StandardSet::NPos | StandardSet::QPos | StandardSet::RPos
            )
        }
        InferRule::NegativeStandardSetMembershipImpliesNegative(rule) => {
            matches!(
                rule.source_set,
                StandardSet::ZNeg | StandardSet::QNeg | StandardSet::RNeg
            )
        }
        InferRule::NonzeroStandardSetMembershipImpliesNonzero(rule) => matches!(
            rule.source_set,
            StandardSet::ZStar | StandardSet::QStar | StandardSet::RStar | StandardSet::CStar
        ),
        InferRule::MultiplicationByNegativeOneReversesOrderAgainstZero
        | InferRule::StrictOrderComparedToZeroImpliesWeakOrder => true,
        InferRule::MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(_) => true,
        InferRule::SubsetImpliesElementwiseMembershipForall(_)
        | InferRule::SupersetImpliesElementwiseMembershipForall(_)
        | InferRule::ConjunctionImpliesComponent(_) => true,
        InferRule::SetBuilderBaseMembershipProjection
        | InferRule::SetBuilderPredicateProjection { .. }
        | InferRule::DefinedPredicateParameterRequirementProjection(_)
        | InferRule::DefinedPredicateDefinitionClauseProjection(_)
        | InferRule::RegisteredTransitivePredicateChainClosure(_)
        | InferRule::TupleEqualityWithKnownTupleImpliesTupleShape(_)
        | InferRule::ListSetMembershipImpliesEqualityAlternatives(_) => false,
    }
}

pub(super) fn infer_result_effects_are_fully_owned_by_direct_compiler_rules(
    result: &SuccessInferResult,
) -> bool {
    let advertised = result
        .store_fact_outputs
        .iter()
        .flat_map(|output| {
            output
                .inferred_facts
                .iter()
                .zip(output.inferred_fact_ids.iter())
                .filter_map(|(fact, fact_id)| fact_id.map(|fact_id| (fact_id, fact.to_string())))
        })
        .collect::<HashSet<_>>();
    let mut typed = HashSet::new();
    collect_supported_typed_infer_conclusions(result, &mut typed);
    typed.retain(|conclusion| advertised.contains(conclusion));
    advertised == typed
}

pub(super) fn collect_supported_typed_infer_conclusions(
    result: &SuccessInferResult,
    conclusions: &mut HashSet<(FactId, String)>,
) {
    for application in &result.rule_applications {
        if !infer_rule_has_direct_compiler_environment_consumer(&application.rule) {
            continue;
        }
        for conclusion in &application.conclusions {
            if let Some(fact_id) = conclusion.fact_id {
                conclusions.insert((fact_id, conclusion.fact.to_string()));
            }
            collect_supported_typed_infer_conclusions(&conclusion.infers, conclusions);
        }
    }
}

pub(super) fn validate_order_sign_inference_target(
    rule: &InferRule,
    source: &Fact,
    target: &Fact,
) -> Result<(), String> {
    let (source_left, source_right, source_strict) = order_relation_parts(source)?;
    let (target_left, target_right, target_strict) = order_relation_parts(target)?;
    let zero =
        |object: &Obj| matches!(object, Obj::Number(number) if number.normalized_value == "0");
    match rule {
        InferRule::MultiplicationByNegativeOneReversesOrderAgainstZero => {
            let (source_expression, source_expression_is_left) = if zero(source_right) {
                (source_left, true)
            } else if zero(source_left) {
                (source_right, false)
            } else {
                return Err("negative-one order inference source is not compared with zero".into());
            };
            let (target_expression, target_expression_is_left) = if zero(target_right) {
                (target_left, true)
            } else if zero(target_left) {
                (target_right, false)
            } else {
                return Err("negative-one order inference target is not compared with zero".into());
            };
            let Obj::Mul(multiplication) = target_expression else {
                return Err("negative-one order inference target is not a multiplication".into());
            };
            if !matches!(multiplication.left.as_ref(), Obj::Number(number) if number.normalized_value == "-1")
                || obj_equality_key(multiplication.right.as_ref())
                    != obj_equality_key(source_expression)
                || source_expression_is_left == target_expression_is_left
            {
                return Err(
                    "negative-one order inference changed its operand or reversal orientation"
                        .into(),
                );
            }
            let expected_target_strict = source_strict && !source_expression_is_left;
            if target_strict != expected_target_strict {
                return Err("negative-one order inference changed its strictness contract".into());
            }
            Ok(())
        }
        InferRule::StrictOrderComparedToZeroImpliesWeakOrder => {
            if !source_strict
                || target_strict
                || obj_equality_key(source_left) != obj_equality_key(target_left)
                || obj_equality_key(source_right) != obj_equality_key(target_right)
                || !zero(source_right)
            {
                return Err("strict-to-weak zero-order inference changed its endpoints".into());
            }
            Ok(())
        }
        _ => Err("non-order inference reached order-sign validation".into()),
    }
}

pub(super) fn validate_membership_in_equal_set_inference_target(
    rule: &MembershipInSetWithKnownEqualityImpliesMembershipInEqualSetInferRule,
    source: &Fact,
    equality: &Fact,
    target: &Fact,
) -> Result<(), String> {
    let (source_element, source_set) = membership_parts(source)?;
    let (target_element, target_set) = membership_parts(target)?;
    let (equality_left, equality_right) = equality_parts(equality)?;
    if obj_equality_key(source_element) != obj_equality_key(target_element) {
        return Err("equal-set membership inference changed its element".into());
    }
    let (expected_left, expected_right) = match rule.equality_orientation {
        KnownSetEqualityOrientation::SourceSetOnLeft => (source_set, target_set),
        KnownSetEqualityOrientation::SourceSetOnRight => (target_set, source_set),
    };
    if obj_equality_key(equality_left) != obj_equality_key(expected_left)
        || obj_equality_key(equality_right) != obj_equality_key(expected_right)
    {
        return Err("equal-set membership inference changed its retained equality".into());
    }
    Ok(())
}

pub(super) fn validate_set_inclusion_elementwise_forall_inference_target(
    rule: &InferRule,
    source: &Fact,
    target: &Fact,
) -> Result<(), String> {
    let (expected_parameter_set, expected_target_set, binder_symbol_id) = match (rule, source) {
        (
            InferRule::SubsetImpliesElementwiseMembershipForall(rule),
            Fact::AtomicFact(AtomicFact::SubsetFact(source)),
        ) => (&source.left, &source.right, rule.binder_symbol_id),
        (
            InferRule::SupersetImpliesElementwiseMembershipForall(rule),
            Fact::AtomicFact(AtomicFact::SupersetFact(source)),
        ) => (&source.right, &source.left, rule.binder_symbol_id),
        (InferRule::SubsetImpliesElementwiseMembershipForall(_), _) => {
            return Err("subset elementwise inference retained a non-subset premise".into());
        }
        (InferRule::SupersetImpliesElementwiseMembershipForall(_), _) => {
            return Err("superset elementwise inference retained a non-superset premise".into());
        }
        _ => return Err("non-inclusion inference reached elementwise-forall validation".into()),
    };
    let Fact::ForallFact(target) = target else {
        return Err("set-inclusion inference conclusion is not a forall fact".into());
    };
    let [parameter_group] = target.typed_parameters.groups.as_slice() else {
        return Err("set-inclusion inference conclusion changed its parameter-group arity".into());
    };
    let [parameter] = parameter_group.params.as_slice() else {
        return Err("set-inclusion inference conclusion changed its binder arity".into());
    };
    let ParamType::Obj(parameter_set) = &parameter_group.param_type else {
        return Err("set-inclusion inference conclusion binder is not object-valued".into());
    };
    if parameter.id() != binder_symbol_id
        || obj_equality_key(parameter_set) != obj_equality_key(expected_parameter_set)
        || !target.dom_facts.is_empty()
        || target.then_facts.len() != 1
    {
        return Err(
            "set-inclusion inference changed its binder identity, carrier, or forall shape".into(),
        );
    }
    let target_membership = target.then_facts[0].clone().to_fact();
    let (target_element, target_set) = membership_parts(&target_membership)?;
    let expected_element = obj_for_bound_param_in_scope(parameter);
    if obj_equality_key(target_element) != obj_equality_key(&expected_element)
        || obj_equality_key(target_set) != obj_equality_key(expected_target_set)
    {
        return Err("set-inclusion inference changed its elementwise membership target".into());
    }
    Ok(())
}

pub(super) fn validate_conjunction_component_inference_target(
    rule: &ConjunctionImpliesComponentInferRule,
    source: &Fact,
    target: &Fact,
) -> Result<(), String> {
    let Fact::AndFact(source) = source else {
        return Err("conjunction-component inference retained a non-conjunction premise".into());
    };
    if rule.component_count != source.facts.len() || rule.component_index >= rule.component_count {
        return Err("conjunction-component inference changed its component bounds".into());
    }
    let expected: Fact = source.facts[rule.component_index].clone().into();
    if expected.to_string() != target.to_string() {
        return Err("conjunction-component inference changed its selected component".into());
    }
    Ok(())
}

pub(super) fn validate_standard_numeric_membership_inference_target(
    rule: &InferRule,
    source: &Fact,
    target: &Fact,
) -> Result<&'static str, String> {
    let (source_element, source_set) = membership_parts(source)?;
    let (target_element, lean_theorem_name) = match rule {
        InferRule::NaturalMembershipImpliesNonnegative => {
            if !matches!(source_set, Obj::StandardSet(StandardSet::N)) {
                return Err("natural-membership inference source is not in N".into());
            }
            let target_element = match target {
                Fact::AtomicFact(AtomicFact::GreaterEqualFact(order)) if matches!(&order.right, Obj::Number(number) if number.normalized_value == "0") => {
                    &order.left
                }
                Fact::AtomicFact(AtomicFact::LessEqualFact(order)) if matches!(&order.left, Obj::Number(number) if number.normalized_value == "0") => {
                    &order.right
                }
                _ => {
                    return Err(
                        "natural-membership inference target is not nonnegativity of its source object"
                            .into(),
                    );
                }
            };
            (target_element, "nonnegativeOfInN")
        }
        InferRule::PositiveStandardSetMembershipImpliesPositive(rule) => {
            if !matches!(source_set, Obj::StandardSet(set) if *set == rule.source_set) {
                return Err(
                    "positive-carrier inference source does not match its typed source set".into(),
                );
            }
            let target_element = match target {
                Fact::AtomicFact(AtomicFact::LessFact(order)) if matches!(&order.left, Obj::Number(number) if number.normalized_value == "0") => {
                    &order.right
                }
                Fact::AtomicFact(AtomicFact::GreaterFact(order)) if matches!(&order.right, Obj::Number(number) if number.normalized_value == "0") => {
                    &order.left
                }
                _ => {
                    return Err(
                        "positive-carrier inference target is not strict positivity of its source object"
                            .into(),
                    );
                }
            };
            let lean_theorem_name = match rule.source_set {
                StandardSet::NPos => "positiveOfInNPos",
                StandardSet::QPos => "positiveOfInQPos",
                StandardSet::RPos => "positiveOfInRPos",
                _ => {
                    return Err(format!(
                        "positive-carrier inference from {} has no direct Lean theorem",
                        rule.source_set
                    ));
                }
            };
            (target_element, lean_theorem_name)
        }
        InferRule::NegativeStandardSetMembershipImpliesNegative(rule) => {
            if !matches!(source_set, Obj::StandardSet(set) if *set == rule.source_set) {
                return Err(
                    "negative-carrier inference source does not match its typed source set".into(),
                );
            }
            let target_element = match target {
                Fact::AtomicFact(AtomicFact::LessFact(order)) if matches!(&order.right, Obj::Number(number) if number.normalized_value == "0") => {
                    &order.left
                }
                Fact::AtomicFact(AtomicFact::GreaterFact(order)) if matches!(&order.left, Obj::Number(number) if number.normalized_value == "0") => {
                    &order.right
                }
                _ => {
                    return Err(
                        "negative-carrier inference target is not strict negativity of its source object"
                            .into(),
                    );
                }
            };
            let lean_theorem_name = match rule.source_set {
                StandardSet::ZNeg => "negativeOfInZNeg",
                StandardSet::QNeg => "negativeOfInQNeg",
                StandardSet::RNeg => "negativeOfInRNeg",
                _ => {
                    return Err(format!(
                        "negative-carrier inference from {} has no direct Lean theorem",
                        rule.source_set
                    ));
                }
            };
            (target_element, lean_theorem_name)
        }
        InferRule::NonzeroStandardSetMembershipImpliesNonzero(rule) => {
            if !matches!(source_set, Obj::StandardSet(set) if *set == rule.source_set) {
                return Err(
                    "nonzero-carrier inference source does not match its typed source set".into(),
                );
            }
            let target_element = match target {
                Fact::AtomicFact(AtomicFact::NotEqualFact(not_equal)) if matches!(&not_equal.right, Obj::Number(number) if number.normalized_value == "0") => {
                    &not_equal.left
                }
                _ => {
                    return Err(
                        "nonzero-carrier inference target is not source-object inequality with zero"
                            .into(),
                    );
                }
            };
            let lean_theorem_name = match rule.source_set {
                StandardSet::ZStar => "notSameZeroOfInZStar",
                StandardSet::QStar => "notSameZeroOfInQStar",
                StandardSet::RStar => "notSameZeroOfInRStar",
                StandardSet::CStar => "notSameZeroOfInCStar",
                _ => {
                    return Err(format!(
                        "nonzero-carrier inference from {} has no direct Lean theorem",
                        rule.source_set
                    ));
                }
            };
            (target_element, lean_theorem_name)
        }
        _ => return Err("unsupported standard numeric inference rule".into()),
    };
    if obj_equality_key(source_element) != obj_equality_key(target_element) {
        return Err("standard numeric inference changed its source object".into());
    }
    Ok(lean_theorem_name)
}

pub(super) fn render_numeric_operand_membership(
    object: &Obj,
    fallback: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> String {
    let proof = match LeanTargetObjectRepresentation::lower(object) {
        Ok(LeanTargetObjectRepresentation::Symbol { symbol_id, .. }) => {
            context.numeric_representation_memberships.get(&symbol_id)
        }
        _ => None,
    };
    proof.map_or_else(|| fallback.to_string(), Clone::clone)
}

pub(super) fn render_additive_sign_rule_from_compiled_children(
    fact: &Fact,
    rule: LeanArithmeticBuiltinCompilationKind,
    premises: &[CompiledFactProofBody],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if premises.len() != 2 {
        return Err("additive sign rule requires two ordered child Results".into());
    }
    let (target_is_strict, left_is_strict, right_is_strict, theorem) = match rule {
        LeanArithmeticBuiltinCompilationKind::AddNonnegative => {
            (false, false, false, "complexAddNonnegative")
        }
        LeanArithmeticBuiltinCompilationKind::AddPositive => {
            (true, true, true, "complexAddPositive")
        }
        LeanArithmeticBuiltinCompilationKind::AddPositiveLeftStrict => {
            (true, true, false, "complexAddPositiveLeftStrict")
        }
        LeanArithmeticBuiltinCompilationKind::AddPositiveRightStrict => {
            (true, false, true, "complexAddPositiveRightStrict")
        }
        LeanArithmeticBuiltinCompilationKind::MulNonnegative => {
            (false, false, false, "complexMulNonnegative")
        }
        LeanArithmeticBuiltinCompilationKind::MulPositive => {
            (true, true, true, "complexMulPositive")
        }
        LeanArithmeticBuiltinCompilationKind::DivNonnegative => {
            (false, false, true, "complexDivNonnegative")
        }
        LeanArithmeticBuiltinCompilationKind::DivPositive => {
            (true, true, true, "complexDivPositive")
        }
    };

    let (target_zero, target_expression) = positive_order_parts(fact, target_is_strict)?;
    let (target_left, target_right) = match (rule, target_expression) {
        (
            LeanArithmeticBuiltinCompilationKind::AddNonnegative
            | LeanArithmeticBuiltinCompilationKind::AddPositive
            | LeanArithmeticBuiltinCompilationKind::AddPositiveLeftStrict
            | LeanArithmeticBuiltinCompilationKind::AddPositiveRightStrict,
            Obj::Add(operation),
        ) => (operation.left.as_ref(), operation.right.as_ref()),
        (
            LeanArithmeticBuiltinCompilationKind::MulNonnegative
            | LeanArithmeticBuiltinCompilationKind::MulPositive,
            Obj::Mul(operation),
        ) => (operation.left.as_ref(), operation.right.as_ref()),
        (
            LeanArithmeticBuiltinCompilationKind::DivNonnegative
            | LeanArithmeticBuiltinCompilationKind::DivPositive,
            Obj::Div(operation),
        ) => (operation.left.as_ref(), operation.right.as_ref()),
        _ => {
            return Err(format!(
                "sign builtin rule {rule:?} changed its target operator"
            ));
        }
    };
    let (left_zero, left_operand) = positive_order_parts(&premises[0].fact, left_is_strict)?;
    let (right_zero, right_operand) = positive_order_parts(&premises[1].fact, right_is_strict)?;
    if target_zero.to_string() != "0"
        || left_zero.to_string() != "0"
        || right_zero.to_string() != "0"
    {
        return Err("sign builtin rule changed its zero endpoint".into());
    }
    if obj_equality_key(target_left) != obj_equality_key(left_operand)
        || obj_equality_key(target_right) != obj_equality_key(right_operand)
    {
        return Err("sign builtin rule premises do not match its ordered operands".into());
    }

    render_fact(fact, context)?;
    let left = transport_zero_ended_order_proof_to_rendered_numeric_operand(
        left_operand,
        left_is_strict,
        &premises[0].proof_expression,
        context,
    )?;
    let right = transport_zero_ended_order_proof_to_rendered_numeric_operand(
        right_operand,
        right_is_strict,
        &premises[1].proof_expression,
        context,
    )?;
    Ok(format!("Litex.Rules.{theorem} ({left}) ({right})"))
}

/// A source-domain sign premise is stated about the heterogeneous parameter,
/// while arithmetic target expressions use the exact numeric Complex
/// representative selected by that parameter's membership proof. Transport
/// only across the equality bridge installed by the active compiler frame.
pub(super) fn transport_zero_ended_order_proof_to_rendered_numeric_operand(
    source_operand: &Obj,
    strict: bool,
    source_proof: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let rendered_source = render_obj(source_operand, context)?;
    let rendered_target = render_numeric_obj(source_operand, context)?;
    if rendered_source == rendered_target {
        return Ok(source_proof.to_string());
    }
    let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
        LeanTargetObjectRepresentation::lower(source_operand)?
    else {
        return Err(format!(
            "sign proof changed `{rendered_source}` to unrelated numeric target `{rendered_target}`"
        ));
    };
    let equality = context
        .numeric_representation_equalities
        .get(&symbol_id)
        .ok_or_else(|| {
            format!(
                "sign proof for `{rendered_source}` has no visible exact numeric equality bridge"
            )
        })?;
    let predicate = if strict {
        "Litex.Positive"
    } else {
        "Litex.Nonnegative"
    };
    Ok(format!(
        "({predicate}.congr ({equality})).mp ({source_proof})"
    ))
}

/// Transport the exact sign proposition retained by one typed infer premise
/// from its source object to the numeric representative selected in the
/// current compiler frame. Both zero orientations are supported because
/// Litex stores positive/nonnegative and negative/nonpositive facts as
/// distinct source comparisons.
pub(super) fn transport_zero_ended_order_fact_proof_to_current_numeric_representation(
    source_fact: &Fact,
    source_proof: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (source_left, source_right, strict) = order_relation_parts(source_fact)?;
    let (source_operand, predicate) = if is_literal_zero(source_left) {
        (
            source_right,
            if strict {
                "Litex.Positive"
            } else {
                "Litex.Nonnegative"
            },
        )
    } else if is_literal_zero(source_right) {
        (
            source_left,
            if strict {
                "Litex.Negative"
            } else {
                "Litex.Nonpositive"
            },
        )
    } else {
        return Err(format!(
            "typed zero-order inference retained a nonzero-ended premise `{source_fact}`"
        ));
    };

    let rendered_source = render_obj(source_operand, context)?;
    let rendered_target = render_numeric_obj(source_operand, context)?;
    if rendered_source == rendered_target {
        return Ok(source_proof.to_string());
    }
    let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
        LeanTargetObjectRepresentation::lower(source_operand)?
    else {
        return Err(format!(
            "zero-order proof changed `{rendered_source}` to unrelated numeric target `{rendered_target}`"
        ));
    };
    let equality = context
        .numeric_representation_equalities
        .get(&symbol_id)
        .ok_or_else(|| {
            format!(
                "zero-order proof for `{rendered_source}` has no visible exact numeric equality bridge"
            )
        })?;
    Ok(format!(
        "({predicate}.congr ({equality})).mp ({source_proof})"
    ))
}

pub(super) fn render_real_operand_membership(
    object: &Obj,
    fallback: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> String {
    let real = match LeanTargetObjectRepresentation::lower(object) {
        Ok(LeanTargetObjectRepresentation::Symbol { symbol_id, .. }) => {
            context.numeric_real_values.get(&symbol_id)
        }
        _ => None,
    };
    real.map_or_else(
        || fallback.to_string(),
        |real| format!("Litex.Rules.complexRealInR ({real})"),
    )
}

pub(super) fn registered_set_rule(
    rule_id: &RuleId,
    semantic_fingerprint: &RuleFingerprint,
) -> Option<(LeanSetBuiltinCompilationKind, usize, usize)> {
    let fingerprint = semantic_fingerprint.as_hex();
    Some(match rule_id.as_str() {
        SET_EMPTY_SUBSET_RULE_ID if fingerprint == SET_EMPTY_SUBSET_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::EmptySubset, 1, 0)
        }
        SET_UNION_ASSOCIATIVE_RULE_ID if fingerprint == SET_UNION_ASSOCIATIVE_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::UnionAssociative, 3, 0)
        }
        SET_UNION_COMMUTATIVE_RULE_ID if fingerprint == SET_UNION_COMMUTATIVE_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::UnionCommutative, 2, 0)
        }
        SET_UNION_EMPTY_LEFT_RULE_ID if fingerprint == SET_UNION_EMPTY_LEFT_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::UnionEmptyIdentity, 1, 0)
        }
        SET_UNION_EMPTY_RIGHT_RULE_ID if fingerprint == SET_UNION_EMPTY_RIGHT_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::UnionEmptyIdentity, 1, 0)
        }
        SET_UNION_IDEMPOTENT_RULE_ID if fingerprint == SET_UNION_IDEMPOTENT_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::UnionIdempotent, 1, 0)
        }
        SET_UNION_MEMBERSHIP_LEFT_RULE_ID
            if fingerprint == SET_UNION_MEMBERSHIP_LEFT_FINGERPRINT =>
        {
            (LeanSetBuiltinCompilationKind::UnionMembershipLeft, 3, 1)
        }
        SET_UNION_MEMBERSHIP_RIGHT_RULE_ID
            if fingerprint == SET_UNION_MEMBERSHIP_RIGHT_FINGERPRINT =>
        {
            (LeanSetBuiltinCompilationKind::UnionMembershipRight, 3, 1)
        }
        SET_INTERSECT_ASSOCIATIVE_RULE_ID
            if fingerprint == SET_INTERSECT_ASSOCIATIVE_FINGERPRINT =>
        {
            (LeanSetBuiltinCompilationKind::IntersectAssociative, 3, 0)
        }
        SET_INTERSECT_COMMUTATIVE_RULE_ID
            if fingerprint == SET_INTERSECT_COMMUTATIVE_FINGERPRINT =>
        {
            (LeanSetBuiltinCompilationKind::IntersectCommutative, 2, 0)
        }
        SET_INTERSECT_MEMBERSHIP_RULE_ID if fingerprint == SET_INTERSECT_MEMBERSHIP_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::IntersectMembershipBoth, 3, 2)
        }
        SET_MINUS_MEMBERSHIP_RULE_ID if fingerprint == SET_MINUS_MEMBERSHIP_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::SetMinusMembership, 3, 2)
        }
        SET_INTERSECT_EQ_LEFT_OF_SUBSET_RULE_ID
            if fingerprint == SET_INTERSECT_EQ_LEFT_OF_SUBSET_FINGERPRINT =>
        {
            (LeanSetBuiltinCompilationKind::IntersectEqLeftOfSubset, 2, 1)
        }
        SET_INTERSECT_EQ_RIGHT_OF_SUBSET_RULE_ID
            if fingerprint == SET_INTERSECT_EQ_RIGHT_OF_SUBSET_FINGERPRINT =>
        {
            (
                LeanSetBuiltinCompilationKind::IntersectEqRightOfSubset,
                2,
                1,
            )
        }
        SET_INTERSECT_FINITE_RULE_ID if fingerprint == SET_INTERSECT_FINITE_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::IntersectFinite, 2, 2)
        }
        SET_INTERSECT_SUBSET_LEFT_RULE_ID
            if fingerprint == SET_INTERSECT_SUBSET_LEFT_FINGERPRINT =>
        {
            (LeanSetBuiltinCompilationKind::IntersectSubsetLeft, 2, 0)
        }
        SET_INTERSECT_SUBSET_RIGHT_RULE_ID
            if fingerprint == SET_INTERSECT_SUBSET_RIGHT_FINGERPRINT =>
        {
            (LeanSetBuiltinCompilationKind::IntersectSubsetRight, 2, 0)
        }
        SET_INTERSECT_UNION_DISTRIBUTIVE_RULE_ID
            if fingerprint == SET_INTERSECT_UNION_DISTRIBUTIVE_FINGERPRINT =>
        {
            (
                LeanSetBuiltinCompilationKind::IntersectUnionDistributive,
                3,
                0,
            )
        }
        SET_POWER_SET_FINITE_RULE_ID if fingerprint == SET_POWER_SET_FINITE_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::PowerSetFinite, 1, 1)
        }
        SET_POWER_SET_MEMBERSHIP_OF_SUBSET_RULE_ID
            if fingerprint == SET_POWER_SET_MEMBERSHIP_OF_SUBSET_FINGERPRINT =>
        {
            (
                LeanSetBuiltinCompilationKind::PowerSetMembershipOfSubset,
                2,
                1,
            )
        }
        SET_POWER_SET_NONEMPTY_RULE_ID if fingerprint == SET_POWER_SET_NONEMPTY_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::PowerSetNonempty, 1, 0)
        }
        SET_MINUS_FINITE_LEFT_RULE_ID if fingerprint == SET_MINUS_FINITE_LEFT_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::SetMinusFiniteLeft, 2, 1)
        }
        SET_MINUS_INTERSECT_DE_MORGAN_RULE_ID
            if fingerprint == SET_MINUS_INTERSECT_DE_MORGAN_FINGERPRINT =>
        {
            (
                LeanSetBuiltinCompilationKind::SetMinusIntersectDeMorgan,
                3,
                0,
            )
        }
        SET_MINUS_RECOVER_SUBSET_RULE_ID if fingerprint == SET_MINUS_RECOVER_SUBSET_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::SetMinusRecoverSubset, 2, 1)
        }
        SET_MINUS_SUBSET_LEFT_RULE_ID if fingerprint == SET_MINUS_SUBSET_LEFT_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::SetMinusSubsetLeft, 2, 0)
        }
        SET_MINUS_UNION_DE_MORGAN_RULE_ID
            if fingerprint == SET_MINUS_UNION_DE_MORGAN_FINGERPRINT =>
        {
            (LeanSetBuiltinCompilationKind::SetMinusUnionDeMorgan, 3, 0)
        }
        SET_SUBSET_EQ_SET_MINUS_RECOVERY_RULE_ID
            if fingerprint == SET_SUBSET_EQ_SET_MINUS_RECOVERY_FINGERPRINT =>
        {
            (
                LeanSetBuiltinCompilationKind::SubsetEqSetMinusRecovery,
                2,
                1,
            )
        }
        SET_SUBSET_UNION_LEFT_RULE_ID if fingerprint == SET_SUBSET_UNION_LEFT_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::SubsetUnionLeft, 2, 0)
        }
        SET_SUBSET_UNION_RIGHT_RULE_ID if fingerprint == SET_SUBSET_UNION_RIGHT_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::SubsetUnionRight, 2, 0)
        }
        SET_UNION_FINITE_RULE_ID if fingerprint == SET_UNION_FINITE_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::UnionFinite, 2, 2)
        }
        SET_UNION_NONEMPTY_LEFT_RULE_ID if fingerprint == SET_UNION_NONEMPTY_LEFT_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::UnionNonemptyLeft, 2, 1)
        }
        SET_UNION_NONEMPTY_RIGHT_RULE_ID if fingerprint == SET_UNION_NONEMPTY_RIGHT_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::UnionNonemptyRight, 2, 1)
        }
        SET_UNION_SUBSET_RULE_ID if fingerprint == SET_UNION_SUBSET_FINGERPRINT => {
            (LeanSetBuiltinCompilationKind::UnionSubset, 3, 2)
        }
        _ => return None,
    })
}
