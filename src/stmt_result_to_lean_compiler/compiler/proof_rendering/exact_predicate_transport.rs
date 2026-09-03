//! Exact predicate instantiation and argument transport.

use super::super::*;

fn render_real_to_complex_same_across_contexts(
    object: &Obj,
    real_context: &StmtResultToLeanCompilerEnvironmentStack,
    complex_context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (theorem, left, right) = match object {
        Obj::Add(operation) => (
            "Litex.Same.realAddComplex",
            operation.left.as_ref(),
            operation.right.as_ref(),
        ),
        Obj::Sub(operation) => (
            "Litex.Same.realSubComplex",
            operation.left.as_ref(),
            operation.right.as_ref(),
        ),
        Obj::Mul(operation) => (
            "Litex.Same.realMulComplex",
            operation.left.as_ref(),
            operation.right.as_ref(),
        ),
        Obj::Div(operation) => (
            "Litex.Same.realDivComplex",
            operation.left.as_ref(),
            operation.right.as_ref(),
        ),
        _ => {
            let real = render_real_source_object(object, real_context)?;
            render_numeric_obj(object, complex_context)?;
            return Ok(format!("Litex.Same.realComplex ({real})"));
        }
    };
    let left = render_real_to_complex_same_across_contexts(left, real_context, complex_context)?;
    let right = render_real_to_complex_same_across_contexts(right, real_context, complex_context)?;
    Ok(format!("{theorem} ({left}) ({right})"))
}

fn render_object_same_across_exact_parameter_contexts(
    object: &Obj,
    source_context: &StmtResultToLeanCompilerEnvironmentStack,
    target_context: &StmtResultToLeanCompilerEnvironmentStack,
    source_bridges: &[(SymbolId, String)],
) -> Result<String, String> {
    let source = render_obj(object, source_context)?;
    let target = render_obj(object, target_context)?;
    if source == target {
        return Ok(format!("Litex.Same.refl ({source})"));
    }
    if let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
        LeanTargetObjectRepresentation::lower(object)?
    {
        if let Some((_, bridge)) = source_bridges
            .iter()
            .rev()
            .find(|(candidate, _)| *candidate == symbol_id)
        {
            return Ok(bridge.clone());
        }
    }

    let source_real = render_real_source_object(object, source_context).map_err(|_| {
        format!(
            "exact-parameter object `{object}` changed from `{source}` to `{target}` without a retained Same bridge"
        )
    })?;
    let target_numeric = render_numeric_obj(object, target_context)?;
    let real_to_target =
        render_real_to_complex_same_across_contexts(object, source_context, target_context)?;
    if source == source_real && target == target_numeric {
        return Ok(real_to_target);
    }

    let source_numeric = render_numeric_obj(object, source_context)?;
    if source == source_numeric && target == target_numeric {
        return Ok(format!(
            "Litex.Same.ofEq ((show {source_numeric} = {target_numeric} from (by\n  have __numeric_bridge := ({real_to_target}).complexEq (Litex.AsComplex.real ({source_real})) (Litex.AsComplex.complex ({target_numeric}))\n  norm_cast at __numeric_bridge ⊢)))"
        ));
    }
    Err(format!(
        "exact-parameter object `{object}` changed from `{source}` to `{target}` outside the reviewed real-to-complex transport"
    ))
}

fn objects_match_under_cross_context_symbol_aliases(
    source: &Obj,
    target: &Obj,
    source_context: &StmtResultToLeanCompilerEnvironmentStack,
    target_context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<bool, String> {
    if obj_equality_key(source) == obj_equality_key(target) {
        return Ok(true);
    }
    if matches!((source, target), (Obj::Atom(_), Obj::Atom(_))) {
        return Ok(render_obj(source, source_context)? == render_obj(target, target_context)?);
    }
    Runtime::same_shape_and_corresponding_args_match(source, target, &mut |left, right| {
        objects_match_under_cross_context_symbol_aliases(
            left,
            right,
            source_context,
            target_context,
        )
    })
}

fn render_abstract_predicate_same_equivalence(
    predicate_name: &str,
    source_arguments: &[Obj],
    target_arguments: &[Obj],
    binding: &PredicateBinding,
    source_context: &StmtResultToLeanCompilerEnvironmentStack,
    target_context: &StmtResultToLeanCompilerEnvironmentStack,
    source_bridges: &[(SymbolId, String)],
) -> Result<String, String> {
    let congruence = binding.same_congruence_name.as_ref().ok_or_else(|| {
        format!("abstract predicate `{predicate_name}` has no retained Same-congruence ABI")
    })?;
    if source_arguments.len() != binding.parameter_count
        || target_arguments.len() != binding.parameter_count
    {
        return Err(format!(
            "abstract predicate `{predicate_name}` changed its argument arity during transport"
        ));
    }
    let mut source_values = Vec::with_capacity(binding.parameter_count);
    let mut target_values = Vec::with_capacity(binding.parameter_count);
    let mut same_proofs = Vec::with_capacity(binding.parameter_count);
    for (index, (source_argument, target_argument)) in source_arguments
        .iter()
        .zip(target_arguments.iter())
        .enumerate()
    {
        let source_value =
            render_concrete_predicate_argument(binding, index, source_argument, source_context)?;
        let target_value =
            render_concrete_predicate_argument(binding, index, target_argument, target_context)?;
        let substituted_target_value =
            render_concrete_predicate_argument(binding, index, source_argument, target_context)?;
        if substituted_target_value != target_value {
            return Err(format!(
                "abstract predicate `{predicate_name}` argument {index} did not match its retained substitution"
            ));
        }
        let same = if source_value == target_value {
            format!("Litex.Same.refl ({source_value})")
        } else {
            render_object_same_across_exact_parameter_contexts(
                source_argument,
                source_context,
                target_context,
                source_bridges,
            )?
        };
        source_values.push(source_value);
        target_values.push(target_value);
        same_proofs.push(format!("({same})"));
    }
    Ok(format!(
        "{congruence} {} {} {}",
        source_values.join(" "),
        target_values.join(" "),
        same_proofs.join(" ")
    ))
}

pub(in super::super) fn instantiated_predicate_components(
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
    if let Some(definition_well_definedness) = &binding.definition_well_definedness {
        nested.well_definedness = Some(definition_well_definedness.clone());
    }
    let mut argument_index = 0;
    for group in &definition.typed_parameters.groups {
        for parameter in &group.params {
            let rendered_argument = render_concrete_predicate_argument(
                binding,
                argument_index,
                &source.body[argument_index],
                context,
            )?;
            nested
                .symbol_names
                .insert(parameter.id(), rendered_argument.clone());
            if let ParamType::Obj(set) = &group.param_type {
                if matches!(set, Obj::FnSet(_) | Obj::FiniteSeqSet(_) | Obj::SeqSet(_)) {
                    let definition_well_definedness = binding
                        .definition_well_definedness
                        .as_ref()
                        .ok_or_else(|| {
                            "concrete predicate function parameter has no retained definition WD context"
                                .to_string()
                        })?;
                    let alias = definition_well_definedness
                        .parameter_fact_aliases
                        .iter()
                        .find(|alias| alias.symbol_id == parameter.id())
                        .ok_or_else(|| {
                            format!(
                                "concrete predicate function parameter {argument_index} has no definition FactId alias"
                            )
                        })?;
                    let rendered_set = render_obj(set, &nested)?;
                    let parameter_proof =
                        format!("Litex.In.own {rendered_set} {rendered_argument}");
                    install_parameter_fact_aliases(
                        parameter.id(),
                        alias.fact_id,
                        &alias.proposition,
                        &parameter_proof,
                        set,
                        &mut nested,
                    )?;
                    if binding.exact_parameters[argument_index] {
                        // Every FactId alias for an exact predicate function
                        // parameter denotes the same already-selected carrier.
                        // Leaving an alias in heterogeneous mode lets the
                        // application Result choose `fnApply` even though the
                        // definition itself used `fnApplyOwn`.
                        for function_binding in nested.function_bindings.values_mut() {
                            if function_binding.symbol_id == parameter.id() {
                                function_binding.direct = true;
                            }
                        }
                    }
                }
            }
            if binding.exact_parameters[argument_index] {
                nested
                    .exact_carrier_values
                    .insert(parameter.id(), rendered_argument.clone());
                let ParamType::Obj(set) = &group.param_type else {
                    return Err("exact predicate parameter retained a non-object type".into());
                };
                let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
                if let Some(real) = exact_set_real_value(&lowered_set, &rendered_argument) {
                    nested.numeric_real_values.insert(parameter.id(), real);
                }
                if let Some(integer) = exact_set_integer_value(&lowered_set, &rendered_argument) {
                    nested
                        .numeric_integer_values
                        .insert(parameter.id(), integer);
                }
                if let Some(rational) = exact_set_rational_value(&lowered_set, &rendered_argument) {
                    nested
                        .numeric_rational_values
                        .insert(parameter.id(), rational);
                }
                if let Some(numeric) = exact_set_numeric_value(&lowered_set, &rendered_argument) {
                    nested
                        .numeric_representations
                        .insert(parameter.id(), numeric);
                }
            }
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
                    let argument = render_concrete_predicate_argument(
                        binding,
                        argument_index,
                        &source.body[argument_index],
                        context,
                    )?;
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

pub(in super::super) fn install_exact_predicate_carrier_value(
    symbol_id: SymbolId,
    set: &Obj,
    value: &str,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
    context
        .exact_carrier_values
        .insert(symbol_id, value.to_string());
    // `value` is already an element of the exact carrier selected for the
    // theorem application. For `R` that carrier is definitionally `ℝ`;
    // wrapping an already-ascribed term once more (`((2 : ℝ) : ℝ)`) is
    // harmless to Lean but destroys the compiler's canonical spelling and
    // makes an instantiated parameter look different from the same closed
    // argument at its target occurrence.
    let exact_real = if matches!(
        lowered_set,
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real)
    ) {
        Some(value.to_string())
    } else {
        exact_set_real_value(&lowered_set, value)
    };
    if let Some(real) = exact_real {
        context.numeric_real_values.insert(symbol_id, real);
    }
    if let Some(integer) = exact_set_integer_value(&lowered_set, value) {
        context.numeric_integer_values.insert(symbol_id, integer);
    }
    if let Some(rational) = exact_set_rational_value(&lowered_set, value) {
        context.numeric_rational_values.insert(symbol_id, rational);
    }
    if let Some(numeric) = exact_set_numeric_value(&lowered_set, value) {
        context.numeric_representations.insert(symbol_id, numeric);
    }
    if let Some(equality) = exact_set_numeric_equality(&lowered_set, value) {
        context
            .numeric_representation_equalities
            .insert(symbol_id, equality);
    }
    if let Some(proof) = exact_set_numeric_proof(&lowered_set, value) {
        context
            .numeric_representation_memberships
            .insert(symbol_id, proof);
    }
    Ok(())
}

/// Transport a proof of a concrete predicate (or a conjunction of concrete
/// predicates) when the source theorem and the target call use different
/// exact representatives of the same checked Litex arguments.  The predicate
/// definition is the only transport interface: parameter memberships are
/// rebuilt with `In.own`, and equality clauses are moved across explicit
/// `Same` bridges.  Unsupported clause shapes fail closed.
pub(in super::super) fn render_fact_proof_across_exact_predicate_arguments(
    source: &Fact,
    target: &Fact,
    source_context: &StmtResultToLeanCompilerEnvironmentStack,
    target_context: &StmtResultToLeanCompilerEnvironmentStack,
    source_proof: &str,
) -> Result<String, String> {
    render_fact_proof_across_exact_predicate_arguments_with_source_bridges(
        source,
        target,
        source_context,
        target_context,
        source_proof,
        &[],
    )
}

/// The general exact-predicate transport with explicit semantic edges between
/// the source and target renderings of selected Litex symbols. Set-builder
/// elimination uses this for its verified `Same source representative`
/// certificate; ordinary callers pass no bridges and therefore require the
/// two source renderings to be identical.
pub(in super::super) fn render_fact_proof_across_exact_predicate_arguments_with_source_bridges(
    source: &Fact,
    target: &Fact,
    source_context: &StmtResultToLeanCompilerEnvironmentStack,
    target_context: &StmtResultToLeanCompilerEnvironmentStack,
    source_proof: &str,
    source_bridges: &[(SymbolId, String)],
) -> Result<String, String> {
    if render_fact(source, source_context)? == render_fact(target, target_context)? {
        return Ok(source_proof.to_string());
    }
    if let (Fact::AndFact(source_and), Fact::AndFact(target_and)) = (source, target) {
        if source_and.facts.len() != target_and.facts.len() || source_and.facts.is_empty() {
            return Err("exact predicate conjunction transport changed its arity".into());
        }
        let mut proofs = Vec::with_capacity(source_and.facts.len());
        for (index, (source_component, target_component)) in source_and
            .facts
            .iter()
            .zip(target_and.facts.iter())
            .enumerate()
        {
            let selector = conjunction_selector(index, source_and.facts.len())?;
            proofs.push(
                render_fact_proof_across_exact_predicate_arguments_with_source_bridges(
                    &Fact::from(source_component.clone()),
                    &Fact::from(target_component.clone()),
                    source_context,
                    target_context,
                    &format!("({source_proof}){selector}"),
                    source_bridges,
                )?,
            );
        }
        return Ok(format!("⟨{}⟩", proofs.join(", ")));
    }

    if let (
        Fact::AtomicFact(AtomicFact::EqualFact(source_equality)),
        Fact::AtomicFact(AtomicFact::EqualFact(target_equality)),
    ) = (source, target)
    {
        if obj_equality_key(&source_equality.left) != obj_equality_key(&target_equality.left)
            || obj_equality_key(&source_equality.right) != obj_equality_key(&target_equality.right)
        {
            return Err("exact-parameter equality transport changed its source objects".into());
        }
        let left = render_object_same_across_exact_parameter_contexts(
            &source_equality.left,
            source_context,
            target_context,
            source_bridges,
        )?;
        let right = render_object_same_across_exact_parameter_contexts(
            &source_equality.right,
            source_context,
            target_context,
            source_bridges,
        )?;
        return Ok(format!(
            "Litex.Same.trans (Litex.Same.symm ({left})) (Litex.Same.trans ({source_proof}) ({right}))"
        ));
    }

    if let (Fact::ExistFact(source_existential), Fact::ExistFact(target_existential)) =
        (source, target)
    {
        if source_existential.to_string() != target_existential.to_string() {
            return Err("exact-parameter existential transport changed its source fact".into());
        }
        let changed = source_bridges
            .iter()
            .filter_map(|(symbol_id, bridge)| {
                let source_value = source_context.symbol_names.get(symbol_id)?;
                let target_value = target_context.symbol_names.get(symbol_id)?;
                (source_value != target_value).then(|| {
                    (
                        source_value.as_str(),
                        target_value.as_str(),
                        bridge.as_str(),
                    )
                })
            })
            .collect::<Vec<_>>();
        let [(source_value, target_value, bridge)] = changed.as_slice() else {
            return Err(
                "exact-parameter existential transport requires one changed source parameter"
                    .into(),
            );
        };
        return render_one_witness_existential_across_representative(
            source_existential,
            source_context,
            target_context,
            source_value,
            target_value,
            bridge,
            source_proof,
        );
    }

    if let (
        Fact::AtomicFact(AtomicFact::NotNormalAtomicFact(source_predicate)),
        Fact::AtomicFact(AtomicFact::NotNormalAtomicFact(target_predicate)),
    ) = (source, target)
    {
        let predicate_name = source_predicate.predicate.to_string();
        if target_predicate.predicate.to_string() != predicate_name {
            return Err("abstract predicate negation transport changed its predicate".into());
        }
        let binding = target_context
            .predicate_bindings
            .get(&predicate_name)
            .ok_or_else(|| format!("unavailable abstract predicate `{predicate_name}`"))?;
        if binding.definition.is_none() {
            let equivalence = render_abstract_predicate_same_equivalence(
                &predicate_name,
                &source_predicate.body,
                &target_predicate.body,
                binding,
                source_context,
                target_context,
                source_bridges,
            )?;
            return Ok(format!(
                "(fun __target => ({source_proof}) (({equivalence}).mpr __target))"
            ));
        }
    }

    let (
        Fact::AtomicFact(AtomicFact::NormalAtomicFact(source_predicate)),
        Fact::AtomicFact(AtomicFact::NormalAtomicFact(target_predicate)),
    ) = (source, target)
    else {
        return Err("exact predicate proof transport requires matching concrete predicates".into());
    };
    let predicate_name = source_predicate.predicate.to_string();
    if target_predicate.predicate.to_string() != predicate_name
        || source_predicate.body.len() != target_predicate.body.len()
    {
        return Err("exact predicate proof transport changed its predicate application".into());
    }
    let binding = target_context
        .predicate_bindings
        .get(&predicate_name)
        .ok_or_else(|| format!("unavailable concrete predicate `{predicate_name}`"))?;
    if binding.definition.is_none() {
        let equivalence = render_abstract_predicate_same_equivalence(
            &predicate_name,
            &source_predicate.body,
            &target_predicate.body,
            binding,
            source_context,
            target_context,
            source_bridges,
        )?;
        return Ok(format!("(({equivalence}).mp ({source_proof}))"));
    }
    let definition = binding
        .definition
        .as_ref()
        .expect("abstract predicates returned through their congruence ABI");
    let parameters = definition
        .typed_parameters
        .collect_param_bindings_with_types();
    if parameters.len() != source_predicate.body.len() {
        return Err("exact predicate proof transport changed its parameter arity".into());
    }

    let mut current = source_context.clone();
    let mut final_context = target_context.clone();
    if let Some(well_definedness) = &binding.definition_well_definedness {
        current.well_definedness = Some(well_definedness.clone());
        final_context.well_definedness = Some(well_definedness.clone());
    }
    let mut transports = Vec::new();
    for (index, ((parameter, parameter_type), (source_argument, target_argument))) in parameters
        .iter()
        .zip(
            source_predicate
                .body
                .iter()
                .zip(target_predicate.body.iter()),
        )
        .enumerate()
    {
        let source_value =
            render_concrete_predicate_argument(binding, index, source_argument, source_context)?;
        let target_value =
            render_concrete_predicate_argument(binding, index, target_argument, target_context)?;
        current
            .symbol_names
            .insert(parameter.id(), source_value.clone());
        final_context
            .symbol_names
            .insert(parameter.id(), target_value.clone());
        if !binding.exact_parameters[index] {
            if source_value != target_value {
                let same_source_object = obj_equality_key(source_argument)
                    == obj_equality_key(target_argument)
                    || render_obj(source_argument, source_context)?
                        == render_obj(target_argument, target_context)?;
                if !same_source_object {
                    return Err(format!(
                        "predicate `{predicate_name}` changed non-exact parameter {index}"
                    ));
                }
                // The two terms differ only because nested scopes retained
                // different proofs of the same membership proposition.
                // Lean proof irrelevance makes those `In.rep` observations
                // definitionally interchangeable. Use the target spelling in
                // both compiler models; no mathematical equality transport is
                // being asserted here.
                current
                    .symbol_names
                    .insert(parameter.id(), target_value.clone());
            }
            continue;
        }
        let ParamType::Obj(set) = parameter_type else {
            return Err("exact predicate transport retained a non-object parameter".into());
        };
        install_exact_predicate_carrier_value(parameter.id(), set, &source_value, &mut current)?;
        install_exact_predicate_carrier_value(
            parameter.id(),
            set,
            &target_value,
            &mut final_context,
        )?;
        if source_value == target_value {
            continue;
        }
        let source_original = render_obj(source_argument, source_context)?;
        let target_original = render_obj(target_argument, target_context)?;
        if obj_equality_key(source_argument) != obj_equality_key(target_argument) {
            return Err(format!(
                "predicate `{predicate_name}` exact parameter {index} changed its Litex argument from `{source_original}` (exact `{source_value}`) to `{target_original}` (exact `{target_value}`)"
            ));
        }
        let source_to_original =
            render_exact_predicate_argument_same_to_source(source_argument, set, source_context)?;
        let target_to_original =
            render_exact_predicate_argument_same_to_source(target_argument, set, target_context)?;
        let original_bridge = if source_original == target_original {
            format!("Litex.Same.refl ({source_original})")
        } else if (obj_equality_key(source_argument) == obj_equality_key(target_argument)
            || objs_equal_with_nested_binder_alpha_equivalence(source_argument, target_argument)
            || matches_directly_or_after_one_transparent_definition_pass(
                source_argument,
                target_argument,
                source_context,
            )?
            || matches_directly_or_after_one_transparent_definition_pass(
                source_argument,
                target_argument,
                target_context,
            )?
            || objects_match_under_cross_context_symbol_aliases(
                source_argument,
                target_argument,
                source_context,
                target_context,
            )?)
            && matches!(set, Obj::StandardSet(StandardSet::R))
        {
            render_numeric_obj(source_argument, source_context)?;
            render_real_source_object(target_argument, target_context)?;
            format!(
                "Litex.Same.symm ({})",
                render_real_to_complex_same_across_contexts(
                    target_argument,
                    target_context,
                    source_context,
                )?
            )
        } else {
            let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
                LeanTargetObjectRepresentation::lower(source_argument)?
            else {
                return Err(format!(
                    "predicate `{predicate_name}` exact parameter {index} changed its source rendering without a direct symbol bridge"
                ));
            };
            source_bridges
                .iter()
                .find_map(|(candidate, proof)| (*candidate == symbol_id).then(|| proof.clone()))
                .ok_or_else(|| {
                    format!(
                        "predicate `{predicate_name}` exact parameter {index} changed its source rendering from `{source_original}` to `{target_original}` without verifier-owned Same evidence"
                    )
                })?
        };
        transports.push((
            parameter.id(),
            set.clone(),
            source_value,
            target_value,
            format!(
                "Litex.Same.trans ({source_to_original}) (Litex.Same.trans ({original_bridge}) (Litex.Same.symm ({target_to_original})))"
            ),
        ));
    }

    let component_count = binding.requirement_count + definition.iff_facts.len();
    if component_count == 0 {
        return Err("concrete predicate transport retained no definition components".into());
    }
    let mut component_proofs = Vec::with_capacity(component_count);
    for index in 0..binding.requirement_count {
        let selector = conjunction_selector(index, component_count)?;
        let source_component = instantiated_predicate_components(source, binding, source_context)?;
        let target_component = instantiated_predicate_components(target, binding, target_context)?;
        if source_component[index] == target_component[index] {
            component_proofs.push(format!("__source{selector}"));
            continue;
        }
        let (_, ParamType::Obj(set)) = &parameters[index] else {
            return Err("predicate requirement transport retained a non-object parameter".into());
        };
        let target_value = render_concrete_predicate_argument(
            binding,
            index,
            &target_predicate.body[index],
            target_context,
        )?;
        component_proofs.push(format!(
            "Litex.In.own {} {target_value}",
            render_obj(set, target_context)?
        ));
    }
    for (clause_index, clause) in definition.iff_facts.iter().enumerate() {
        let selector =
            conjunction_selector(binding.requirement_count + clause_index, component_count)?;
        let source_clause = render_fact(clause, &current)?;
        let target_clause = render_fact(clause, &final_context)?;
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = clause else {
            if source_clause == target_clause {
                component_proofs.push(format!("__source{selector}"));
                continue;
            }
            if transports
                .iter()
                .all(|(_, set, _, _, _)| matches!(set, Obj::StandardSet(StandardSet::R)))
            {
                // A checked exact-R argument can be represented either by a
                // compositional native real term or by `In.rep` applied to
                // the verifier-owned membership constructor.  Normalize only
                // those closed constructors here.  Lean must prove the whole
                // clause conversion (including forall/implication nesting);
                // no `Same ℝ ℝ -> Eq` principle is introduced.
                let conversion = if matches!(clause, Fact::ForallFact(_)) {
                    format!(
                        "(by convert (@__source{selector}) using 1 <;> simp [Litex.In.rep, Litex.Rules.complexRealInR, Litex.Rules.complexAddInR, Litex.Rules.complexSubInR, Litex.Rules.complexMulInR, Litex.Rules.complexDivInR, Litex.Rules.inROfInRPos, Litex.Le, Litex.Lt, Litex.OrderValue])"
                    )
                } else {
                    format!(
                        "(by simpa [Litex.In.rep, Litex.Rules.complexRealInR, Litex.Rules.complexAddInR, Litex.Rules.complexSubInR, Litex.Rules.complexMulInR, Litex.Rules.complexDivInR, Litex.Rules.inROfInRPos, Litex.Le, Litex.Lt, Litex.OrderValue] using (__source{selector}))"
                    )
                };
                component_proofs.push(conversion);
                continue;
            }
            return Err(format!(
                "exact predicate transport does not yet support definition clause `{source_clause}` changing to `{target_clause}`",
            ));
        };
        let mut proof = format!("__source{selector}");
        let mut clause_context = current.clone();
        for (symbol_id, set, source_value, target_value, bridge) in &transports {
            let mut next = clause_context.clone();
            next.symbol_names.insert(*symbol_id, target_value.clone());
            install_exact_predicate_carrier_value(*symbol_id, set, target_value, &mut next)?;
            proof = render_equality_across_representative(
                equality,
                &clause_context,
                &next,
                source_value,
                target_value,
                bridge,
                &proof,
            )?;
            clause_context = next;
        }
        if render_fact(clause, &clause_context)? != render_fact(clause, &final_context)? {
            return Err(format!(
                "predicate `{predicate_name}` clause {clause_index} did not reach its target representation"
            ));
        }
        component_proofs.push(proof);
    }
    Ok(format!(
        "(by\n  have __source := {source_proof}\n  unfold {} at __source ⊢\n  exact ⟨{}⟩)",
        binding.lean_name,
        component_proofs.join(", ")
    ))
}

/// Whether `source` and `target` are made entirely from applications of
/// concrete predicates whose definitions are available in `context`.
///
/// Known-forall replay uses this guard before invoking the representation
/// transport above.  Ordinary relations such as equality may also be encoded
/// as `NormalAtomicFact`; they must keep the normal theorem-application path
/// instead of being mistaken for user-defined predicates.
pub(in super::super) fn facts_require_exact_predicate_argument_transport(
    source: &Fact,
    target: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> bool {
    match (source, target) {
        (Fact::AndFact(source_and), Fact::AndFact(target_and)) => {
            source_and.facts.len() == target_and.facts.len()
                && !source_and.facts.is_empty()
                && source_and.facts.iter().zip(target_and.facts.iter()).all(
                    |(source_component, target_component)| {
                        facts_require_exact_predicate_argument_transport(
                            &Fact::from(source_component.clone()),
                            &Fact::from(target_component.clone()),
                            context,
                        )
                    },
                )
        }
        (
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(source_predicate)),
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(target_predicate)),
        ) => {
            let predicate_name = source_predicate.predicate.to_string();
            predicate_name == target_predicate.predicate.to_string()
                && context
                    .predicate_bindings
                    .get(&predicate_name)
                    .and_then(|binding| binding.definition.as_ref())
                    .is_some()
        }
        _ => false,
    }
}

pub(in super::super) fn facts_require_abstract_predicate_argument_transport(
    source: &Fact,
    target: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> bool {
    match (source, target) {
        (Fact::AndFact(source_and), Fact::AndFact(target_and)) => {
            source_and.facts.len() == target_and.facts.len()
                && !source_and.facts.is_empty()
                && source_and.facts.iter().zip(target_and.facts.iter()).all(
                    |(source_component, target_component)| {
                        facts_require_abstract_predicate_argument_transport(
                            &Fact::from(source_component.clone()),
                            &Fact::from(target_component.clone()),
                            context,
                        )
                    },
                )
        }
        (
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(source_predicate)),
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(target_predicate)),
        ) => {
            let predicate_name = source_predicate.predicate.to_string();
            predicate_name == target_predicate.predicate.to_string()
                && context
                    .predicate_bindings
                    .get(&predicate_name)
                    .is_some_and(|binding| {
                        binding.definition.is_none() && binding.same_congruence_name.is_some()
                    })
        }
        (
            Fact::AtomicFact(AtomicFact::NotNormalAtomicFact(source_predicate)),
            Fact::AtomicFact(AtomicFact::NotNormalAtomicFact(target_predicate)),
        ) => {
            let predicate_name = source_predicate.predicate.to_string();
            predicate_name == target_predicate.predicate.to_string()
                && context
                    .predicate_bindings
                    .get(&predicate_name)
                    .is_some_and(|binding| {
                        binding.definition.is_none() && binding.same_congruence_name.is_some()
                    })
        }
        _ => false,
    }
}
