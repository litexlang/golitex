//! Exact predicate instantiation and argument transport.

use super::super::*;

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
    if let Some(real) = exact_set_real_value(&lowered_set, value) {
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
            proofs.push(render_fact_proof_across_exact_predicate_arguments(
                &Fact::from(source_component.clone()),
                &Fact::from(target_component.clone()),
                source_context,
                target_context,
                &format!("({source_proof}){selector}"),
            )?);
        }
        return Ok(format!("⟨{}⟩", proofs.join(", ")));
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
    let definition = binding
        .definition
        .as_ref()
        .ok_or_else(|| "abstract predicates have no representation transport".to_string())?;
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
                return Err(format!(
                    "predicate `{predicate_name}` changed non-exact parameter {index}"
                ));
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
                "predicate `{predicate_name}` exact parameter {index} changed its Litex argument from `{source_original}` to `{target_original}`"
            ));
        }
        let source_to_original =
            render_exact_predicate_argument_same_to_source(source_argument, set, source_context)?;
        let target_to_original =
            render_exact_predicate_argument_same_to_source(target_argument, set, target_context)?;
        transports.push((
            parameter.id(),
            set.clone(),
            source_value,
            target_value,
            format!(
                "Litex.Same.trans ({source_to_original}) (Litex.Same.symm ({target_to_original}))"
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
                component_proofs.push(format!(
                    "(by simpa [Litex.In.rep, Litex.Rules.complexRealInR, Litex.Rules.complexAddInR, Litex.Rules.complexSubInR, Litex.Rules.complexMulInR, Litex.Rules.complexDivInR, Litex.Rules.inROfInRPos, Litex.Le, Litex.Lt, Litex.OrderValue] using (__source{selector}))"
                ));
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
