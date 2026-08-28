//! Set-builder membership and predicate projection proofs.

use super::super::*;

pub(in super::super) fn conjunction_selector(index: usize, count: usize) -> Result<String, String> {
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

pub(in super::super) fn render_set_builder_membership_from_fact_and_proofs(
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
    let exact_source_element = render_exact_predicate_argument(element, base_set, context)
        .unwrap_or_else(|_| rendered_element.clone());
    let mut nested = context.clone();
    nested
        .symbol_names
        .insert(builder.symbol_id, representative.clone());
    nested
        .exact_carrier_values
        .insert(builder.symbol_id, representative.clone());
    nested
        .semantic_zero_ended_order_symbols
        .insert(builder.symbol_id);

    let mut predicate_proofs = Vec::with_capacity(builder.facts.len());
    let mut source = context.clone();
    source
        .symbol_names
        .insert(builder.symbol_id, rendered_element.clone());
    source
        .exact_carrier_values
        .insert(builder.symbol_id, exact_source_element.clone());
    source
        .semantic_zero_ended_order_symbols
        .insert(builder.symbol_id);
    let representative_same = format!("Litex.In.same_rep {rendered_element} ({base_proof})");
    for (index, fact) in builder.facts.iter().enumerate() {
        let premise = &premises[index + 1];
        let expected_premise = render_fact(fact, &source)?;
        let retained_premise = render_fact(&premise.0, context)?;
        if expected_premise != retained_premise {
            return Err(format!(
                "set-builder predicate premise changed its checked binder substitution from `{expected_premise}` to `{retained_premise}`"
            ));
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
            Fact::AtomicFact(
                AtomicFact::LessFact(_)
                | AtomicFact::GreaterFact(_)
                | AtomicFact::LessEqualFact(_)
                | AtomicFact::GreaterEqualFact(_),
            ) => render_zero_ended_order_across_representative(
                fact,
                &source,
                &nested,
                &rendered_element,
                &representative,
                &representative_same,
                &source_proof,
            )?,
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
                let expected_source_argument = if binding.exact_parameters[0] {
                    &exact_source_element
                } else {
                    &rendered_element
                };
                let argument_source = if binding.exact_parameters[0] {
                    render_exact_predicate_argument(&predicate.body[0], base_set, &source)?
                } else {
                    render_obj(&predicate.body[0], &source)?
                };
                let argument_target = render_obj(&predicate.body[0], &nested)?;
                if argument_source != *expected_source_argument || argument_target != representative
                {
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
                let (predicate_source_value, predicate_source_same_representative) = if binding
                    .exact_parameters[0]
                {
                    let exact_source_same_external =
                        render_exact_predicate_argument_same_to_source(element, base_set, context)?;
                    (
                            exact_source_element.clone(),
                            format!(
                                "Litex.Same.trans ({exact_source_same_external}) ({representative_same})"
                            ),
                        )
                } else {
                    (rendered_element.clone(), representative_same.clone())
                };
                let mut component_proofs = vec![format!(
                    "(Litex.In.congr ({predicate_source_same_representative}) {rendered_set}).mp (__source{membership_selector})"
                )];
                let mut clause_source = context.clone();
                clause_source
                    .symbol_names
                    .insert(definition_parameter.id(), predicate_source_value.clone());
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
                        &predicate_source_value,
                        &representative,
                        &predicate_source_same_representative,
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

pub(in super::super) fn render_set_builder_predicate_projection_from_fact_and_proof(
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
    let Obj::SetBuilder(source_builder) = source_set else {
        return Err("set-builder predicate projection lost its source builder".into());
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
        representative_context
            .semantic_zero_ended_order_symbols
            .insert(builder.symbol_id);
        let mut element_context = context.clone();
        element_context
            .symbol_names
            .insert(builder.symbol_id, rendered_element.clone());
        element_context
            .semantic_zero_ended_order_symbols
            .insert(builder.symbol_id);
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
    if matches!(
        clause,
        Fact::AtomicFact(
            AtomicFact::LessFact(_)
                | AtomicFact::GreaterFact(_)
                | AtomicFact::LessEqualFact(_)
                | AtomicFact::GreaterEqualFact(_)
        )
    ) {
        let mut representative_context = context.clone();
        representative_context
            .symbol_names
            .insert(builder.symbol_id, "__rep".into());
        representative_context
            .semantic_zero_ended_order_symbols
            .insert(builder.symbol_id);
        let mut element_context = context.clone();
        element_context
            .symbol_names
            .insert(builder.symbol_id, rendered_element.clone());
        element_context
            .semantic_zero_ended_order_symbols
            .insert(builder.symbol_id);
        let expected_clause = render_fact(clause, &element_context)?;
        let retained_clause = render_fact(target, context)?;
        if expected_clause != retained_clause {
            return Err(format!(
                "set-builder order projection changed its instantiated clause from `{expected_clause}` to `{retained_clause}`"
            ));
        }
        let transported = render_zero_ended_order_across_representative(
            clause,
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
    let (predicate_target_value, representative_same_predicate_target) =
        if binding.exact_parameters[0] {
            let predicate_target_value = render_exact_predicate_argument(
                &target_predicate.body[0],
                &source_builder.param_set,
                context,
            )?;
            let predicate_target_same_external = render_exact_predicate_argument_same_to_source(
                &target_predicate.body[0],
                &source_builder.param_set,
                context,
            )?;
            let predicate_target_same_representative =
                format!("Litex.Same.trans ({predicate_target_same_external}) (__same)");
            (
                predicate_target_value,
                format!("Litex.Same.symm ({predicate_target_same_representative})"),
            )
        } else {
            (rendered_element.clone(), "Litex.Same.symm __same".into())
        };
    let mut component_proofs = vec![format!(
        "(Litex.In.congr (Litex.Same.symm ({representative_same_predicate_target})) {rendered_set}).mpr (__selected{membership_selector})"
    )];
    let mut representative_context = context.clone();
    representative_context
        .symbol_names
        .insert(definition_parameter.id(), "__rep".into());
    let mut element_context = context.clone();
    element_context
        .symbol_names
        .insert(definition_parameter.id(), predicate_target_value.clone());
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
            &predicate_target_value,
            &representative_same_predicate_target,
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
