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
    if let Some((exact_value, exact_base_same_source)) =
        render_exact_set_builder_value_from_fact_and_proofs(target, premises, context)?
    {
        return Ok(format!(
            "⟨{exact_value}, Litex.Same.trans (Litex.Same.symm ({exact_base_same_source})) (Litex.Same.symm (Litex.Same.subtype {exact_value}))⟩"
        ));
    }
    let base_proof = premises[0].1.clone();
    let rendered_element = render_obj(element, context)?;
    let representative = format!("Litex.In.rep {rendered_element} ({base_proof})");
    let exact_source_element = render_exact_predicate_argument(element, base_set, context)
        .unwrap_or_else(|_| rendered_element.clone());
    let lowered_base_set = LeanTargetObjectRepresentation::lower(base_set)?;
    if exact_set_real_value(&lowered_base_set, &exact_source_element).is_some()
        && matches!(
            LeanTargetObjectRepresentation::lower(element)?,
            LeanTargetObjectRepresentation::Number { .. }
                | LeanTargetObjectRepresentation::Constant(_)
        )
        && builder.facts.iter().all(|fact| {
            matches!(
                fact,
                Fact::AtomicFact(
                    AtomicFact::LessFact(_)
                        | AtomicFact::GreaterFact(_)
                        | AtomicFact::LessEqualFact(_)
                        | AtomicFact::GreaterEqualFact(_)
                )
            )
        })
    {
        let mut exact_context = context.clone();
        exact_context
            .symbol_names
            .insert(builder.symbol_id, exact_source_element.clone());
        install_exact_set_builder_parameter_representation(
            builder.symbol_id,
            builder.set.as_ref(),
            &exact_source_element,
            &mut exact_context,
        );
        let mut predicate_proofs = Vec::with_capacity(builder.facts.len());
        for (index, fact) in builder.facts.iter().enumerate() {
            if !fact_matches_structured_induction_goal_substitution(
                fact,
                &premises[index + 1].0,
                builder.symbol_id,
                element,
            ) {
                return Err(
                    "set-builder closed-real predicate changed its checked substitution".into(),
                );
            }
            let proposition = render_fact(fact, &exact_context)?;
            predicate_proofs.push(format!(
                "(show {proposition} by norm_num [Litex.Le, Litex.Lt, Litex.OrderValue])"
            ));
        }
        let exact_same_source =
            render_exact_predicate_argument_same_to_source(element, base_set, context)?;
        return Ok(format!(
            "Litex.Rules.inSetBuilder (Litex.Same.symm ({exact_same_source})) ({})",
            conjunction(&predicate_proofs)
        ));
    }
    let mut nested = context.clone();
    nested
        .symbol_names
        .insert(builder.symbol_id, representative.clone());
    install_exact_set_builder_parameter_representation(
        builder.symbol_id,
        builder.set.as_ref(),
        &representative,
        &mut nested,
    );

    let mut predicate_proofs = Vec::with_capacity(builder.facts.len());
    let mut source = context.clone();
    source
        .symbol_names
        .insert(builder.symbol_id, rendered_element.clone());
    install_exact_set_builder_parameter_representation(
        builder.symbol_id,
        builder.set.as_ref(),
        &exact_source_element,
        &mut source,
    );
    let representative_same = format!("Litex.In.same_rep {rendered_element} ({base_proof})");
    for (index, fact) in builder.facts.iter().enumerate() {
        let premise = &premises[index + 1];
        if !fact_matches_structured_induction_goal_substitution(
            fact,
            &premise.0,
            builder.symbol_id,
            element,
        ) {
            return Err(
                "set-builder predicate premise is not the checked binder substitution".into(),
            );
        }
        let expected_premise = render_fact(fact, &source)?;
        let retained_premise = render_fact(&premise.0, context)?;
        let source_proof = if expected_premise == retained_premise {
            premise.1.clone()
        } else if let Some(role_preserving) =
            render_role_preserving_zero_substitution(fact, element, builder.symbol_id)?
        {
            role_preserving
        } else {
            return Err(format!(
                "set-builder predicate premise changed its checked binder substitution from `{expected_premise}` to `{retained_premise}`"
            ));
        };
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

/// Construct the canonical exact carrier value certified by one checked
/// set-builder membership Result.  Unlike `In.rep`, this value retains the
/// verifier-selected base representation definitionally, so a real-valued
/// set member observes the same native real expression that the source wrote.
pub(in super::super) fn render_exact_set_builder_value_from_fact_and_proofs(
    target: &Fact,
    premises: &[(Fact, String)],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<Option<(String, String)>, String> {
    let (element, target_set) = membership_parts(target)?;
    let Obj::SetBuilder(source_builder) = target_set else {
        return Ok(None);
    };
    let lowered = LeanTargetObjectRepresentation::lower(target_set)?;
    let LeanTargetObjectRepresentation::SetBuilder(builder) = lowered else {
        return Err("set-builder membership lowered to another target set".into());
    };
    if premises.len() != builder.facts.len() + 1 {
        return Err("set-builder membership lost its base or predicate premises".into());
    }
    let (base_element, base_set) = membership_parts(&premises[0].0)?;
    if obj_equality_key(element) != obj_equality_key(base_element)
        || obj_equality_key(base_set) != obj_equality_key(source_builder.param_set.as_ref())
        || LeanTargetObjectRepresentation::lower(base_set)? != *builder.set
    {
        return Err("set-builder membership changed its base-membership premise".into());
    }

    let exact_base = match render_exact_predicate_argument(element, base_set, context) {
        Ok(value) => value,
        Err(_) => return Ok(None),
    };
    let exact_base_same_source =
        match render_exact_predicate_argument_same_to_source(element, base_set, context) {
            Ok(proof) => proof,
            Err(_) => return Ok(None),
        };
    let mut exact_context = context.clone();
    exact_context
        .symbol_names
        .insert(builder.symbol_id, exact_base.clone());
    install_exact_set_builder_parameter_representation(
        builder.symbol_id,
        builder.set.as_ref(),
        &exact_base,
        &mut exact_context,
    );

    let mut predicate_proofs = Vec::with_capacity(builder.facts.len());
    for (index, fact) in builder.facts.iter().enumerate() {
        let premise = &premises[index + 1];
        if !fact_matches_structured_induction_goal_substitution(
            fact,
            &premise.0,
            builder.symbol_id,
            element,
        ) {
            return Err(
                "set-builder canonical value changed its checked predicate substitution".into(),
            );
        }
        let exact_proposition = render_fact(fact, &exact_context)?;
        let retained_proposition = render_fact(&premise.0, context)?;
        predicate_proofs.push(if exact_proposition == retained_proposition {
            premise.1.clone()
        } else if matches!(
            fact,
            Fact::AtomicFact(
                AtomicFact::LessFact(_)
                    | AtomicFact::GreaterFact(_)
                    | AtomicFact::LessEqualFact(_)
                    | AtomicFact::GreaterEqualFact(_)
            )
        ) && matches!(
            LeanTargetObjectRepresentation::lower(element)?,
            LeanTargetObjectRepresentation::Number { .. }
                | LeanTargetObjectRepresentation::Constant(_)
        ) {
            format!("(show {exact_proposition} by norm_num [Litex.Le, Litex.Lt, Litex.OrderValue])")
        } else {
            // The verifier has already checked the structural binder
            // substitution above.  Exact numeric carriers may only differ
            // here by Lean's canonical casts (for example `(0 : ℂ)` versus
            // `((0 : ℝ) : ℂ)`), which `simpa` must discharge in the kernel.
            format!("(by simpa using ({}))", premise.1)
        });
    }
    let predicate_proof = conjunction(&predicate_proofs);
    let exact_value = format!("⟨{exact_base}, {predicate_proof}⟩");
    Ok(Some((exact_value, exact_base_same_source)))
}

/// Substituting the literal `0` for the binder in `x ≤ 0` or `0 ≤ x`
/// produces the same closed source fact `0 ≤ 0`, but the set-builder ABI
/// must retain which side belonged to the binder: `Nonpositive` and
/// `Nonnegative` are different semantic propositions.  The structural
/// substitution check above already certifies the source Result.  This fixed
/// adapter merely replays reflexivity in the original binder role.
fn render_role_preserving_zero_substitution(
    source_fact: &Fact,
    replacement: &Obj,
    binder_symbol_id: SymbolId,
) -> Result<Option<String>, String> {
    if !is_literal_zero(replacement) {
        return Ok(None);
    }
    let (left, right, strict) = order_relation_parts(source_fact)?;
    if strict {
        return Ok(None);
    }
    let predicate = if object_is_symbol(left, binder_symbol_id) && is_literal_zero(right) {
        "Nonpositive"
    } else if is_literal_zero(left) && object_is_symbol(right, binder_symbol_id) {
        "Nonnegative"
    } else {
        return Ok(None);
    };
    Ok(Some(format!(
        "Litex.{predicate}.intro (Litex.AsReal.complex (0 : ℝ)) (show (0 : ℝ) ≤ 0 by norm_num)"
    )))
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
    if let Ok(LeanTargetObjectRepresentation::Symbol { symbol_id, .. }) =
        LeanTargetObjectRepresentation::lower(element)
    {
        if let Some(exact_carrier) = context.exact_carrier_values.get(&symbol_id) {
            let base_value = format!("({exact_carrier}).val");
            let mut exact_context = context.clone();
            exact_context
                .symbol_names
                .insert(builder.symbol_id, base_value.clone());
            install_exact_set_builder_parameter_representation(
                builder.symbol_id,
                builder.set.as_ref(),
                &base_value,
                &mut exact_context,
            );
            if render_fact(clause, &exact_context)? == render_fact(target, context)? {
                return Ok(format!("(({exact_carrier}).property{predicate_selector})"));
            }
            let rendered_source_set = render_obj(source_set, context)?;
            let selected_membership =
                cached_exact_membership_selection_proof(exact_carrier, &rendered_element).map(
                    |proof| proof.trim_matches(|character| character == '(' || character == ')'),
                );
            let exact_carrier_is_owned_by_source_set = selected_membership.is_some_and(|proof| {
                context.fact_propositions.iter().any(|(fact_id, fact)| {
                    let Ok((declared_element, declared_set)) = membership_parts(fact) else {
                        return false;
                    };
                    context
                        .fact_names
                        .get(fact_id)
                        .is_some_and(|name| name == proof)
                        && render_obj(declared_element, context)
                            .is_ok_and(|value| value == rendered_element)
                        && (render_obj(declared_set, context)
                            .is_ok_and(|value| value == rendered_source_set)
                            || matches_directly_or_after_one_transparent_definition_pass(
                                declared_set,
                                source_set,
                                context,
                            )
                            .unwrap_or(false)
                            || matches_directly_or_after_one_transparent_definition_pass(
                                source_set,
                                declared_set,
                                context,
                            )
                            .unwrap_or(false))
                })
            });
            if exact_carrier_is_owned_by_source_set
                && fact_matches_structured_induction_goal_substitution(
                    clause,
                    target,
                    builder.symbol_id,
                    element,
                )
            {
                return Ok(format!(
                    "(by simpa using (({exact_carrier}).property{predicate_selector}))"
                ));
            }
        }
    }
    if let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = clause {
        let mut representative_context = context.clone();
        representative_context
            .symbol_names
            .insert(builder.symbol_id, "__rep".into());
        representative_context
            .exact_carrier_values
            .insert(builder.symbol_id, "__rep".into());
        representative_context
            .semantic_zero_ended_order_symbols
            .insert(builder.symbol_id);
        let mut element_context = context.clone();
        element_context
            .symbol_names
            .insert(builder.symbol_id, rendered_element.clone());
        element_context
            .exact_carrier_values
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
            .exact_carrier_values
            .insert(builder.symbol_id, "__rep".into());
        representative_context
            .semantic_zero_ended_order_symbols
            .insert(builder.symbol_id);
        let mut element_context = context.clone();
        element_context
            .symbol_names
            .insert(builder.symbol_id, rendered_element.clone());
        element_context
            .exact_carrier_values
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
        let exact_carrier = LeanTargetObjectRepresentation::lower(element)
            .ok()
            .and_then(|lowered| match lowered {
                LeanTargetObjectRepresentation::Symbol { symbol_id, .. } => {
                    context.exact_carrier_values.get(&symbol_id).cloned()
                }
                _ => None,
            });
        return Err(format!(
            "set-builder concrete predicate projection changed its application (clause `{}`, target `{}`, element `{element}`, exact carrier {exact_carrier:?})",
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(predicate.clone())),
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(target_predicate.clone())),
        ));
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
