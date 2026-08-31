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
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(_)) => {
                render_fact_proof_across_exact_predicate_arguments(
                    fact,
                    fact,
                    &source,
                    &nested,
                    &source_proof,
                )?
            }
            _ => {
                return Err(
                    "compiler set-builder membership currently transports equality, order, or concrete predicate clauses"
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
    if !fact_matches_structured_induction_goal_substitution(
        clause,
        target,
        builder.symbol_id,
        element,
    ) {
        return Err(format!(
            "set-builder predicate projection changed its verified binder substitution (clause `{clause}`, target `{target}`, element `{element}`)"
        ));
    }
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
        || predicate.body.len() != target_predicate.body.len()
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
    if binding.parameter_count != predicate.body.len() {
        return Err("set-builder concrete predicate changed its parameter arity".into());
    }
    binding.definition.as_ref().ok_or_else(|| {
        "abstract set-builder predicates have no projection definition".to_string()
    })?;

    // The structural check above replays the verifier-owned binder
    // substitution on the Litex AST. Re-render the same retained predicate
    // under both carrier environments and transport every exact argument
    // uniformly, including captured parameters such as `P(a, x)`.
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
    install_exact_predicate_carrier_value(
        builder.symbol_id,
        &source_builder.param_set,
        "__rep",
        &mut representative_context,
    )?;
    let mut element_context = context.clone();
    element_context
        .symbol_names
        .insert(builder.symbol_id, rendered_element.clone());
    element_context
        .semantic_zero_ended_order_symbols
        .insert(builder.symbol_id);
    let exact_element =
        render_exact_predicate_argument(element, &source_builder.param_set, context)?;
    let exact_element_to_source = render_exact_predicate_argument_same_to_source(
        element,
        &source_builder.param_set,
        context,
    )?;
    install_exact_predicate_carrier_value(
        builder.symbol_id,
        &source_builder.param_set,
        &exact_element,
        &mut element_context,
    )?;
    element_context.exact_carrier_source_equalities.insert(
        builder.symbol_id,
        ExactCarrierSourceEqualityBinding::new(exact_element, exact_element_to_source),
    );
    let expected_target = render_fact(clause, &element_context)?;
    let retained_target = render_fact(target, context)?;
    let transported = render_fact_proof_across_exact_predicate_arguments_with_source_bridges(
        clause,
        clause,
        &representative_context,
        &element_context,
        "__selected",
        &[(builder.symbol_id, "Litex.Same.symm __same".to_string())],
    )?;
    Ok(format!(
        "(show {retained_target} from (by\n  rcases Litex.Rules.inSetBuilder_iff.mp ({source_proof}) with ⟨__rep, __predicate, __same⟩\n  have __selected := __predicate{predicate_selector}\n  have __transported : {expected_target} := {transported}\n  simpa [Litex.In.rep, Litex.Rules.complexRealInR, Litex.Rules.complexAddInR, Litex.Rules.complexSubInR, Litex.Rules.complexMulInR, Litex.Rules.complexDivInR, Litex.Rules.inROfInRPos] using __transported))"
    ))
}
