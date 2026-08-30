//! Exact and concrete predicate argument rendering.

use super::super::*;

pub(in super::super) fn object_is_symbol(object: &Obj, symbol_id: SymbolId) -> bool {
    matches!(object, Obj::Atom(atom) if atom.symbol_ref().is_some_and(|symbol| symbol.id() == symbol_id))
}

fn cached_exact_membership_selection_proof<'a>(exact: &'a str, source: &str) -> Option<&'a str> {
    // `exact_carrier_values` is populated only from compiler-rendered checked
    // membership selections.  Preserve the proof carried by that cached term
    // when an instantiated body alpha-refreshes the source SymbolId.
    let prefix = format!("(Litex.In.rep {source} ");
    exact
        .strip_prefix(&prefix)
        .and_then(|remainder| remainder.strip_suffix(')'))
        .filter(|proof| !proof.is_empty())
}

fn resolve_exact_predicate_function_binding<'a>(
    object: &Obj,
    context: &'a StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(&'a FunctionBinding, String), String> {
    let LeanTargetObjectRepresentation::Symbol { symbol_id, name } =
        LeanTargetObjectRepresentation::lower(object)?
    else {
        return Err(format!(
            "exact predicate function argument `{object}` is not a named function"
        ));
    };
    let mut candidates = context
        .function_bindings
        .values()
        .filter(|binding| binding.symbol_id == symbol_id)
        .collect::<Vec<_>>();
    candidates.sort_by(|left, right| left.membership_proof_name.cmp(&right.membership_proof_name));
    let Some(first) = candidates.first().copied() else {
        return Err(format!(
            "predicate function argument `{name}` has no visible checked function membership"
        ));
    };
    if candidates
        .iter()
        .any(|candidate| candidate.function != first.function || candidate.direct != first.direct)
    {
        return Err(format!(
            "predicate function argument `{name}` has evidence-distinct visible function contracts"
        ));
    }
    Ok((first, render_obj(object, context)?))
}

pub(in super::super) fn render_exact_predicate_function_argument(
    object: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match LeanTargetObjectRepresentation::lower(object)? {
        LeanTargetObjectRepresentation::AnonymousFunction(_) => render_obj(object, context),
        LeanTargetObjectRepresentation::Symbol { .. } => {
            let (first, source) = resolve_exact_predicate_function_binding(object, context)?;
            Ok(if first.direct {
                source
            } else {
                format!("(Litex.In.rep {source} ({}))", first.membership_proof_name)
            })
        }
        _ => Err(format!(
            "exact predicate function argument `{object}` is neither a named nor anonymous function"
        )),
    }
}

fn resolve_visible_exact_membership_proof(
    object: &Obj,
    set: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let mut candidates = context
        .fact_propositions
        .iter()
        .filter_map(|(fact_id, fact)| {
            let (element, retained_set) = membership_parts(fact).ok()?;
            (obj_equality_key(element) == obj_equality_key(object)
                && obj_equality_key(retained_set) == obj_equality_key(set))
            .then_some((*fact_id, fact))
        })
        .collect::<Vec<_>>();
    candidates.sort_by_key(|(fact_id, _)| *fact_id);
    for (fact_id, fact) in candidates {
        if let Ok(proof) = resolve_fact_citation(&fact_id, fact, context) {
            return Ok(proof);
        }
    }
    // Instantiating a retained forall/existential body can alpha-refresh its
    // SymbolId while keeping the same Lean binder.  In that case the exact
    // representative and its membership proof are still in the same lexical
    // frame, so compare their already-rendered terms before failing closed.
    let rendered_object = render_obj(object, context)?;
    let rendered_set = render_obj(set, context)?;
    let mut rendered_candidates = context
        .fact_propositions
        .iter()
        .filter_map(|(fact_id, fact)| {
            let (element, retained_set) = membership_parts(fact).ok()?;
            (render_obj(element, context).ok().as_deref() == Some(rendered_object.as_str())
                && render_obj(retained_set, context).ok().as_deref() == Some(rendered_set.as_str()))
            .then_some((*fact_id, fact))
        })
        .collect::<Vec<_>>();
    rendered_candidates.sort_by_key(|(fact_id, _)| *fact_id);
    for (fact_id, fact) in rendered_candidates {
        if let Ok(proof) = resolve_fact_citation(&fact_id, fact, context) {
            return Ok(proof);
        }
    }
    Err(format!(
        "exact predicate argument `{object}` has no visible checked membership in `{set}`"
    ))
}

pub(in super::super) fn render_exact_predicate_argument(
    object: &Obj,
    set: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let Ok(LeanTargetObjectRepresentation::Symbol { symbol_id, name }) =
        LeanTargetObjectRepresentation::lower(object)
    {
        if let Some(value) = context.exact_carrier_values.get(&symbol_id) {
            return Ok(value.clone());
        }
        // Cloning/instantiating an existential fact may alpha-refresh the
        // body's SymbolId while preserving its binder name.  The existential
        // renderer records that lexical name together with the dependent
        // membership binder, so recover the same exact representative here
        // instead of searching ambient facts by proposition.
        if let Some(witness_name) = context.existential_names.get(&name) {
            if matches!(set, Obj::StandardSet(StandardSet::C)) {
                return Ok(witness_name.clone());
            }
            return Ok(format!(
                "(Litex.In.rep {witness_name} __type_{witness_name})"
            ));
        }
    }
    if matches!(set, Obj::FnSet(_) | Obj::FiniteSeqSet(_) | Obj::SeqSet(_)) {
        return render_exact_predicate_function_argument(object, context);
    }
    let representative = || -> Result<String, String> {
        let source = render_obj(object, context)?;
        let proof = resolve_visible_exact_membership_proof(object, set, context)?;
        Ok(format!("(Litex.In.rep {source} ({proof}))"))
    };
    match set {
        Obj::StandardSet(StandardSet::R) => LeanTargetObjectRepresentation::lower(object)
            .and_then(|lowered| render_real_target_object_representation(&lowered, context))
            .or_else(|_| representative()),
        Obj::StandardSet(StandardSet::C) => render_numeric_obj(object, context),
        Obj::StandardSet(StandardSet::Z) => {
            render_integer_obj(object, context).or_else(|_| representative())
        }
        Obj::StandardSet(StandardSet::Q) => {
            render_rational_obj(object, context).or_else(|_| representative())
        }
        _ => representative(),
    }
}

/// Prove that the exact carrier passed to a concrete predicate is semantically
/// the original Litex argument. The bridge is determined entirely by the same
/// checked membership representation used to render the call; it does not
/// search for a replacement mathematical proof.
pub(in super::super) fn render_exact_predicate_argument_same_to_source(
    object: &Obj,
    set: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let exact = render_exact_predicate_argument(object, set, context)?;
    let source = render_obj(object, context)?;
    if exact == source {
        return Ok(format!("Litex.Same.refl ({exact})"));
    }
    if let Some(membership) = cached_exact_membership_selection_proof(&exact, &source) {
        return Ok(format!(
            "Litex.Same.symm (Litex.In.same_rep {source} {membership})"
        ));
    }
    if let LeanTargetObjectRepresentation::Symbol { name, .. } =
        LeanTargetObjectRepresentation::lower(object)?
    {
        if let Some(witness_name) = context.existential_names.get(&name) {
            let membership = format!("__type_{witness_name}");
            let selected = if matches!(set, Obj::StandardSet(StandardSet::C)) {
                witness_name.clone()
            } else {
                format!("(Litex.In.rep {witness_name} {membership})")
            };
            if source == *witness_name && exact == selected {
                return Ok(format!(
                    "Litex.Same.symm (Litex.In.same_rep {witness_name} {membership})"
                ));
            }
        }
    }
    if matches!(set, Obj::FnSet(_) | Obj::FiniteSeqSet(_) | Obj::SeqSet(_))
        && matches!(
            LeanTargetObjectRepresentation::lower(object)?,
            LeanTargetObjectRepresentation::Symbol { .. }
        )
    {
        let (binding, function_source) = resolve_exact_predicate_function_binding(object, context)?;
        if !binding.direct {
            let selected = format!(
                "(Litex.In.rep {function_source} ({}))",
                binding.membership_proof_name
            );
            if exact == selected {
                return Ok(format!(
                    "Litex.Same.symm (Litex.In.same_rep {function_source} ({}))",
                    binding.membership_proof_name
                ));
            }
        }
    }
    if matches!(
        LeanTargetObjectRepresentation::lower(object)?,
        LeanTargetObjectRepresentation::Symbol { .. }
    ) {
        if let Ok(membership) = resolve_visible_exact_membership_proof(object, set, context) {
            let selected = if matches!(set, Obj::StandardSet(StandardSet::C)) {
                vec![source.clone()]
            } else {
                vec![
                    format!("(Litex.In.rep {source} {membership})"),
                    format!("(Litex.In.rep {source} ({membership}))"),
                ]
            };
            if selected.iter().any(|candidate| exact == *candidate) {
                return Ok(format!(
                    "Litex.Same.symm (Litex.In.same_rep {source} ({membership}))"
                ));
            }
        }
    }

    let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
    let exact_to_numeric = exact_set_numeric_equality(&lowered_set, &exact).ok_or_else(|| {
        format!(
            "exact predicate argument `{object}` has no equality bridge for `{set}` (exact Lean value `{exact}`, source Lean value `{source}`)"
        )
    })?;
    let numeric = exact_set_numeric_value(&lowered_set, &exact).ok_or_else(|| {
        format!("exact predicate argument `{object}` has no numeric observation for `{set}`")
    })?;
    if source == numeric {
        return Ok(exact_to_numeric);
    }
    if let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
        LeanTargetObjectRepresentation::lower(object)?
    {
        if context
            .numeric_representations
            .get(&symbol_id)
            .is_some_and(|selected| selected == &numeric)
        {
            let source_to_numeric = context
                .numeric_representation_equalities
                .get(&symbol_id)
                .ok_or_else(|| {
                    format!(
                        "exact predicate argument `{object}` has a numeric observation but no equality bridge"
                    )
                })?;
            return Ok(format!(
                "Litex.Same.trans ({exact_to_numeric}) (Litex.Same.symm ({source_to_numeric}))"
            ));
        }
    }
    // Closed numeric expressions elaborate their direct Complex notation and
    // the exact carrier's canonical cast to the same Mathlib value. Keep the
    // reviewed carrier bridge and let Lean check that endpoint conversion.
    if matches!(
        LeanTargetObjectRepresentation::lower(object)?,
        LeanTargetObjectRepresentation::Number { .. } | LeanTargetObjectRepresentation::Constant(_)
    ) {
        return Ok(exact_to_numeric);
    }
    Err(format!(
        "exact predicate argument `{object}` changed from source `{source}` to unrelated numeric observation `{numeric}`"
    ))
}

pub(in super::super) fn render_concrete_predicate_argument(
    binding: &PredicateBinding,
    argument_index: usize,
    object: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let Some(definition) = binding.definition.as_ref() else {
        // Abstract predicates deliberately have no Litex-side parameter
        // classification to unwrap. Their generated Lean axiom remains
        // universe-polymorphic over the source value's existing host carrier.
        return render_obj(object, context);
    };
    let parameter_types = definition
        .typed_parameters
        .collect_param_bindings_with_types();
    let (_, parameter_type) = parameter_types.get(argument_index).ok_or_else(|| {
        format!("concrete predicate argument {argument_index} has no declared parameter")
    })?;
    match parameter_type {
        ParamType::Obj(set) if binding.exact_parameters[argument_index] => {
            render_exact_predicate_argument(object, set, context)
        }
        ParamType::Obj(Obj::StandardSet(_)) => {
            // Proper numeric subsets use a Complex-facing predicate ABI, but
            // the value passed at each call site must still be the canonical
            // numeric observation selected by visible membership evidence.
            // Rendering compositionally (rather than `In.rep` on the whole
            // expression) keeps `epsilon / d`, products, and named members on
            // the same representation used by their checked arithmetic facts.
            render_numeric_obj(object, context).or_else(|_| render_obj(object, context))
        }
        ParamType::Obj(_) => render_obj(object, context),
        ParamType::Set(_) => render_obj(object, context),
        unsupported => Err(format!(
            "concrete predicate argument {argument_index} has unsupported type `{unsupported}`"
        )),
    }
}
