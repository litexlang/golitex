//! Exact and concrete predicate argument rendering.

use super::super::*;

pub(in super::super) fn object_is_symbol(object: &Obj, symbol_id: SymbolId) -> bool {
    matches!(object, Obj::Atom(atom) if atom.symbol_ref().is_some_and(|symbol| symbol.id() == symbol_id))
}

pub(in super::super) fn cached_exact_membership_selection_proof<'a>(
    exact: &'a str,
    source: &str,
) -> Option<&'a str> {
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
    // A verifier-checked closed numeric argument of a refined standard set
    // has a canonical exact carrier: the normalized native value paired with
    // its refinement proof. Recheck both the sign/integrality classification
    // here and the proposition in generated Lean. This is the closed-value
    // counterpart of selecting a variable through its retained `In` proof;
    // it does not search for or invent a different mathematical fact.
    if let (Obj::StandardSet(standard_set), Some(evaluation)) =
        (set, object.evaluate_to_normalized_decimal_number())
    {
        let normalized = &evaluation.normalized_value;
        let sign = compare_normalized_number_str_to_zero(normalized);
        let native_type = match standard_set {
            StandardSet::NPos
                if matches!(sign, NumberCompareResult::Greater)
                    && normalized
                        .chars()
                        .all(|character| character.is_ascii_digit()) =>
            {
                Some("ℕ")
            }
            StandardSet::QPos if matches!(sign, NumberCompareResult::Greater) => Some("ℚ"),
            StandardSet::RPos if matches!(sign, NumberCompareResult::Greater) => Some("ℝ"),
            StandardSet::ZNeg
                if matches!(sign, NumberCompareResult::Less)
                    && normalized.parse::<i128>().is_ok() =>
            {
                Some("ℤ")
            }
            StandardSet::QNeg if matches!(sign, NumberCompareResult::Less) => Some("ℚ"),
            StandardSet::RNeg if matches!(sign, NumberCompareResult::Less) => Some("ℝ"),
            _ => None,
        };
        if let Some(native_type) = native_type {
            let rendered_set = render_obj(set, context)?;
            return Ok(format!(
                "(⟨({normalized} : {native_type}), by norm_num⟩ : ({rendered_set}).Carrier)"
            ));
        }
    }
    if matches!(set, Obj::StandardSet(StandardSet::RPos))
        && !matches!(
            LeanTargetObjectRepresentation::lower(object),
            Ok(LeanTargetObjectRepresentation::Symbol { .. })
        )
    {
        if let Ok(real) = render_real_source_object(object, context) {
            let mut positive_carriers = context
                .exact_positive_real_carriers
                .values()
                .cloned()
                .collect::<Vec<_>>();
            positive_carriers.sort();
            positive_carriers.dedup();
            let premises = positive_carriers
                .iter()
                .enumerate()
                .map(|(index, carrier)| {
                    format!(
                        "have __exact_positive{index} : 0 < (({carrier}).val : ℝ) := ({carrier}).property"
                    )
                })
                .collect::<Vec<_>>();
            let positivity = if premises.is_empty() {
                "by positivity".to_string()
            } else {
                format!("by\n  {}\n  positivity", premises.join("\n  "))
            };
            return Ok(format!("(⟨{real}, {positivity}⟩ : (Litex.RPos).Carrier)"));
        }
    }
    if let Ok(LeanTargetObjectRepresentation::Symbol { symbol_id, name }) =
        LeanTargetObjectRepresentation::lower(object)
    {
        // One symbol may inhabit an exact refined carrier such as a
        // set-builder while a later predicate asks for its underlying exact
        // `R` value. `exact_carrier_values` records the former; the registered
        // real observer supplies the latter. Prefer an already-installed
        // native real, otherwise recover the unique nontrivial projection
        // from a visible checked membership fact. This keeps the existing
        // environment layout while preventing a subtype value from being
        // passed where `R.Carrier` is required.
        if matches!(set, Obj::StandardSet(StandardSet::R)) {
            if let Some(real) = context.numeric_real_values.get(&symbol_id) {
                return Ok(real.clone());
            }
            if let Some(exact) = context.exact_carrier_values.get(&symbol_id) {
                let rendered_source = render_obj(object, context)?;
                if let Some(selection_proof) =
                    cached_exact_membership_selection_proof(exact, &rendered_source)
                {
                    let selection_proof = selection_proof
                        .trim_matches(|character| character == '(' || character == ')');
                    let mut owners = context
                        .fact_names
                        .iter()
                        .filter(|(_, proof)| {
                            proof.trim_matches(|character| character == '(' || character == ')')
                                == selection_proof
                        })
                        .filter_map(|(fact_id, _)| context.fact_propositions.get(fact_id))
                        .filter_map(|fact| membership_parts(fact).ok())
                        .filter(|(element, _)| {
                            obj_equality_key(element) == obj_equality_key(object)
                        })
                        .filter_map(|(_, owner_set)| {
                            let lowered = LeanTargetObjectRepresentation::lower(owner_set).ok()?;
                            render_real_set_observer(&lowered, context, exact).ok()
                        })
                        .collect::<Vec<_>>();
                    owners.sort();
                    owners.dedup();
                    match owners.as_slice() {
                        [owner] => return Ok(owner.clone()),
                        [] => {}
                        _ => {
                            return Err(format!(
                                "predicate argument `{name}` has evidence-distinct exact carrier owners"
                            ));
                        }
                    }
                }
                let mut projections = context
                    .fact_propositions
                    .values()
                    .filter_map(|fact| {
                        let (element, owner_set) = membership_parts(fact).ok()?;
                        (obj_equality_key(element) == obj_equality_key(object)).then_some(owner_set)
                    })
                    .filter_map(|owner_set| {
                        let lowered = LeanTargetObjectRepresentation::lower(owner_set).ok()?;
                        render_real_set_observer(&lowered, context, exact).ok()
                    })
                    .filter(|projection| projection != exact)
                    .collect::<Vec<_>>();
                projections.sort();
                projections.dedup();
                let projected = projections
                    .iter()
                    .filter(|projection| projection.contains(".val"))
                    .cloned()
                    .collect::<Vec<_>>();
                if let [projection] = projected.as_slice() {
                    return Ok(projection.clone());
                }
                match projections.as_slice() {
                    [projection] => return Ok(projection.clone()),
                    [] => {}
                    _ => {
                        return Err(format!(
                            "predicate argument `{name}` has multiple exact real-carrier projections: [{}]",
                            projections.join(", ")
                        ));
                    }
                }
            }
        }
        if let Some(value) = context.exact_carrier_values.get(&symbol_id) {
            return Ok(value.clone());
        }
        // Definition and existential instantiation may alpha-refresh the
        // SymbolId of a retained parameter. Recover only a unique cached
        // representative that names the same visible Lean source binder.
        let source = render_obj(object, context)?;
        let mut lexical_candidates = context
            .exact_carrier_values
            .values()
            .filter(|value| {
                value.as_str() == source
                    || cached_exact_membership_selection_proof(value, &source).is_some()
            })
            .cloned()
            .collect::<Vec<_>>();
        lexical_candidates.sort();
        lexical_candidates.dedup();
        match lexical_candidates.as_slice() {
            [value] => return Ok(value.clone()),
            [] => {}
            _ => {
                return Err(format!(
                    "predicate argument `{name}` has evidence-distinct cached exact representatives"
                ));
            }
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
        Obj::StandardSet(StandardSet::R) => {
            render_real_source_object(object, context).or_else(|_| representative())
        }
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
    if let Ok(LeanTargetObjectRepresentation::Symbol { symbol_id, .. }) =
        LeanTargetObjectRepresentation::lower(object)
    {
        if let Some(binding) = context.exact_carrier_source_equalities.get(&symbol_id) {
            // The binding is installed from the same checked membership FactId
            // that produced `exact`.  The surrounding exact-carrier map may
            // intentionally retain only the lexical source name, so using it
            // as an additional string-equality gate would discard the valid
            // heterogeneous bridge and fall back to a native `realComplex`
            // theorem with the wrong left endpoint.
            return Ok(binding.proof_expression.clone());
        }
    }
    // An exact `R` carrier selected from the visible membership proof may be
    // printed either bare (`In.rep x hx`) or with Lean's redundant `: ℝ`
    // ascription.  These are the same selected value; importantly, the
    // bridge must remain the heterogeneous `Same` proof from that membership,
    // never a cast of the proof object itself.
    if matches!(set, Obj::StandardSet(StandardSet::R)) {
        if let Ok(membership) = resolve_visible_exact_membership_proof(object, set, context) {
            let selected = format!("Litex.In.rep {source} ({membership})");
            if exact.contains(&format!("Litex.In.rep {source}")) {
                return Ok(format!(
                    "Litex.Same.symm (Litex.In.same_rep {source} ({membership}))"
                ));
            }
            let exact_without_outer = exact
                .strip_prefix('(')
                .and_then(|value| value.strip_suffix(')'))
                .unwrap_or(&exact);
            let selected_without_outer = selected
                .strip_prefix('(')
                .and_then(|value| value.strip_suffix(')'))
                .unwrap_or(&selected);
            let exact_without_type = exact_without_outer
                .strip_suffix(" : ℝ")
                .unwrap_or(exact_without_outer)
                .trim();
            if exact_without_type == selected_without_outer {
                return Ok(format!(
                    "Litex.Same.symm (Litex.In.same_rep {source} ({membership}))"
                ));
            }
        }
    }
    if matches!(set, Obj::StandardSet(StandardSet::R))
        && (exact == format!("({source} : ℝ)") || exact == format!("(({source}) : ℝ)"))
    {
        // Context substitution can leave an otherwise native real term with
        // one explicit result ascription. Both endpoints are the same exact
        // `R.Carrier` value, so this is homogeneous reflexive equality rather
        // than a heterogeneous `Same` elimination.
        return Ok("Litex.Same.ofEq (by rfl)".into());
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
    // A compositional numeric Litex expression can have a native real value
    // whose Complex observation differs only by homomorphic coercion, e.g.
    // `((x - 1 : ℝ) : ℂ)` versus `(x : ℂ) - 1`.  The exact carrier
    // bridge reaches the former; Mathlib's cast normalization proves the
    // remaining native equality, which Lean checks at the generated gate.
    if render_numeric_obj(object, context)
        .is_ok_and(|rendered_numeric_source| rendered_numeric_source == source)
    {
        return Ok(format!(
            "Litex.Same.trans ({exact_to_numeric}) (Litex.Same.ofEq (by norm_cast <;> norm_num))"
        ));
    }
    Err(format!(
        "exact predicate argument `{object}` changed from exact `{exact}` and source `{source}` to unrelated numeric observation `{numeric}`"
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
