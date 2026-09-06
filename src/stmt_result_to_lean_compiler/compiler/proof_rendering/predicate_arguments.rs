//! Exact and concrete predicate argument rendering.

use super::super::*;

pub(in super::super) fn object_is_symbol(object: &Obj, symbol_id: SymbolId) -> bool {
    matches!(object, Obj::Atom(atom) if atom.symbol_ref().is_some_and(|symbol| symbol.id() == symbol_id))
}

/// Whether the source syntax itself fixes an expression's host carrier to
/// `ℂ`.  A bare Litex atom is intentionally excluded: even when its spelling
/// has a numeric-looking rendering, its checked source carrier may still be
/// heterogeneous.  The theorem-call path must use `In.rep` for that case.
pub(in super::super) fn object_has_closed_complex_carrier(object: &Obj) -> bool {
    match object {
        Obj::Number(_) | Obj::ImaginaryUnit(_) | Obj::EulerNumber(_) | Obj::Pi(_) => true,
        Obj::Add(operation) => {
            object_has_closed_complex_carrier(operation.left.as_ref())
                && object_has_closed_complex_carrier(operation.right.as_ref())
        }
        Obj::Sub(operation) => {
            object_has_closed_complex_carrier(operation.left.as_ref())
                && object_has_closed_complex_carrier(operation.right.as_ref())
        }
        Obj::Mul(operation) => {
            object_has_closed_complex_carrier(operation.left.as_ref())
                && object_has_closed_complex_carrier(operation.right.as_ref())
        }
        Obj::Div(operation) => {
            object_has_closed_complex_carrier(operation.left.as_ref())
                && object_has_closed_complex_carrier(operation.right.as_ref())
        }
        Obj::Abs(operation) => object_has_closed_complex_carrier(operation.arg.as_ref()),
        Obj::Mod(operation) => {
            object_has_closed_complex_carrier(operation.left.as_ref())
                && object_has_closed_complex_carrier(operation.right.as_ref())
        }
        Obj::Pow(operation) => {
            object_has_closed_complex_carrier(operation.base.as_ref())
                && matches!(operation.exponent.as_ref(), Obj::Number(_))
        }
        _ => false,
    }
}

/// Build the reverse local `Same` edge from the exact `C.Carrier = ℂ`
/// representative selected by one membership proof back to a closed native
/// complex source expression.  The ordinary `In.same_rep` edge can carry
/// Core's default observer when `C.Carrier` is hidden behind a set definition.
/// First reify the carrier selection as native equality with `In.rep_exact`,
/// then use the native observer and `AsComplex` evidence explicitly.
/// Heterogeneous source objects do not use this helper; they stay on the
/// observation-free edge.
pub(in super::super) fn render_complex_same_from_membership(
    source: &str,
    selected: &str,
    membership: &str,
) -> String {
    format!(
        "(by\n  have __selected_eq : {source} = (show ℂ from ({selected})) := by\n    simpa only [Litex.In.rep_exact] using (Eq.symm (Litex.In.rep_exact ({source}) ({membership})))\n  have __source_same : @Litex.Same ℂ ℂ Litex.complexComplexObserver Litex.complexComplexObserver {source} (show ℂ from ({selected})) := Litex.Same.ofEq __selected_eq\n  have __source_as_complex : @Litex.AsComplex ℂ Litex.complexComplexObserver {source} {source} := Litex.AsComplex.complex {source}\n  have __selected_as_complex : @Litex.AsComplex ℂ Litex.complexComplexObserver (show ℂ from ({selected})) (show ℂ from ({selected})) := Litex.AsComplex.complex (show ℂ from ({selected}))\n  have __observed_equal := (__source_same).complexEq __source_as_complex __selected_as_complex\n  exact (show Litex.Same (show ℂ from ({selected})) ({source}) from Litex.Same.ofEq (Eq.symm __observed_equal)))"
    )
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

pub(in super::super) fn resolve_visible_exact_membership_proof(
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

/// Select a numeric representative through a visible subset Result. A
/// heterogeneous parameter may be introduced as `x : E`, while the consumer
/// expects the target carrier `R`; the retained subset membership is the only
/// valid bridge between those carriers.
pub(in super::super) fn resolve_visible_subset_transport_real_argument(
    object: &Obj,
    target_set: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<Option<(String, String)>, String> {
    let source = render_obj(object, context)?;
    let lowered_target_set = LeanTargetObjectRepresentation::lower(target_set)?;
    for transport in context.subset_membership_transports.iter().rev() {
        // The target is supplied by the caller (currently the native `R`
        // consumer). Restrict this bridge to the exact retained target key;
        // attempting to normalize arbitrary source definitions here would
        // re-enter the runtime's global environment machinery while rendering
        // a local compiler frame.
        if obj_equality_key(&transport.target_set) != obj_equality_key(target_set) {
            continue;
        }
        let Ok(membership) =
            resolve_visible_subset_source_membership_proof(object, &transport.source_set, context)
        else {
            continue;
        };
        // A subset whose source is a predicate-defined set already carries a
        // canonical base representative inside its membership witness.  Use
        // that witness's `.val` directly instead of selecting a second,
        // unrelated `In.rep x target` value: arbitrary predicates are not
        // extensional under a no-observation `Same` edge, so the latter could
        // not soundly inherit the source predicate proof.
        let source_is_set_builder = match &transport.source_set {
            Obj::SetBuilder(_) => true,
            Obj::Atom(atom) => atom
                .symbol_ref()
                .and_then(|symbol| context.transparent_object_definitions.get(&symbol.id()))
                .is_some_and(|definition| matches!(definition.value, Obj::SetBuilder(_))),
            _ => false,
        };
        if source_is_set_builder {
            let source_representative = format!("Litex.In.rep {source} ({membership})");
            let source_base = format!("({source_representative}).val");
            let Some(real) = exact_set_real_value(&lowered_target_set, &source_base) else {
                continue;
            };
            let same = format!(
                "Litex.Same.symm (Litex.Same.trans (Litex.In.same_rep {source} ({membership})) (Litex.Same.subtypeNoObservation ({source_representative})))"
            );
            return Ok(Some((real, same)));
        }
        let target_membership = format!(
            "(({}) {} ({}))",
            transport.proof_expression, source, membership
        );
        let target_representative = format!("Litex.In.rep {source} ({target_membership})");
        let Some(real) = exact_set_real_value(&lowered_target_set, &target_representative) else {
            continue;
        };
        let same = format!("Litex.Same.symm (Litex.In.same_rep {source} ({target_membership}))");
        return Ok(Some((real, same)));
    }
    Ok(None)
}

/// Membership lookup used by subset transport rendering. Keep this lookup
/// deliberately shallow: the general renderer's lexical fallback may render
/// arbitrary retained arithmetic facts, which would re-enter numeric
/// rendering while we are already resolving a numeric representative.
fn resolve_visible_subset_source_membership_proof(
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
    let rendered_object = render_obj(object, context)?;
    let (
        LeanTargetObjectRepresentation::Symbol { .. },
        LeanTargetObjectRepresentation::Symbol { .. },
    ) = (
        LeanTargetObjectRepresentation::lower(object)?,
        LeanTargetObjectRepresentation::lower(set)?,
    )
    else {
        return Err(format!(
            "subset transport source `{object}` has no direct visible membership in `{set}`"
        ));
    };
    let rendered_set = render_obj(set, context)?;
    let mut lexical = context
        .fact_propositions
        .iter()
        .filter_map(|(fact_id, fact)| {
            let (element, retained_set) = membership_parts(fact).ok()?;
            let (
                LeanTargetObjectRepresentation::Symbol { .. },
                LeanTargetObjectRepresentation::Symbol { .. },
            ) = (
                LeanTargetObjectRepresentation::lower(element).ok()?,
                LeanTargetObjectRepresentation::lower(retained_set).ok()?,
            )
            else {
                return None;
            };
            (render_obj(element, context).ok().as_deref() == Some(rendered_object.as_str())
                && render_obj(retained_set, context).ok().as_deref() == Some(rendered_set.as_str()))
            .then_some((*fact_id, fact))
        })
        .collect::<Vec<_>>();
    lexical.sort_by_key(|(fact_id, _)| *fact_id);
    for (fact_id, fact) in lexical {
        if let Ok(proof) = resolve_fact_citation(&fact_id, fact, context) {
            return Ok(proof);
        }
    }
    Err(format!(
        "subset transport source `{object}` has no visible membership in `{set}`"
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
            // A refined-positive argument may be a simple division such as
            // `epsilon / 2`.  The local exact carrier already carries
            // `epsilon.property`; ask the kernel for the corresponding
            // native `div_pos` proof instead of hoping `positivity` unfolds a
            // dependent subtype projection through the generated term.
            if let Ok(LeanTargetObjectRepresentation::BuiltinApp {
                operator: LeanTargetBuiltinObjectOperator::Div,
                arguments,
                ..
            }) = LeanTargetObjectRepresentation::lower(object)
            {
                if let [LeanTargetObjectRepresentation::Symbol { symbol_id, .. }, LeanTargetObjectRepresentation::Number { normalized_value }] =
                    arguments.as_slice()
                {
                    if normalized_value == "2" {
                        if let Some(carrier) = context.exact_positive_real_carriers.get(symbol_id) {
                            let positivity =
                                format!("by\n  exact div_pos ({carrier}).property (by norm_num)");
                            return Ok(format!("(⟨{real}, {positivity}⟩ : (Litex.RPos).Carrier)"));
                        }
                    }
                }
            }
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
            let positivity = if positive_carriers.len() == 1
                && real.contains("/ (2 : ℝ)")
                && real.contains(".val")
            {
                // The lowered source may have crossed a function/template
                // boundary and therefore no longer be structurally visible
                // as `Obj::Div`.  The exact-positive carrier is still the
                // only semantic witness in this frame; use it explicitly.
                format!(
                    "by\n  exact div_pos ({}).property (by norm_num)",
                    positive_carriers[0]
                )
            } else if premises.is_empty() {
                "by positivity".to_string()
            } else {
                format!("by\n  {}\n  positivity", premises.join("\n  "))
            };
            return Ok(format!("(⟨{real}, {positivity}⟩ : (Litex.RPos).Carrier)"));
        }
    }
    if matches!(
        LeanTargetObjectRepresentation::lower(object),
        Ok(LeanTargetObjectRepresentation::Symbol { .. })
    ) {
        if let Some((real, _same)) =
            resolve_visible_subset_transport_real_argument(object, set, context)?
        {
            return Ok(real);
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
        Obj::StandardSet(StandardSet::C) => {
            // A theorem parameter over `C` must receive an actual `ℂ` value.
            // Many source objects already have a compositional numeric
            // rendering, but an arbitrary heterogeneous object (for example
            // a function application whose only evidence is `x $in C`) does
            // not.  In that case the checked membership proof is the only
            // sound bridge: `In.rep` selects the exact `C.Carrier = ℂ`
            // representative for this call.  Do not invent a cast from the
            // source syntax, and do not search a different ambient fact.
            if object_has_closed_complex_carrier(object) {
                render_numeric_obj(object, context).or_else(|_| representative())
            } else {
                representative()
            }
        }
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
        if matches!(
            LeanTargetObjectRepresentation::lower(object),
            Ok(LeanTargetObjectRepresentation::Symbol { .. })
        ) {
            if let Some((selected, same)) =
                resolve_visible_subset_transport_real_argument(object, set, context)?
            {
                if exact == selected {
                    return Ok(same);
                }
            }
        }
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
    if matches!(set, Obj::StandardSet(StandardSet::C)) {
        if let Ok(membership) = resolve_visible_exact_membership_proof(object, set, context) {
            let selected = format!("Litex.In.rep {source} ({membership})");
            let exact_without_outer = exact
                .strip_prefix('(')
                .and_then(|value| value.strip_suffix(')'))
                .unwrap_or(&exact);
            let selected_without_outer = selected
                .strip_prefix('(')
                .and_then(|value| value.strip_suffix(')'))
                .unwrap_or(&selected);
            if exact_without_outer == selected_without_outer {
                // A `C` theorem parameter is homogeneous at its exact
                // carrier (`C.Carrier = ℂ`).  When the source can also be
                // rendered as a complex term, use the old Core observer
                // contract to make this bridge explicit: `AsComplex` gives
                // the two observations, and `Same.complexEq` supplies the
                // native equality used to reify the reverse edge.  This is
                // local theorem-call evidence; it is not a new environment
                // fact or a second representative lookup.
                let source_has_known_complex_carrier = object_has_closed_complex_carrier(object);
                if source_has_known_complex_carrier {
                    return Ok(render_complex_same_from_membership(
                        &source,
                        &selected,
                        &membership,
                    ));
                }
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
