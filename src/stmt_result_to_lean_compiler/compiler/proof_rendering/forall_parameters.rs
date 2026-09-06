//! Universal fact types and parameter aliases.

use super::super::*;

pub(in super::super) fn forall_parameter_uses_exact_refined_numeric_carrier(set: &Obj) -> bool {
    matches!(set, Obj::StandardSet(StandardSet::RPos))
}

/// Adapter-facing real and complex parameters use one native complex host
/// carrier.  Their `Litex.In` premise remains the semantic fact that records
/// membership in `R` or `C`; it does not retype the expression as `ℝ`.
pub(in super::super) fn forall_parameter_uses_complex_host_carrier(set: &Obj) -> bool {
    matches!(set, Obj::StandardSet(StandardSet::R | StandardSet::C))
}

/// Positive-real values remain exact subtypes because positivity is part of
/// the native carrier contract used by the current positive-real rules.
pub(in super::super) fn forall_parameter_uses_exact_real_carrier(set: &Obj) -> bool {
    matches!(set, Obj::StandardSet(StandardSet::RPos))
}

pub(in super::super) fn forall_parameter_uses_exact_complex_carrier(_set: &Obj) -> bool {
    false
}

pub(in super::super) fn forall_parameter_uses_exact_structured_set_carrier(set: &Obj) -> bool {
    matches!(
        set,
        Obj::SetBuilder(_)
            | Obj::FnRange(_)
            | Obj::IntervalObj(_)
            | Obj::OneSideInfinityIntervalObj(_)
    )
}

pub(in super::super) fn forall_parameter_uses_exact_object_carrier(set: &Obj) -> bool {
    forall_parameter_uses_exact_real_carrier(set)
        || forall_parameter_uses_exact_complex_carrier(set)
        || forall_parameter_uses_exact_structured_set_carrier(set)
        || matches!(set, Obj::FnSet(_) | Obj::FiniteSeqSet(_) | Obj::SeqSet(_))
}

pub(in super::super) fn forall_parameter_uses_implicit_host_carrier(
    param_type: &ParamType,
) -> bool {
    matches!(
        param_type,
        ParamType::Obj(set)
            if !matches!(set, Obj::StandardSet(StandardSet::Z))
                && !forall_parameter_uses_complex_host_carrier(set)
                && !forall_parameter_uses_exact_object_carrier(set)
    )
}

/// Projecting a polymorphic forall clause through a conjunction must delay
/// field selection until after the complete telescope has been introduced.
/// Otherwise Lean may instantiate an implicit host carrier while evaluating
/// `definition.right`, freezing it as a metavariable before the caller's
/// carrier is in scope.
pub(in super::super) fn render_eta_expanded_forall_projection(
    forall: &ForallFact,
    selected_component: &str,
) -> Result<String, String> {
    let mut intro_names = Vec::new();
    let mut arguments = Vec::new();
    for (index, (_, parameter_type)) in forall
        .typed_parameters
        .collect_param_bindings_with_types()
        .iter()
        .enumerate()
    {
        let suffix = index + 1;
        let parameter = format!("__projection_parameter{suffix}");
        match parameter_type {
            ParamType::Set(_) => {
                intro_names.push(parameter.clone());
                arguments.push(parameter);
            }
            ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {
                let requirement = format!("__projection_type{suffix}");
                intro_names.extend([parameter.clone(), requirement.clone()]);
                arguments.extend([parameter, requirement]);
            }
            ParamType::Obj(set) if matches!(set, Obj::StandardSet(StandardSet::Z)) => {
                intro_names.push(parameter.clone());
                arguments.push(parameter);
            }
            ParamType::Obj(_) => {
                if forall_parameter_uses_implicit_host_carrier(parameter_type) {
                    intro_names.push(format!("__projection_carrier{suffix}"));
                }
                let requirement = format!("__projection_type{suffix}");
                intro_names.extend([parameter.clone(), requirement.clone()]);
                arguments.extend([parameter, requirement]);
            }
        }
    }
    for index in 0..forall.dom_facts.len() {
        let domain = format!("__projection_domain{}", index + 1);
        intro_names.push(domain.clone());
        arguments.push(domain);
    }
    if intro_names.is_empty() {
        return Err("definition projection retained a forall without binders".into());
    }
    Ok(format!(
        "intro {}\n  exact ({selected_component}) {}",
        intro_names.join(" "),
        arguments.join(" ")
    ))
}

pub(in super::super) fn render_forall_fact_type(
    forall: &ForallFact,
    outer_context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    render_forall_fact_type_with_conclusion_renderer(forall, outer_context, render_fact)
}

pub(in super::super) fn render_forall_fact_type_with_no_observation_equality_conclusions(
    forall: &ForallFact,
    outer_context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    render_forall_fact_type_with_conclusion_renderer(
        forall,
        outer_context,
        render_no_observation_equality_alternatives_fact,
    )
}

fn render_forall_fact_type_with_conclusion_renderer(
    forall: &ForallFact,
    outer_context: &StmtResultToLeanCompilerEnvironmentStack,
    render_conclusion: fn(
        &Fact,
        &StmtResultToLeanCompilerEnvironmentStack,
    ) -> Result<String, String>,
) -> Result<String, String> {
    let mut context = outer_context.clone();
    let mut binders = Vec::new();
    // Domain facts are introduced after the parameter telescope, but a
    // subset domain is exactly the evidence needed to select the target
    // numeric representative of a parameter.  Keep the parameter metadata so
    // we can replay that lexical transport once all domain proofs are visible.
    let mut subset_transport_parameters = Vec::new();
    for (index, (binding, param_type)) in forall
        .typed_parameters
        .collect_param_bindings_with_types()
        .iter()
        .enumerate()
    {
        let ordinal = index + 1;
        let base_name = format!("__p{ordinal}");
        // A caller may have already installed this exact SymbolId as one side
        // of a verifier-certified alpha alias (structured induction is the
        // current example).  Preserve that explicit lexical choice.  In the
        // ordinary nested-forall case the new SymbolId has no such binding,
        // so an outer `__pN` still forces a collision-free local name.
        let explicitly_prebound_to_base = context
            .symbol_names
            .get(&binding.id())
            .is_some_and(|visible| visible == &base_name);
        let collides_with_outer_binder =
            !explicitly_prebound_to_base && context.reserved_lean_names.contains(&base_name);
        let local_suffix = if collides_with_outer_binder {
            format!("{ordinal}_s{}", binding.id().value())
        } else {
            ordinal.to_string()
        };
        let name = format!("__p{local_suffix}");
        let type_name = format!("__type{local_suffix}");
        let carrier_name = format!("__carrier{local_suffix}");
        context.reserved_lean_names.insert(name.clone());
        context.reserved_lean_names.insert(type_name.clone());
        context.reserved_lean_names.insert(carrier_name.clone());
        context.symbol_names.insert(binding.id(), name.clone());
        // The outer Result environment may already contain callable evidence
        // for this source SymbolId under proof-layer names such as `g` and
        // `__hN`.  A rendered forall telescope introduces fresh textual
        // binders (`__pN`, `__typeN`), so those older function bindings are
        // lexically shadowed and must not win exact-function argument
        // selection inside the new type.
        context
            .function_bindings
            .retain(|_, function| function.symbol_id != binding.id());
        context.exact_carrier_values.remove(&binding.id());
        context.exact_positive_real_carriers.remove(&binding.id());
        context.numeric_representations.remove(&binding.id());
        context
            .numeric_representation_equalities
            .remove(&binding.id());
        context
            .numeric_representation_memberships
            .remove(&binding.id());
        context.numeric_real_values.remove(&binding.id());
        context.numeric_integer_values.remove(&binding.id());
        context.numeric_rational_values.remove(&binding.id());
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
            binders.push(format!("({type_name} : {property} {name})"));
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
                &type_name,
                None,
                &mut context,
            )?;
            install_result_owned_forall_parameter_fact_alias(
                binding.id(),
                &expected,
                &type_name,
                &mut context,
            )?;
            continue;
        }

        let set = parameter_set(param_type)?;
        if matches!(set, Obj::StandardSet(StandardSet::Z)) {
            binders.push(format!("({name} : ℤ)"));
            let proof = format!("(Litex.In.own Litex.Z {name})");
            let expected = format!("Litex.In {name} Litex.Z");
            install_rendered_parameter_aliases(
                binding.id(),
                &expected,
                &proof,
                None,
                &mut context,
            )?;
            install_result_owned_forall_parameter_fact_alias(
                binding.id(),
                &expected,
                &proof,
                &mut context,
            )?;
            install_structured_induction_native_integer_symbol(binding.id(), &name, &mut context);
            continue;
        }
        if forall_parameter_uses_complex_host_carrier(set)
            && !forall_parameter_has_direct_membership_domain(binding.id(), &forall.dom_facts)
        {
            let rendered_set = render_obj(set, &context)?;
            binders.push(format!("({name} : ℂ)"));
            binders.push(format!("({type_name} : Litex.In {name} {rendered_set})"));
            let expected = format!("Litex.In {name} {rendered_set}");
            install_rendered_parameter_aliases(
                binding.id(),
                &expected,
                &type_name,
                None,
                &mut context,
            )?;
            install_result_owned_forall_parameter_fact_alias(
                binding.id(),
                &expected,
                &type_name,
                &mut context,
            )?;
            // Keep a real representative available only for consumers whose
            // native theorem genuinely requires `ℝ` (for example the
            // completeness bridge).  `numeric_representations` is deliberately
            // left empty so ordinary Litex arithmetic continues to render the
            // complex-host binder directly.
            if matches!(set, Obj::StandardSet(StandardSet::R)) {
                let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
                if let Some(real) = membership_real_value(&lowered_set, &name, &type_name) {
                    context.numeric_real_values.insert(binding.id(), real);
                }
            }
            // Keep the public Litex expression on the complex host carrier.
            // Real-native consumers select a local `ℝ` representative at
            // their own adapter boundary instead of rewriting every ordinary
            // arithmetic occurrence to `Litex.In.rep`.
            continue;
        }
        if forall_parameter_uses_exact_object_carrier(set)
            && !forall_parameter_has_direct_membership_domain(binding.id(), &forall.dom_facts)
        {
            let rendered_set = render_obj(set, &context)?;
            binders.push(format!("({name} : ({rendered_set}).Carrier)"));
            binders.push(format!(
                "({type_name} : Litex.In (α := ({rendered_set}).Carrier) {name} {rendered_set})"
            ));
            let expected = format!("Litex.In {name} {rendered_set}");
            let function = match set {
                Obj::FnSet(function) => {
                    Some(LeanTargetFunctionTypeRepresentation::lower(function)?)
                }
                Obj::FiniteSeqSet(sequence) => {
                    let function =
                        Runtime::default().finite_seq_set_to_fn_set(sequence, default_line_file());
                    Some(LeanTargetFunctionTypeRepresentation::lower(&function)?)
                }
                Obj::SeqSet(sequence) => {
                    let function =
                        Runtime::default().seq_set_to_fn_set(sequence, default_line_file());
                    Some(LeanTargetFunctionTypeRepresentation::lower(&function)?)
                }
                _ => None,
            };
            install_rendered_parameter_aliases(
                binding.id(),
                &expected,
                &type_name,
                function,
                &mut context,
            )?;
            install_result_owned_forall_parameter_fact_alias(
                binding.id(),
                &expected,
                &type_name,
                &mut context,
            )?;
            let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
            // The binder already inhabits the exact source set carrier.  Its
            // explicit membership argument is Result-owned evidence, not a
            // second choice of the value represented by this variable.
            install_exact_set_builder_parameter_representation(
                binding.id(),
                &lowered_set,
                &name,
                &mut context,
            );
            if forall_parameter_uses_exact_refined_numeric_carrier(set) {
                context
                    .exact_positive_real_carriers
                    .insert(binding.id(), name.clone());
            }
            install_visible_subset_transports_for_parameter(
                binding.id(),
                &name,
                &type_name,
                set,
                &mut context,
            )?;
            subset_transport_parameters.push((
                binding.id(),
                name.clone(),
                type_name.clone(),
                set.clone(),
            ));
            continue;
        }
        match set {
            Obj::FnSet(_) | Obj::FiniteSeqSet(_) | Obj::SeqSet(_) => {
                binders.push(format!("{{{carrier_name} : Type 1}}"));
                binders.push(format!("({name} : {carrier_name})"));
            }
            _ => {
                binders.push(format!("{{{carrier_name} : Type}}"));
                binders.push(format!("({name} : {carrier_name})"));
            }
        }
        binders.push(format!(
            "({type_name} : Litex.In {name} {})",
            render_obj(set, &context)?
        ));
        let expected = format!("Litex.In {name} {}", render_obj(set, &context)?);
        install_rendered_parameter_aliases(
            binding.id(),
            &expected,
            &type_name,
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
            &type_name,
            &mut context,
        )?;
        let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
        if let Some(real) = membership_real_value(&lowered_set, &name, &type_name) {
            context.numeric_real_values.insert(binding.id(), real);
        }
        if let Some(integer) = membership_integer_value(&lowered_set, &name, &type_name) {
            context.numeric_integer_values.insert(binding.id(), integer);
        }
        if let Some(rational) = membership_rational_value(&lowered_set, &name, &type_name) {
            context
                .numeric_rational_values
                .insert(binding.id(), rational);
        }
        if let Some(representation) = membership_numeric_value(&lowered_set, &name, &type_name) {
            context
                .numeric_representations
                .insert(binding.id(), representation);
        }
        if let Some(equality) = membership_numeric_equality(&lowered_set, &name, &type_name) {
            context
                .numeric_representation_equalities
                .insert(binding.id(), equality);
        }
        if let Some(proof) = membership_numeric_proof(&lowered_set, &name, &type_name) {
            context
                .numeric_representation_memberships
                .insert(binding.id(), proof);
        }
        install_visible_subset_transports_for_parameter(
            binding.id(),
            &name,
            &type_name,
            set,
            &mut context,
        )?;
        subset_transport_parameters.push((
            binding.id(),
            name.clone(),
            type_name.clone(),
            set.clone(),
        ));
    }
    for (index, premise) in forall.dom_facts.iter().enumerate() {
        let proof_name = format!("__domain{}", index + 1);
        binders.push(format!(
            "({proof_name} : {})",
            render_fact(premise, &context)?
        ));
        install_subset_transport_from_fact(premise, &proof_name, &mut context)?;
    }
    for (symbol_id, parameter_name, parameter_membership, source_set) in subset_transport_parameters
    {
        install_visible_subset_transports_for_parameter(
            symbol_id,
            &parameter_name,
            &parameter_membership,
            &source_set,
            &mut context,
        )?;
    }
    let conclusions = forall
        .then_facts
        .iter()
        .map(|conclusion| render_conclusion(&conclusion.clone().to_fact(), &context))
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

fn direct_membership_subject_symbol_id(fact: &Fact) -> Option<SymbolId> {
    match fact {
        Fact::AtomicFact(AtomicFact::InFact(in_fact)) => match &in_fact.element {
            Obj::Atom(atom) => atom.symbol_ref().map(SymbolRef::id),
            _ => None,
        },
        Fact::AtomicFact(AtomicFact::NotEqualFact(not_equal)) => match &not_equal.left {
            Obj::Atom(atom) => atom.symbol_ref().map(SymbolRef::id),
            _ => None,
        },
        _ => None,
    }
}

pub(in super::super) fn forall_parameter_has_direct_membership_domain(
    symbol_id: SymbolId,
    domains: &[Fact],
) -> bool {
    domains.iter().any(|fact| {
        matches!(
            direct_membership_subject_symbol_id(fact),
            Some(candidate) if candidate == symbol_id
        ) && matches!(fact, Fact::AtomicFact(AtomicFact::InFact(_)))
    })
}

/// While rendering a nested forall type, connect the textual binder
/// hypothesis to the exact parameter FactId retained by the recursive WD
/// Result. The Result context can contain aliases from several lexical
/// binders, so SymbolId is the structural discriminator; no proposition-based
/// environment lookup is performed.
pub(in super::super) fn install_result_owned_forall_parameter_fact_alias(
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

pub(in super::super) fn install_parameter_fact_aliases(
    symbol_id: SymbolId,
    primary_fact_id: FactId,
    proposition: &Fact,
    proof_name: &str,
    set: &Obj,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let function = match set {
        Obj::FnSet(function) => Some(LeanTargetFunctionTypeRepresentation::lower(function)?),
        Obj::FiniteSeqSet(sequence) => {
            let function =
                Runtime::default().finite_seq_set_to_fn_set(sequence, default_line_file());
            Some(LeanTargetFunctionTypeRepresentation::lower(&function)?)
        }
        Obj::SeqSet(sequence) => {
            let function = Runtime::default().seq_set_to_fn_set(sequence, default_line_file());
            Some(LeanTargetFunctionTypeRepresentation::lower(&function)?)
        }
        _ => None,
    };
    let expected = render_fact(proposition, context)?;
    context
        .fact_names
        .insert(primary_fact_id, proof_name.to_string());
    context
        .fact_propositions
        .insert(primary_fact_id, proposition.clone());
    if let Some(function) = &function {
        context.function_bindings.insert(
            primary_fact_id,
            FunctionBinding {
                symbol_id,
                function: function.clone(),
                membership_proof_name: proof_name.to_string(),
                direct: false,
            },
        );
    }
    install_rendered_parameter_aliases(symbol_id, &expected, proof_name, function, context)?;
    let source_name = context
        .symbol_names
        .get(&symbol_id)
        .cloned()
        .ok_or_else(|| "parameter alias has no visible compiler symbol".to_string())?;

    // `R`/`C` forall binders use the complex host ABI.  Their membership proof
    // remains visible evidence, but ordinary Litex expressions must keep the
    // binder itself rather than replacing it with an independent `In.rep`
    // choice.  Native real/rational/integer consumers opt into a local
    // representative at their own boundary.
    if forall_parameter_uses_complex_host_carrier(set) {
        if matches!(set, Obj::StandardSet(StandardSet::R)) {
            let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
            if let Some(real) = membership_real_value(&lowered_set, &source_name, proof_name) {
                context.numeric_real_values.insert(symbol_id, real);
            }
        }
        return Ok(());
    }

    // Integer-only target operators cannot be applied to the ordinary
    // Complex view used by Litex arithmetic. Retain the exact representative
    // selected by this parameter's membership proof in the current compiler
    // frame; child lexical frames inherit it and pop discards it.
    let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
    let exact_carrier_value = format!("(Litex.In.rep {source_name} {proof_name})");
    context.exact_carrier_source_equalities.insert(
        symbol_id,
        ExactCarrierSourceEqualityBinding::new(
            exact_carrier_value.clone(),
            format!("Litex.Same.symm (Litex.In.same_rep {source_name} {proof_name})"),
        ),
    );
    install_exact_set_builder_parameter_representation(
        symbol_id,
        &lowered_set,
        &exact_carrier_value,
        context,
    );
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

pub(in super::super) fn install_numeric_representations_from_membership(
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

pub(in super::super) fn install_rendered_parameter_aliases(
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
