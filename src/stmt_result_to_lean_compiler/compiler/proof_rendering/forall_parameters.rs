//! Universal fact types and parameter aliases.

use super::super::*;

pub(in super::super) fn forall_parameter_uses_exact_refined_numeric_carrier(set: &Obj) -> bool {
    matches!(set, Obj::StandardSet(StandardSet::RPos))
}

/// Universal parameters over native reals and exact real refinements keep the
/// exact Lean carrier.  A theorem application may still start from a
/// heterogeneous Litex value; its checked membership Result selects the real
/// argument before the theorem is called.  Keeping the binder exact prevents
/// independent `In.rep` choices from becoming the observable meaning of one
/// real variable.
pub(in super::super) fn forall_parameter_uses_exact_real_carrier(set: &Obj) -> bool {
    matches!(set, Obj::StandardSet(StandardSet::R | StandardSet::RPos))
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
                && !forall_parameter_uses_exact_object_carrier(set)
    )
}

pub(in super::super) fn render_forall_fact_type(
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
        if forall_parameter_uses_exact_object_carrier(set) {
            let rendered_set = render_obj(set, &context)?;
            binders.push(format!("({name} : ({rendered_set}).Carrier)"));
            binders.push(format!(
                "(__type{} : Litex.In {name} {rendered_set})",
                index + 1
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
                &format!("__type{}", index + 1),
                function,
                &mut context,
            )?;
            install_result_owned_forall_parameter_fact_alias(
                binding.id(),
                &expected,
                &format!("__type{}", index + 1),
                &mut context,
            )?;
            let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
            context
                .exact_carrier_values
                .insert(binding.id(), name.clone());
            if forall_parameter_uses_exact_refined_numeric_carrier(set) {
                context
                    .exact_positive_real_carriers
                    .insert(binding.id(), name.clone());
            }
            if let Some(real) = exact_set_real_value(&lowered_set, &name) {
                context.numeric_real_values.insert(binding.id(), real);
            }
            if let Some(integer) = exact_set_integer_value(&lowered_set, &name) {
                context.numeric_integer_values.insert(binding.id(), integer);
            }
            if let Some(rational) = exact_set_rational_value(&lowered_set, &name) {
                context
                    .numeric_rational_values
                    .insert(binding.id(), rational);
            }
            if let Some(numeric) = exact_set_numeric_value(&lowered_set, &name) {
                context
                    .numeric_representations
                    .insert(binding.id(), numeric);
            }
            if let Some(equality) = exact_set_numeric_equality(&lowered_set, &name) {
                context
                    .numeric_representation_equalities
                    .insert(binding.id(), equality);
            }
            if let Some(proof) = exact_set_numeric_proof(&lowered_set, &name) {
                context
                    .numeric_representation_memberships
                    .insert(binding.id(), proof);
            }
            continue;
        }
        let carrier = format!("__carrier{}", index + 1);
        match set {
            Obj::FnSet(_) | Obj::FiniteSeqSet(_) | Obj::SeqSet(_) => {
                binders.push(format!("{{{carrier} : Type 1}}"));
                binders.push(format!("({name} : {carrier})"));
            }
            _ => {
                binders.push(format!("{{{carrier} : Type}}"));
                binders.push(format!("({name} : {carrier})"));
            }
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
    let exact_carrier_value = format!("(Litex.In.rep {source_name} {proof_name})");
    context
        .exact_carrier_values
        .insert(symbol_id, exact_carrier_value);
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
