//! Lean target-set representation rendering.

use super::super::*;

pub(in super::super) fn install_exact_set_builder_parameter_representation(
    symbol_id: SymbolId,
    base_set: &LeanTargetObjectRepresentation,
    value: &str,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) {
    context
        .exact_carrier_values
        .insert(symbol_id, value.to_string());
    if let Some(real) = exact_set_real_value(base_set, value) {
        context.numeric_real_values.insert(symbol_id, real);
    } else {
        // A non-exact carrier still needs the representation-invariant sign
        // predicate used by heterogeneous set-builder transport.
        context.semantic_zero_ended_order_symbols.insert(symbol_id);
    }
    if let Some(integer) = exact_set_integer_value(base_set, value) {
        context.numeric_integer_values.insert(symbol_id, integer);
    }
    if let Some(rational) = exact_set_rational_value(base_set, value) {
        context.numeric_rational_values.insert(symbol_id, rational);
    }
    if let Some(representation) = exact_set_numeric_value(base_set, value) {
        context
            .numeric_representations
            .insert(symbol_id, representation);
    }
    if let Some(equality) = exact_set_numeric_equality(base_set, value) {
        context
            .numeric_representation_equalities
            .insert(symbol_id, equality);
    }
    if let Some(proof) = exact_set_numeric_proof(base_set, value) {
        context
            .numeric_representation_memberships
            .insert(symbol_id, proof);
    }
}

pub(in super::super) fn render_lean_source_for_target_set_representation(
    object: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match object {
        LeanTargetObjectRepresentation::Symbol { symbol_id, name } => context
            .symbol_names
            .get(symbol_id)
            .cloned()
            .ok_or_else(|| format!("unbound compiler set symbol `{name}`")),
        LeanTargetObjectRepresentation::StandardSet(set) => {
            render_lean_source_for_standard_set_representation(*set)
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => {
            let base =
                render_lean_source_for_target_set_representation(builder.set.as_ref(), context)?;
            let parameter = lean_identifier(&builder.name);
            let mut nested = context.clone();
            nested
                .symbol_names
                .insert(builder.symbol_id, parameter.clone());
            // A set-builder lambda binds the exact carrier of its base set.
            // Concrete predicates with exact parameters must consume that
            // value directly instead of searching for a heterogeneous
            // membership fact that the lambda does not need to carry.
            install_exact_set_builder_parameter_representation(
                builder.symbol_id,
                builder.set.as_ref(),
                &parameter,
                &mut nested,
            );
            let facts = builder
                .facts
                .iter()
                .map(|fact| render_fact(fact, &nested))
                .collect::<Result<Vec<_>, _>>()?;
            if facts.is_empty() {
                return Err("compiler set builder retained an empty predicate".into());
            }
            Ok(format!(
                "(Litex.setBuilder {base} (fun ({parameter} : {base}.Carrier) => {}))",
                conjunction(&facts)
            ))
        }
        LeanTargetObjectRepresentation::FunctionSet { function } => {
            render_function_set(function, context)
        }
        LeanTargetObjectRepresentation::FunctionRange { function } => {
            render_function_range(function, context)
        }
        LeanTargetObjectRepresentation::RealInterval {
            start,
            end,
            left_closed,
            right_closed,
        } => Ok(format!(
            "(Litex.realInterval {left_closed} {right_closed} {} {})",
            render_real_target_object_representation(start, context)?,
            render_real_target_object_representation(end, context)?,
        )),
        LeanTargetObjectRepresentation::RealRay {
            endpoint,
            closed,
            extends_right,
        } => Ok(format!(
            "(Litex.{} {closed} {})",
            if *extends_right {
                "realLeftRay"
            } else {
                "realRightRay"
            },
            render_real_target_object_representation(endpoint, context)?,
        )),
        other => Err(format!(
            "unsupported compiler function domain/codomain `{other:?}`"
        )),
    }
}

fn render_function_range(
    object: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let function_type = resolve_exact_function_range_type(object, context)?;
    match object {
        LeanTargetObjectRepresentation::AnonymousFunction(function) => {
            let value = render_anonymous_function(function, context)?;
            Ok(format!(
                "(Litex.{} {value})",
                if function_type.domain_facts.is_empty() {
                    "fnRangeOwn"
                } else {
                    "fnWhereRangeOwn"
                }
            ))
        }
        LeanTargetObjectRepresentation::Symbol { .. } => {
            let value = render_ir_symbol(object, context)?;
            Ok(format!(
                "(Litex.{} {value})",
                if function_type.domain_facts.is_empty() {
                    "fnRangeOwn"
                } else {
                    "fnWhereRangeOwn"
                }
            ))
        }
        other => Err(format!(
            "function-range target requires a named or anonymous function, found `{other:?}`"
        )),
    }
}

pub(in super::super) fn resolve_exact_function_range_type(
    object: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<LeanTargetFunctionTypeRepresentation, String> {
    let function = match object {
        LeanTargetObjectRepresentation::AnonymousFunction(function) => function.function.clone(),
        LeanTargetObjectRepresentation::Symbol { symbol_id, .. } => {
            let mut bindings = context
                .function_bindings
                .values()
                .filter(|binding| binding.symbol_id == *symbol_id)
                .collect::<Vec<_>>();
            bindings.sort_by_key(|binding| &binding.membership_proof_name);
            let Some(binding) = bindings.first().copied() else {
                return Err("function-range symbol has no Result-owned function binding".into());
            };
            if bindings.iter().any(|candidate| {
                candidate.function != binding.function || candidate.direct != binding.direct
            }) {
                return Err(
                    "function-range symbol has multiple representation-distinct bindings".into(),
                );
            }
            if !binding.direct {
                return Err(
                    "function-range target currently requires an exact function carrier".into(),
                );
            }
            binding.function.clone()
        }
        other => {
            return Err(format!(
                "function-range target requires a named or anonymous function, found `{other:?}`"
            ));
        }
    };
    if function_uses_telescope(&function) {
        return Err("function-range target does not yet support telescope functions".into());
    }
    if function.parameters.len() != 1 {
        return Err("function-range target currently requires one source parameter".into());
    }
    Ok(function)
}

pub(in super::super) fn render_real_set_observer(
    set: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
    value: &str,
) -> Result<String, String> {
    match set {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
            Ok(format!("({value} : ℝ)"))
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => render_real_set_observer(
            builder.set.as_ref(),
            context,
            &format!("({value}).val"),
        ),
        LeanTargetObjectRepresentation::FunctionRange { function } => {
            let function_type = resolve_exact_function_range_type(function, context)?;
            render_real_set_observer(
                function_type.return_set.as_ref(),
                context,
                &format!("({value}).val"),
            )
        }
        LeanTargetObjectRepresentation::RealInterval { .. }
        | LeanTargetObjectRepresentation::RealRay { .. } => {
            Ok(format!("(({value}).val : ℝ)"))
        }
        other => Err(format!(
            "target set `{other:?}` has no registered native-real carrier observation"
        )),
    }
}

pub(in super::super) fn render_real_set_observer_same(
    set: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
    value: &str,
) -> Result<String, String> {
    match set {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
            Ok(format!("Litex.Same.refl {value}"))
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => Ok(format!(
            "Litex.Same.trans (Litex.Same.subtype {value}) ({})",
            render_real_set_observer_same(builder.set.as_ref(), context, &format!("({value}).val"))?
        )),
        LeanTargetObjectRepresentation::FunctionRange { function } => {
            let function_type = resolve_exact_function_range_type(function, context)?;
            Ok(format!(
                "Litex.Same.trans (Litex.Same.subtype {value}) ({})",
                render_real_set_observer_same(
                    function_type.return_set.as_ref(),
                    context,
                    &format!("({value}).val"),
                )?
            ))
        }
        LeanTargetObjectRepresentation::RealInterval { .. }
        | LeanTargetObjectRepresentation::RealRay { .. } => {
            Ok(format!("Litex.Same.subtype {value}"))
        }
        other => Err(format!(
            "target set `{other:?}` has no registered native-real semantic bridge"
        )),
    }
}
