//! Atomic, composite, quantified, and order fact rendering.

use super::super::*;

fn render_same_fact(
    left: &Obj,
    right: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let rendered_left = render_obj(left, context)?;
    let rendered_right = render_obj(right, context)?;
    if let Some(opaque_type) = opaque_object_type_annotation(left, context)
        .or_else(|| opaque_object_type_annotation(right, context))
    {
        return Ok(format!(
            "@Litex.Same ({opaque_type}) ({opaque_type}) (Litex.ComplexObserver.none _) (Litex.ComplexObserver.none _) {rendered_left} {rendered_right}"
        ));
    }
    if object_has_only_default_observer(left, context)
        || object_has_only_default_observer(right, context)
        || rendered_left.contains("fnTelescope")
        || rendered_right.contains("fnTelescope")
        || rendered_left.contains("setBuilder")
        || rendered_right.contains("setBuilder")
    {
        // Opaque exact carriers (notably a set-builder or a telescope result)
        // deliberately carry no native observation.  Equality and
        // non-equality must share this same observer choice: a contradiction
        // proof negates the rendered equality proposition rather than
        // changing its observer index.
        Ok(format!(
            "@Litex.Same _ _ (Litex.ComplexObserver.none _) (Litex.ComplexObserver.none _) {rendered_left} {rendered_right}"
        ))
    } else {
        Ok(format!("Litex.Same {rendered_left} {rendered_right}"))
    }
}

pub(in super::super) fn render_fact(
    fact: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match fact {
        Fact::AtomicFact(atomic) => match atomic {
            AtomicFact::NormalAtomicFact(fact) => {
                let source_name = fact.predicate.to_string();
                if source_name == PRIME && fact.body.len() == 1 {
                    return Ok(format!(
                        "Litex.Prime {}",
                        render_obj(&fact.body[0], context)?
                    ));
                }
                if source_name == COPRIME && fact.body.len() == 2 {
                    return Ok(format!(
                        "Litex.Coprime {} {}",
                        render_obj(&fact.body[0], context)?,
                        render_obj(&fact.body[1], context)?
                    ));
                }
                if source_name == IS_REAL_LEAST_UPPER_BOUND && fact.body.len() == 2 {
                    return Ok(format!(
                        "Litex.RealLeastUpperBound {} {}",
                        render_obj(&fact.body[0], context)?,
                        render_obj(&fact.body[1], context)?
                    ));
                }
                if source_name == IS_REAL_GREATEST_LOWER_BOUND && fact.body.len() == 2 {
                    return Ok(format!(
                        "Litex.RealGreatestLowerBound {} {}",
                        render_obj(&fact.body[0], context)?,
                        render_obj(&fact.body[1], context)?
                    ));
                }
                let binding = context
                    .predicate_bindings
                    .get(&source_name)
                    .ok_or_else(|| format!("unavailable concrete predicate `{source_name}`"))?;
                if fact.body.len() != binding.parameter_count {
                    return Err(format!(
                        "predicate `{source_name}` expected {} arguments, retained {}",
                        binding.parameter_count,
                        fact.body.len()
                    ));
                }
                let arguments = fact
                    .body
                    .iter()
                    .enumerate()
                    .map(|(argument_index, argument)| {
                        render_concrete_predicate_argument(
                            binding,
                            argument_index,
                            argument,
                            context,
                        )
                        .map_err(|error| {
                            format!(
                                "predicate `{source_name}` argument {argument_index} (`{argument}`) failed: {error}"
                            )
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(format!("{} {}", binding.lean_name, arguments.join(" ")))
            }
            AtomicFact::NotNormalAtomicFact(fact) => {
                let source_name = fact.predicate.to_string();
                if source_name == PRIME && fact.body.len() == 1 {
                    return Ok(format!(
                        "¬ Litex.Prime {}",
                        render_obj(&fact.body[0], context)?
                    ));
                }
                if source_name == COPRIME && fact.body.len() == 2 {
                    return Ok(format!(
                        "¬ Litex.Coprime {} {}",
                        render_obj(&fact.body[0], context)?,
                        render_obj(&fact.body[1], context)?
                    ));
                }
                if source_name == IS_REAL_LEAST_UPPER_BOUND && fact.body.len() == 2 {
                    return Ok(format!(
                        "¬ Litex.RealLeastUpperBound {} {}",
                        render_obj(&fact.body[0], context)?,
                        render_obj(&fact.body[1], context)?
                    ));
                }
                if source_name == IS_REAL_GREATEST_LOWER_BOUND && fact.body.len() == 2 {
                    return Ok(format!(
                        "¬ Litex.RealGreatestLowerBound {} {}",
                        render_obj(&fact.body[0], context)?,
                        render_obj(&fact.body[1], context)?
                    ));
                }
                let binding = context
                    .predicate_bindings
                    .get(&source_name)
                    .ok_or_else(|| format!("unavailable concrete predicate `{source_name}`"))?;
                if fact.body.len() != binding.parameter_count {
                    return Err(format!(
                        "predicate `{source_name}` expected {} arguments, retained {}",
                        binding.parameter_count,
                        fact.body.len()
                    ));
                }
                let arguments = fact
                    .body
                    .iter()
                    .enumerate()
                    .map(|(argument_index, argument)| {
                        render_concrete_predicate_argument(
                            binding,
                            argument_index,
                            argument,
                            context,
                        )
                        .map_err(|error| {
                            format!(
                                "negated predicate `{source_name}` argument {argument_index} (`{argument}`) failed: {error}"
                            )
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(format!("¬ {} {}", binding.lean_name, arguments.join(" ")))
            }
            AtomicFact::InFact(fact) => Ok(format!(
                "Litex.In {} {}",
                render_obj(&fact.element, context)?,
                render_obj(&fact.set, context)?
            )),
            AtomicFact::NotInFact(fact) => Ok(format!(
                "¬ Litex.In {} {}",
                render_obj(&fact.element, context)?,
                render_obj(&fact.set, context)?
            )),
            AtomicFact::SubsetFact(fact) => Ok(format!(
                "Litex.Subset {} {}",
                render_obj(&fact.left, context)?,
                render_obj(&fact.right, context)?
            )),
            AtomicFact::SupersetFact(fact) => Ok(format!(
                "Litex.Subset {} {}",
                render_obj(&fact.right, context)?,
                render_obj(&fact.left, context)?
            )),
            AtomicFact::NotSubsetFact(fact) => Ok(format!(
                "¬ Litex.Subset {} {}",
                render_obj(&fact.left, context)?,
                render_obj(&fact.right, context)?
            )),
            AtomicFact::NotSupersetFact(fact) => Ok(format!(
                "¬ Litex.Subset {} {}",
                render_obj(&fact.right, context)?,
                render_obj(&fact.left, context)?
            )),
            AtomicFact::EqualFact(fact) => render_same_fact(&fact.left, &fact.right, context),
            AtomicFact::NotEqualFact(fact) => {
                let left = render_obj(&fact.left, context)?;
                let right = render_obj(&fact.right, context)?;
                // Non-equality is consumed by the generic nonzero/refined-set
                // rules through their representation-invariant, unobserved
                // `Same` index.  A contradiction against an observed equality
                // renders its local reverse type from that equality instead
                // of changing this global NotEqual ABI.
                Ok(format!(
                    "¬ @Litex.Same _ _ (Litex.ComplexObserver.none _) (Litex.ComplexObserver.none _) {left} {right}"
                ))
            }
            AtomicFact::LessFact(fact) => render_order_fact(&fact.left, &fact.right, true, context),
            AtomicFact::GreaterFact(fact) => {
                render_order_fact(&fact.right, &fact.left, true, context)
            }
            AtomicFact::LessEqualFact(fact) => {
                render_order_fact(&fact.left, &fact.right, false, context)
            }
            AtomicFact::GreaterEqualFact(fact) => {
                render_order_fact(&fact.right, &fact.left, false, context)
            }
            AtomicFact::NotLessFact(fact) => Ok(format!(
                "¬ {}",
                render_order_fact(&fact.left, &fact.right, true, context)?
            )),
            AtomicFact::NotGreaterFact(fact) => Ok(format!(
                "¬ {}",
                render_order_fact(&fact.right, &fact.left, true, context)?
            )),
            AtomicFact::NotLessEqualFact(fact) => Ok(format!(
                "¬ {}",
                render_order_fact(&fact.left, &fact.right, false, context)?
            )),
            AtomicFact::NotGreaterEqualFact(fact) => Ok(format!(
                "¬ {}",
                render_order_fact(&fact.right, &fact.left, false, context)?
            )),
            AtomicFact::IsNonemptySetFact(fact) => Ok(format!(
                "Litex.Set.Nonempty {}",
                render_obj(&fact.set, context)?
            )),
            AtomicFact::IsFiniteSetFact(fact) => Ok(format!(
                "Litex.Set.Finite {}",
                render_obj(&fact.set, context)?
            )),
            // A Litex set parameter is represented as a Lean value whose type
            // is already `Litex.Set`; its explicit source-level sethood check
            // therefore lowers to the proposition `True`.
            AtomicFact::IsSetFact(_) => Ok("True".to_string()),
            AtomicFact::NotIsSetFact(_) => Ok("¬ True".to_string()),
            AtomicFact::IsTupleFact(fact) => {
                Ok(format!("Litex.IsTuple {}", render_obj(&fact.set, context)?))
            }
            _ => Err(format!("unsupported compiler atomic fact `{fact}`")),
        },
        Fact::AndFact(_) | Fact::ChainFact(_) => {
            let components = conjunction_components(&Runtime::default(), fact)?;
            let rendered = components
                .iter()
                .map(|component| render_fact(component, context))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(conjunction(&rendered))
        }
        Fact::OrFact(_) => {
            let branches = disjunction_components(fact)?;
            let rendered = branches
                .iter()
                .map(|branch| render_fact(branch, context))
                .collect::<Result<Vec<_>, _>>()?;
            if rendered.is_empty() {
                return Err("compiler disjunction retained no branches".into());
            }
            Ok(rendered.join(" ∨ "))
        }
        Fact::ExistFact(existential) => render_existential_fact(existential, context),
        Fact::ForallFact(forall) => render_forall_fact_type(forall, context),
        _ => Err(format!("unsupported compiler fact `{fact}`")),
    }
}

/// Return an explicit Lean type for an opaque function value when inference
/// cannot recover the dependent telescope carrier from the term alone.  This
/// occurs for a quantified parameter whose type is a `fnTelescopeSet`: the
/// source binder fixes the type, but `@Same _ _ ...` is elaborated before the
/// proof body and leaves the telescope's dependent universe metavariables
/// unresolved.
fn opaque_object_type_annotation(
    object: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Option<String> {
    let Obj::Atom(atom) = object else {
        return None;
    };
    let symbol_id = atom.symbol_ref().map(SymbolRef::id)?;
    let binding = context
        .function_bindings
        .values()
        .find(|binding| binding.symbol_id == symbol_id)?;
    if !(function_uses_telescope(&binding.function)
        || matches!(
            binding.function.return_set.as_ref(),
            LeanTargetObjectRepresentation::SetBuilder(_)
                | LeanTargetObjectRepresentation::FunctionSet { .. }
                | LeanTargetObjectRepresentation::FunctionRange { .. }
                | LeanTargetObjectRepresentation::RealInterval { .. }
                | LeanTargetObjectRepresentation::RealRay { .. }
        ))
    {
        return None;
    }
    render_function_type(&binding.function, context).ok()
}

pub(in super::super) fn render_order_fact(
    left: &Obj,
    right: &Obj,
    strict: bool,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let uses_transportable_builder_sign = |object: &Obj| -> bool {
        matches!(
            LeanTargetObjectRepresentation::lower(object),
            Ok(LeanTargetObjectRepresentation::Symbol { symbol_id, .. })
                if context.semantic_zero_ended_order_symbols.contains(&symbol_id)
        )
    };
    if left.to_string() == "0" && uses_transportable_builder_sign(right) {
        return Ok(format!(
            "{} {}",
            if strict {
                "Litex.Positive"
            } else {
                "Litex.Nonnegative"
            },
            render_obj(right, context)?
        ));
    }
    if right.to_string() == "0" && uses_transportable_builder_sign(left) {
        return Ok(format!(
            "{} {}",
            if strict {
                "Litex.Negative"
            } else {
                "Litex.Nonpositive"
            },
            render_obj(left, context)?
        ));
    }
    let exact_selected_real = |object: &Obj| -> Option<String> {
        let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
            LeanTargetObjectRepresentation::lower(object).ok()?
        else {
            return None;
        };
        context.numeric_real_values.get(&symbol_id)?;
        context.numeric_representations.get(&symbol_id).cloned()
    };
    let exact_integer_endpoint = |object: &Obj| -> bool {
        if !matches!(
            LeanTargetObjectRepresentation::lower(object),
            Ok(LeanTargetObjectRepresentation::Symbol { .. })
        ) {
            return false;
        }
        let Ok(source) = render_obj(object, context) else {
            return false;
        };
        let Ok(integer) = render_integer_obj(object, context) else {
            return false;
        };
        source == integer
    };
    if left.to_string() == "0" {
        if let Some(right) = exact_selected_real(right) {
            return Ok(format!(
                "{} (0 : ℂ) {right}",
                if strict { "Litex.Lt" } else { "Litex.Le" }
            ));
        }
    }
    if right.to_string() == "0" {
        if let Some(left) = exact_selected_real(left) {
            return Ok(format!(
                "{} {left} (0 : ℂ)",
                if strict { "Litex.Lt" } else { "Litex.Le" }
            ));
        }
    }
    if left.to_string() == "0" && !exact_integer_endpoint(right) {
        let predicate = if strict {
            "Litex.Positive"
        } else {
            "Litex.Nonnegative"
        };
        return Ok(format!("{predicate} {}", render_obj(right, context)?));
    }
    if right.to_string() == "0" && !exact_integer_endpoint(left) {
        let predicate = if strict {
            "Litex.Negative"
        } else {
            "Litex.Nonpositive"
        };
        return Ok(format!("{predicate} {}", render_obj(left, context)?));
    }
    let predicate = if strict { "Litex.Lt" } else { "Litex.Le" };
    Ok(format!(
        "{predicate} {} {}",
        render_numeric_obj(left, context)?,
        render_numeric_obj(right, context)?
    ))
}

/// Whether an object is carried by a target type for which the compiler has
/// no reviewed native observation.  `Litex.Set.Carrier` is intentionally
/// opaque, so a set-builder/telescope result must be compared under the
/// explicit no-observation `Same` ABI.
fn object_has_only_default_observer(
    object: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> bool {
    if let Obj::Atom(atom) = object {
        if let Some(symbol_id) = atom.symbol_ref().map(SymbolRef::id) {
            if context.opaque_carrier_symbols.contains(&symbol_id)
                && !context.observed_carrier_symbols.contains(&symbol_id)
            {
                return true;
            }
            if context.function_bindings.values().any(|binding| {
                binding.symbol_id == symbol_id
                    && (function_uses_telescope(&binding.function)
                        || matches!(
                            binding.function.return_set.as_ref(),
                            LeanTargetObjectRepresentation::SetBuilder(_)
                                | LeanTargetObjectRepresentation::FunctionSet { .. }
                                | LeanTargetObjectRepresentation::FunctionRange { .. }
                                | LeanTargetObjectRepresentation::RealInterval { .. }
                                | LeanTargetObjectRepresentation::RealRay { .. }
                        ))
            }) {
                return true;
            }
        }
    }
    if let Obj::FnObj(application) = object {
        let symbol_id = match application.head.as_ref() {
            FnObjHead::Identifier(identifier) => identifier.symbol.as_ref().map(SymbolRef::id),
            FnObjHead::IdentifierWithMod(identifier) => {
                identifier.symbol.as_ref().map(SymbolRef::id)
            }
            FnObjHead::Bound(parameter) => Some(parameter.symbol.id()),
            _ => None,
        };
        if let Some(symbol_id) = symbol_id {
            if context
                .function_bindings
                .values()
                .find(|binding| binding.symbol_id == symbol_id)
                .is_some_and(|binding| {
                    matches!(
                        binding.function.return_set.as_ref(),
                        LeanTargetObjectRepresentation::SetBuilder(_)
                            | LeanTargetObjectRepresentation::FunctionSet { .. }
                            | LeanTargetObjectRepresentation::FunctionRange { .. }
                            | LeanTargetObjectRepresentation::RealInterval { .. }
                            | LeanTargetObjectRepresentation::RealRay { .. }
                    )
                })
            {
                return true;
            }
        }
    }
    let Ok(lowered) = LeanTargetObjectRepresentation::lower(object) else {
        return false;
    };
    match lowered {
        LeanTargetObjectRepresentation::SetBuilder(_)
        | LeanTargetObjectRepresentation::FunctionSet { .. }
        | LeanTargetObjectRepresentation::FunctionRange { .. }
        | LeanTargetObjectRepresentation::RealInterval { .. }
        | LeanTargetObjectRepresentation::RealRay { .. } => true,
        LeanTargetObjectRepresentation::FunctionApplication(application) => {
            function_application_return_set_from_result(&application, context)
                .map(|set| {
                    matches!(
                        set,
                        LeanTargetObjectRepresentation::SetBuilder(_)
                            | LeanTargetObjectRepresentation::FunctionSet { .. }
                            | LeanTargetObjectRepresentation::FunctionRange { .. }
                            | LeanTargetObjectRepresentation::RealInterval { .. }
                            | LeanTargetObjectRepresentation::RealRay { .. }
                    )
                })
                .unwrap_or(false)
        }
        _ => false,
    }
}
