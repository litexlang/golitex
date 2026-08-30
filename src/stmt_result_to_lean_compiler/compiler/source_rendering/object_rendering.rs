//! General objects and their Lean target representations.

use super::super::*;

pub(in super::super) fn render_obj(
    obj: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match obj {
        Obj::Atom(AtomObj::Bound(parameter)) => context
            .symbol_names
            .get(&parameter.symbol.id())
            .cloned()
            .or_else(|| context.existential_names.get(parameter.name()).cloned())
            .ok_or_else(|| format!("unbound compiler symbol `{obj}`")),
        Obj::Atom(AtomObj::Identifier(identifier)) => identifier
            .symbol
            .as_ref()
            .and_then(|symbol| context.symbol_names.get(&symbol.id()))
            .cloned()
            .ok_or_else(|| format!("unbound compiler symbol `{obj}`")),
        Obj::Atom(atom) => atom
            .symbol_ref()
            .and_then(|symbol| context.symbol_names.get(&symbol.id()))
            .cloned()
            .ok_or_else(|| format!("unbound compiler symbol `{obj}`")),
        Obj::Number(number) => render_normalized_complex_number(&number.normalized_value),
        Obj::ImaginaryUnit(_) => Ok("Complex.I".into()),
        Obj::EulerNumber(_) => Ok("((Real.exp 1 : ℝ) : ℂ)".into()),
        Obj::Pi(_) => Ok("((Real.pi : ℝ) : ℂ)".into()),
        Obj::Add(addition) => Ok(format!(
            "({} + {})",
            render_numeric_obj(addition.left.as_ref(), context)?,
            render_numeric_obj(addition.right.as_ref(), context)?
        )),
        Obj::Sub(subtraction) => Ok(format!(
            "({} - {})",
            render_numeric_obj(subtraction.left.as_ref(), context)?,
            render_numeric_obj(subtraction.right.as_ref(), context)?
        )),
        Obj::Mul(multiplication) => Ok(format!(
            "({} * {})",
            render_numeric_obj(multiplication.left.as_ref(), context)?,
            render_numeric_obj(multiplication.right.as_ref(), context)?
        )),
        Obj::Div(division) => Ok(format!(
            "({} / {})",
            render_numeric_obj(division.left.as_ref(), context)?,
            render_numeric_obj(division.right.as_ref(), context)?
        )),
        Obj::Abs(operation) => Ok(format!(
            "(Litex.abs {})",
            render_numeric_obj(operation.arg.as_ref(), context)?
        )),
        Obj::Mod(remainder) => Ok(format!(
            "(({} % {} : ℤ) : ℂ)",
            render_integer_obj(remainder.left.as_ref(), context)?,
            render_integer_obj(remainder.right.as_ref(), context)?
        )),
        Obj::Pow(power) => render_numeric_power(power, context),
        Obj::FnSet(function_set) => {
            let function = LeanTargetFunctionTypeRepresentation::lower(function_set)?;
            render_function_set(&function, context)
        }
        Obj::SetBuilder(_) => {
            let lowered = LeanTargetObjectRepresentation::lower(obj)?;
            render_lean_source_for_target_set_representation(&lowered, context)
        }
        Obj::AnonymousFn(_) => {
            let LeanTargetObjectRepresentation::AnonymousFunction(function) =
                LeanTargetObjectRepresentation::lower(obj)?
            else {
                return Err("anonymous function lowered to another object".into());
            };
            render_anonymous_function(&function, context)
        }
        Obj::FnObj(application) => {
            let mut source: Obj = application.clone().into();
            if application.source_occurrence_id.is_none() {
                let alpha_display = source_display_without_symbol_ids(&source.to_string());
                let result_context = context.well_definedness.as_ref().ok_or_else(|| {
                    format!(
                        "synthesized application `{source}` has no active Result-owned WD context"
                    )
                })?;
                let mut matching = result_context
                    .function_applications
                    .values()
                    .filter(|candidate| {
                        objs_equal_with_nested_binder_alpha_equivalence(
                            &candidate.source_application,
                            &source,
                        ) || source_display_without_symbol_ids(
                            &candidate.source_application.to_string(),
                        ) == alpha_display
                    })
                    .collect::<Vec<_>>();
                matching.sort_by_key(|candidate| match &candidate.source_application {
                    Obj::FnObj(application) => application
                        .source_occurrence_id
                        .map(|occurrence| occurrence.value())
                        .unwrap_or_default(),
                    _ => 0,
                });
                let Some(first) = matching.first().copied() else {
                    let available = result_context
                        .function_applications
                        .values()
                        .map(|candidate| candidate.source_application.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    return Err(format!(
                        "synthesized application `{source}` has no structurally matching Result-owned occurrence; active applications: [{available}]"
                    ));
                };
                let expected_certificate = function_application_result_certificate_key(first);
                if matching.iter().any(|candidate| {
                    function_application_result_certificate_key(candidate) != expected_certificate
                }) {
                    return Err(format!(
                        "synthesized application `{source}` has evidence-distinct matching Result-owned occurrences"
                    ));
                }
                let Obj::FnObj(source_application) = &mut source else {
                    unreachable!("FnObj branch retained a non-application object")
                };
                let Obj::FnObj(certified_application) = &first.source_application else {
                    return Err(
                        "Result-owned function application certificate retained a non-application"
                            .into(),
                    );
                };
                // Keep the synthesized application's current binder symbols.  The
                // Result-owned occurrence contributes identity/evidence only; copying
                // the whole certified source here would reintroduce the fresh binder
                // symbols from the verifier's alpha-equivalent replay and make them
                // unbound in the current Lean lambda/forall scope.
                source_application.source_occurrence_id =
                    certified_application.source_occurrence_id;
            }
            let LeanTargetObjectRepresentation::FunctionApplication(application) =
                LeanTargetObjectRepresentation::lower(&source)?
            else {
                return Err("function application lowered to a non-application object".into());
            };
            render_function_application(&application, context)
        }
        Obj::InstantiatedTemplateObj(application) => {
            if let Some(rendered) = context.symbol_names.get(&application.symbol.id()) {
                return Ok(rendered.clone());
            }
            let binding = context
                .template_set_alias_bindings
                .get(&application.template_name.to_string())
                .ok_or_else(|| format!("unbound compiler Template application `{obj}`"))?;
            if application.args.len() != binding.parameter_count {
                return Err(format!(
                    "Template application `{obj}` changed its compiled argument count"
                ));
            }
            let arguments = application
                .args
                .iter()
                .map(|argument| render_obj(argument, context))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(format!("({} {})", binding.lean_name, arguments.join(" ")))
        }
        Obj::StandardSet(set) => render_standard_set(*set).map(str::to_string),
        _ => render_lean_source_for_target_object_representation(
            &LeanTargetObjectRepresentation::lower(obj)?,
            context,
        ),
    }
}

pub(in super::super) fn render_ir_symbol(
    object: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let LeanTargetObjectRepresentation::Symbol { symbol_id, name } = object else {
        return Err("expected a compiler symbol".into());
    };
    context
        .symbol_names
        .get(symbol_id)
        .cloned()
        .ok_or_else(|| format!("unbound compiler symbol `{name}`"))
}

pub(in super::super) fn render_lean_source_for_native_target_object_representation(
    object: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    render_lean_source_for_target_object_representation(object, context)
}

pub(in super::super) fn render_lean_source_for_target_object_representation(
    object: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match object {
        LeanTargetObjectRepresentation::Symbol { .. } => render_ir_symbol(object, context),
        LeanTargetObjectRepresentation::Number { normalized_value } => {
            render_normalized_complex_number(normalized_value)
        }
        LeanTargetObjectRepresentation::Constant(constant) => Ok(match constant {
            LeanTargetConstantObject::ImaginaryUnit => "Complex.I".into(),
            LeanTargetConstantObject::EulerNumber => "((Real.exp 1 : ℝ) : ℂ)".into(),
            LeanTargetConstantObject::Pi => "((Real.pi : ℝ) : ℂ)".into(),
        }),
        LeanTargetObjectRepresentation::StandardSet(set) => {
            render_lean_source_for_standard_set_representation(*set)
        }
        LeanTargetObjectRepresentation::FunctionSet { function } => {
            render_function_set(function, context)
        }
        LeanTargetObjectRepresentation::SetBuilder(_) => {
            render_lean_source_for_target_set_representation(object, context)
        }
        LeanTargetObjectRepresentation::AnonymousFunction(function) => {
            render_anonymous_function(function, context)
        }
        LeanTargetObjectRepresentation::FunctionApplication(application) => {
            render_function_application(application, context)
        }
        LeanTargetObjectRepresentation::FunctionRange { .. }
        | LeanTargetObjectRepresentation::RealInterval { .. }
        | LeanTargetObjectRepresentation::RealRay { .. } => {
            render_lean_source_for_target_set_representation(object, context)
        }
        LeanTargetObjectRepresentation::Range { start, end } => Ok(format!(
            "(Litex.range {} {})",
            render_integer_endpoint(start, context)?,
            render_integer_endpoint(end, context)?
        )),
        LeanTargetObjectRepresentation::ClosedRange { start, end } => Ok(format!(
            "(Litex.closedRange {} {})",
            render_integer_endpoint(start, context)?,
            render_integer_endpoint(end, context)?
        )),
        LeanTargetObjectRepresentation::GeneralCartesianProduct {
            index_set,
            family_set,
            family_function,
        } => Ok(format!(
            "(Litex.generalCart {} {} {})",
            render_lean_source_for_target_object_representation(index_set, context)?,
            render_lean_source_for_target_object_representation(family_set, context)?,
            render_lean_source_for_target_object_representation(family_function, context)?
        )),
        LeanTargetObjectRepresentation::SequenceSet { values, length } => match length {
            Some(length) => Ok(format!(
                "(Litex.finiteSequenceSet.{{0}} {} {})",
                render_lean_source_for_target_set_representation(values, context)?,
                render_natural_endpoint(length)?
            )),
            None => Ok(format!(
                "(Litex.sequenceSet {})",
                render_lean_source_for_target_set_representation(values, context)?
            )),
        },
        LeanTargetObjectRepresentation::MatrixSet {
            values,
            row_count,
            column_count,
        } => Ok(format!(
            "(Litex.matrixSet.{{0}} {} {} {})",
            render_lean_source_for_target_set_representation(values, context)?,
            render_natural_endpoint(row_count)?,
            render_natural_endpoint(column_count)?,
        )),
        LeanTargetObjectRepresentation::CartesianProduct { factors } => {
            let mut rendered = "Litex.cartNil".to_string();
            for factor in factors.iter().rev() {
                rendered = format!(
                    "(Litex.cartCons {} {rendered})",
                    render_lean_source_for_target_set_representation(factor, context)?
                );
            }
            Ok(rendered)
        }
        LeanTargetObjectRepresentation::Aggregate {
            source_occurrence_id,
            semantic_key,
            kind,
            arguments,
        } => render_aggregate_object(
            *source_occurrence_id,
            semantic_key,
            *kind,
            arguments,
            context,
        ),
        LeanTargetObjectRepresentation::TupleDimension(tuple) => Ok(format!(
            "(Litex.tupleDim {})",
            render_lean_source_for_target_object_representation(tuple, context)?
        )),
        LeanTargetObjectRepresentation::IndexedAccess { object, index } => {
            render_literal_indexed_access(object, index, context)
        }
        LeanTargetObjectRepresentation::BuiltinApp {
            operator,
            arguments,
            ..
        } => render_builtin_object(*operator, arguments, context),
        LeanTargetObjectRepresentation::Collection {
            constructor: LeanTargetCollectionObjectConstructor::Tuple,
            items,
            ..
        } => render_typed_spine(items, context),
        LeanTargetObjectRepresentation::Collection {
            constructor: LeanTargetCollectionObjectConstructor::SequenceLiteral,
            items,
            ..
        } => Ok(format!(
            "(Litex.SequenceLiteral.mk {})",
            render_typed_spine(items, context)?
        )),
        LeanTargetObjectRepresentation::Collection {
            constructor: LeanTargetCollectionObjectConstructor::ListSet,
            items,
            ..
        } => render_list_set(items, context),
    }
}
