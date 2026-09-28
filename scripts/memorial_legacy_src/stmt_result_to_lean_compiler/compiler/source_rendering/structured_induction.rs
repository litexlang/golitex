//! Structured induction symbols, target representations, and substitution matching.

use super::super::*;

pub(in super::super) fn install_structured_induction_shape_symbol(
    symbol_id: SymbolId,
    rendered: &str,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) {
    let rendered = rendered.to_string();
    context.symbol_names.insert(symbol_id, rendered.clone());
    context
        .numeric_representations
        .insert(symbol_id, rendered.clone());
    context
        .numeric_integer_values
        .insert(symbol_id, rendered.clone());
    context
        .numeric_rational_values
        .insert(symbol_id, rendered.clone());
    context.numeric_real_values.insert(symbol_id, rendered);
}

pub(in super::super) fn install_structured_induction_native_integer_symbol(
    symbol_id: SymbolId,
    native_integer: &str,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) {
    let complex = format!("((({native_integer}) : ℂ))");
    context
        .symbol_names
        .insert(symbol_id, native_integer.to_string());
    context.numeric_representations.insert(symbol_id, complex);
    context
        .numeric_integer_values
        .insert(symbol_id, native_integer.to_string());
    context
        .numeric_rational_values
        .insert(symbol_id, format!("((({native_integer}) : ℚ))"));
    context
        .numeric_real_values
        .insert(symbol_id, format!("((({native_integer}) : ℝ))"));
    // This binder is already the exact `Z.Carrier` (`ℤ`).  Do not leave the
    // generic heterogeneous-membership representative installed by
    // `install_parameter_fact_aliases`: its arbitrary `In.rep` term is only
    // propositionally related to the native binder and therefore cannot feed
    // a closure theorem whose operands are the exact complex casts rendered
    // above.
    context.numeric_representation_equalities.insert(
        symbol_id,
        format!("Litex.Same.intComplex ({native_integer})"),
    );
    context.numeric_representation_memberships.insert(
        symbol_id,
        format!("Litex.Rules.complexIntInZ ({native_integer})"),
    );
}

/// A structured induction Result owns two binder identities for one logical
/// value: the parameter named by the source `by induc` statement and the fresh
/// parameter owned by the generated forall fact.  Result validation proves
/// that the generated forall is exactly the source goal under that rebinding;
/// Lean replay must therefore install both verified identities as aliases for
/// the same native integer.
pub(in super::super) fn install_verified_structured_induction_binder_aliases(
    verification: &SuccessVerifyByInducResult,
    native_integer: &str,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let generated_parameters = verification
        .generated_forall
        .typed_parameters
        .collect_param_bindings_with_types();
    let [(generated_binding, generated_type)] = generated_parameters.as_slice() else {
        return Err("structured induction generated forall must own one parameter".into());
    };
    if generated_type.to_string() != ParamType::Obj(StandardSet::Z.into()).to_string() {
        return Err("structured induction generated forall changed its integer binder".into());
    }
    install_structured_induction_native_integer_symbol(
        verification.parameter_binding.id(),
        native_integer,
        context,
    );
    install_structured_induction_native_integer_symbol(
        generated_binding.id(),
        native_integer,
        context,
    );
    Ok(())
}

/// Render the exact native real selected by verifier-owned membership
/// evidence. This is intentionally narrower than ordinary object rendering:
/// callers use it only for target rules whose Lean theorem is stated over the
/// exact `R.Carrier`, never as a fallback conversion from `Same`.
pub(in super::super) fn render_real_target_object_representation(
    object: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match object {
        LeanTargetObjectRepresentation::Symbol { symbol_id, name } => context
            .numeric_real_values
            .get(symbol_id)
            .cloned()
            .ok_or_else(|| format!("real target symbol `{name}` has no exact ℝ representation")),
        LeanTargetObjectRepresentation::Number { normalized_value } => {
            Ok(format!("({normalized_value} : ℝ)"))
        }
        LeanTargetObjectRepresentation::BuiltinApp {
            operator,
            arguments,
            ..
        } if arguments.len() == 2
            && matches!(
                operator,
                LeanTargetBuiltinObjectOperator::Add
                    | LeanTargetBuiltinObjectOperator::Sub
                    | LeanTargetBuiltinObjectOperator::Mul
                    | LeanTargetBuiltinObjectOperator::Div
                    | LeanTargetBuiltinObjectOperator::Min
                    | LeanTargetBuiltinObjectOperator::Max
            ) =>
        {
            let left = render_real_target_object_representation(&arguments[0], context)?;
            let right = render_real_target_object_representation(&arguments[1], context)?;
            match operator {
                LeanTargetBuiltinObjectOperator::Min => Ok(format!("(min {left} {right})")),
                LeanTargetBuiltinObjectOperator::Max => Ok(format!("(max {left} {right})")),
                LeanTargetBuiltinObjectOperator::Add
                | LeanTargetBuiltinObjectOperator::Sub
                | LeanTargetBuiltinObjectOperator::Mul
                | LeanTargetBuiltinObjectOperator::Div => {
                    let symbol = match operator {
                        LeanTargetBuiltinObjectOperator::Add => "+",
                        LeanTargetBuiltinObjectOperator::Sub => "-",
                        LeanTargetBuiltinObjectOperator::Mul => "*",
                        LeanTargetBuiltinObjectOperator::Div => "/",
                        _ => unreachable!("guarded real infix operator"),
                    };
                    Ok(format!("({left} {symbol} {right})"))
                }
                _ => unreachable!("guarded real binary operator"),
            }
        }
        LeanTargetObjectRepresentation::BuiltinApp {
            operator: LeanTargetBuiltinObjectOperator::Abs,
            arguments,
            ..
        } if arguments.len() == 1 => Ok(format!(
            "|{}|",
            render_real_target_object_representation(&arguments[0], context)?
        )),
        LeanTargetObjectRepresentation::FunctionApplication(application) => {
            let return_set = function_application_return_set_from_result(application, context)?;
            if return_set
                != LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real)
            {
                return Err(
                    "function application has no verifier-owned exact R return carrier".into(),
                );
            }
            render_function_application(application, context)
        }
        _ => Err(format!(
            "target object `{object:?}` has no reviewed exact ℝ representation"
        )),
    }
}

/// Render a checked source object at the exact native real carrier.  Most
/// objects lower directly to the target IR. Definition replay may synthesize
/// an equivalent application shape, so the source-shaped fallback resolves
/// its semantic object key against the active Result certificate and then
/// recurses compositionally through ordinary real arithmetic.
pub(in super::super) fn render_real_source_object(
    object: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let Ok(lowered) = LeanTargetObjectRepresentation::lower(object) {
        if let Ok(rendered) = render_real_target_object_representation(&lowered, context) {
            return Ok(rendered);
        }
    }
    match object {
        Obj::Add(operation) => Ok(format!(
            "({} + {})",
            render_real_source_object(operation.left.as_ref(), context)?,
            render_real_source_object(operation.right.as_ref(), context)?,
        )),
        Obj::Sub(operation) => Ok(format!(
            "({} - {})",
            render_real_source_object(operation.left.as_ref(), context)?,
            render_real_source_object(operation.right.as_ref(), context)?,
        )),
        Obj::Mul(operation) => Ok(format!(
            "({} * {})",
            render_real_source_object(operation.left.as_ref(), context)?,
            render_real_source_object(operation.right.as_ref(), context)?,
        )),
        Obj::Div(operation) => Ok(format!(
            "({} / {})",
            render_real_source_object(operation.left.as_ref(), context)?,
            render_real_source_object(operation.right.as_ref(), context)?,
        )),
        Obj::Abs(operation) => Ok(format!(
            "|{}|",
            render_real_source_object(operation.arg.as_ref(), context)?
        )),
        Obj::FnObj(application) => {
            let application = lower_source_function_application_with_result_owned_occurrence(
                application,
                context,
            )?;
            let return_set = function_application_return_set_from_result(&application, context)?;
            if return_set
                != LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real)
            {
                return Err(
                    "function application has no verifier-owned exact R return carrier".into(),
                );
            }
            render_function_application(&application, context)
        }
        _ => Err(format!(
            "source object `{object}` has no reviewed exact ℝ representation"
        )),
    }
}

pub(in super::super) fn fact_matches_structured_induction_goal_substitution(
    source: &Fact,
    target: &Fact,
    parameter_symbol_id: SymbolId,
    replacement: &Obj,
) -> bool {
    let argument_pairs = match (source, target) {
        (Fact::AtomicFact(source), Fact::AtomicFact(target)) => {
            Runtime::_verify_atomic_fact_the_same_type_and_return_matched_args(source, target)
        }
        (Fact::AndFact(source), Fact::AndFact(target)) => {
            Runtime::_verify_and_fact_the_same_type_and_return_matched_args(source, target)
        }
        (Fact::ChainFact(source), Fact::ChainFact(target)) => {
            Runtime::_verify_chain_fact_the_same_type_and_return_matched_args(source, target)
        }
        (Fact::OrFact(source), Fact::OrFact(target)) => {
            Runtime::_verify_or_fact_the_same_type_and_return_matched_args(source, target)
        }
        _ => return false,
    };
    let Some(argument_pairs) = argument_pairs.ok().flatten() else {
        return false;
    };
    argument_pairs.iter().all(|(source, target)| {
        object_matches_structured_induction_substitution(
            source,
            target,
            parameter_symbol_id,
            replacement,
        )
    })
}

pub(in super::super) fn object_matches_structured_induction_substitution(
    source: &Obj,
    target: &Obj,
    parameter_symbol_id: SymbolId,
    replacement: &Obj,
) -> bool {
    if object_is_symbol(source, parameter_symbol_id) {
        return objects_align_by_nested_rational_normalization_for_result_compiler(
            replacement,
            target,
        );
    }
    if obj_equality_key(source) == obj_equality_key(target) {
        return true;
    }
    let comparison: Result<bool, ()> = Runtime::same_shape_and_corresponding_args_match(
        source,
        target,
        &mut |source_argument, target_argument| {
            Ok(object_matches_structured_induction_substitution(
                source_argument,
                target_argument,
                parameter_symbol_id,
                replacement,
            ))
        },
    );
    comparison.unwrap_or(false)
}
