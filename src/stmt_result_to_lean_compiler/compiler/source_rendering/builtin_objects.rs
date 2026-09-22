//! Built-in objects and numeric target representations.

use super::super::*;

pub(in super::super) fn render_builtin_object(
    operator: LeanTargetBuiltinObjectOperator,
    arguments: &[LeanTargetObjectRepresentation],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let binary_symbol = match operator {
        LeanTargetBuiltinObjectOperator::Add => Some("+"),
        LeanTargetBuiltinObjectOperator::Sub => Some("-"),
        LeanTargetBuiltinObjectOperator::Mul => Some("*"),
        LeanTargetBuiltinObjectOperator::Div => Some("/"),
        _ => None,
    };
    if let Some(symbol) = binary_symbol {
        let [left, right] = arguments else {
            return Err(format!("numeric operator `{operator:?}` changed its arity"));
        };
        return Ok(format!(
            "({} {symbol} {})",
            render_lean_source_for_numeric_target_object_representation(left, context)?,
            render_lean_source_for_numeric_target_object_representation(right, context)?
        ));
    }
    match (operator, arguments) {
        (LeanTargetBuiltinObjectOperator::Abs, [value]) => Ok(format!(
            "(Litex.abs {})",
            render_lean_source_for_numeric_target_object_representation(value, context)?
        )),
        (LeanTargetBuiltinObjectOperator::Min, [left, right]) => Ok(format!(
            "(Litex.min {} {})",
            render_lean_source_for_numeric_target_object_representation(left, context)?,
            render_lean_source_for_numeric_target_object_representation(right, context)?
        )),
        (LeanTargetBuiltinObjectOperator::Max, [left, right]) => Ok(format!(
            "(Litex.max {} {})",
            render_lean_source_for_numeric_target_object_representation(left, context)?,
            render_lean_source_for_numeric_target_object_representation(right, context)?
        )),
        (LeanTargetBuiltinObjectOperator::Union, [left, right]) => Ok(format!(
            "(Litex.union {} {})",
            render_lean_source_for_target_object_representation(left, context)?,
            render_lean_source_for_target_object_representation(right, context)?
        )),
        (LeanTargetBuiltinObjectOperator::Intersect, [left, right]) => Ok(format!(
            "(Litex.intersect {} {})",
            render_lean_source_for_target_object_representation(left, context)?,
            render_lean_source_for_target_object_representation(right, context)?
        )),
        (LeanTargetBuiltinObjectOperator::SetMinus, [left, right]) => Ok(format!(
            "(Litex.setMinus {} {})",
            render_lean_source_for_target_object_representation(left, context)?,
            render_lean_source_for_target_object_representation(right, context)?
        )),
        (LeanTargetBuiltinObjectOperator::FamilyUnion, [family]) => Ok(format!(
            "(Litex.familyUnion {})",
            render_lean_source_for_target_object_representation(family, context)?
        )),
        (LeanTargetBuiltinObjectOperator::FamilyIntersect, [family]) => Ok(format!(
            "(Litex.familyIntersect {})",
            render_lean_source_for_target_object_representation(family, context)?
        )),
        (LeanTargetBuiltinObjectOperator::PowerSet, [base]) => Ok(format!(
            "(Litex.powerSet {})",
            render_lean_source_for_target_object_representation(base, context)?
        )),
        _ => Err(format!(
            "unsupported typed builtin object `{operator:?}` with {} arguments",
            arguments.len()
        )),
    }
}

pub(in super::super) fn render_lean_source_for_numeric_target_object_representation(
    object: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } = object {
        if let Some(value) = context.numeric_representations.get(symbol_id) {
            return Ok(value.clone());
        }
    }
    render_lean_source_for_target_object_representation(object, context)
}
