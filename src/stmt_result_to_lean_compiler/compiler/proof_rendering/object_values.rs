//! Indexed tuple classification and set-definition values.

use super::super::*;

pub(in super::super) fn indexed_tuple_value_is_complex(
    object: &LeanTargetObjectRepresentation,
    index: SymbolId,
) -> bool {
    match object {
        LeanTargetObjectRepresentation::Number { .. }
        | LeanTargetObjectRepresentation::Constant(_) => true,
        LeanTargetObjectRepresentation::Symbol { symbol_id, .. } => *symbol_id == index,
        LeanTargetObjectRepresentation::BuiltinApp {
            operator,
            arguments,
            ..
        } if matches!(
            operator,
            LeanTargetBuiltinObjectOperator::Add
                | LeanTargetBuiltinObjectOperator::Sub
                | LeanTargetBuiltinObjectOperator::Mul
                | LeanTargetBuiltinObjectOperator::Div
        ) =>
        {
            arguments
                .iter()
                .all(|argument| indexed_tuple_value_is_complex(argument, index))
        }
        _ => false,
    }
}

pub(in super::super) fn render_set_definition_value(
    value: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match value {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
            Ok("Litex.R".into())
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Complex) => {
            Ok("Litex.C".into())
        }
        LeanTargetObjectRepresentation::SetBuilder(_) => {
            render_lean_source_for_target_set_representation(value, context)
        }
        LeanTargetObjectRepresentation::FunctionSet { .. } => {
            render_lean_source_for_target_set_representation(value, context)
        }
        _ => Err(format!(
            "unsupported compiler named set definition value `{value:?}`"
        )),
    }
}
