//! Range endpoints, typed spines, and exact unary integer functions.

use super::super::*;

pub(in super::super) fn render_integer_endpoint(
    object: &LeanTargetObjectRepresentation,
    _context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let LeanTargetObjectRepresentation::Number { normalized_value } = object else {
        return Err("integer range endpoints currently require closed integer numerals".into());
    };
    if normalized_value.parse::<i128>().is_err() {
        return Err(format!(
            "integer range endpoint `{normalized_value}` is not a closed integer numeral"
        ));
    }
    Ok(format!("({normalized_value} : ℤ)"))
}

pub(in super::super) fn render_natural_endpoint(
    object: &LeanTargetObjectRepresentation,
) -> Result<String, String> {
    let LeanTargetObjectRepresentation::Number { normalized_value } = object else {
        return Err("finite sequence length currently requires a closed natural numeral".into());
    };
    if normalized_value.is_empty()
        || !normalized_value
            .chars()
            .all(|character| character.is_ascii_digit())
    {
        return Err(format!(
            "finite sequence length `{normalized_value}` is not a natural numeral"
        ));
    }
    Ok(format!("({normalized_value} : Nat)"))
}

pub(in super::super) fn render_typed_spine(
    items: &[LeanTargetObjectRepresentation],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let mut tail = "Litex.HNil.nil".to_string();
    for item in items.iter().rev() {
        tail = format!(
            "(Litex.HCons.mk {} {tail})",
            render_lean_source_for_target_object_representation(item, context)?
        );
    }
    Ok(tail)
}

pub(in super::super) fn render_exact_unary_integer_function(
    function: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(String, Option<(String, String)>), String> {
    match function {
        LeanTargetObjectRepresentation::Symbol { symbol_id, .. } => {
            let source = render_ir_symbol(function, context)?;
            let mut matching_bindings = context
                .function_bindings
                .values()
                .filter(|binding| {
                    binding.symbol_id == *symbol_id
                        && binding.function.parameters.len() == 1
                        && binding.function.domain_facts.is_empty()
                        && binding.function.parameters[0].set
                            == LeanTargetObjectRepresentation::StandardSet(
                                LeanTargetStandardSet::Integer,
                            )
                        && binding.function.return_set.as_ref()
                            == &LeanTargetObjectRepresentation::StandardSet(
                                LeanTargetStandardSet::Integer,
                            )
                })
                .collect::<Vec<_>>();
            matching_bindings.sort_by(|left, right| {
                left.membership_proof_name.cmp(&right.membership_proof_name)
            });
            matching_bindings.dedup_by(|left, right| {
                left.membership_proof_name == right.membership_proof_name
                    && left.direct == right.direct
            });
            let [binding] = matching_bindings.as_slice() else {
                return Err(
                    "sum function symbol has no unique exact unary Z-to-Z membership binding"
                        .into(),
                );
            };
            if binding.direct {
                Ok((source, None))
            } else {
                Ok((
                    format!(
                        "(Litex.In.rep {source} ({}))",
                        binding.membership_proof_name
                    ),
                    Some((source, binding.membership_proof_name.clone())),
                ))
            }
        }
        _ => Ok((
            render_lean_source_for_target_object_representation(function, context)?,
            None,
        )),
    }
}
