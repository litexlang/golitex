//! Lean target-set representation rendering.

use super::super::*;

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
            nested
                .exact_carrier_values
                .insert(builder.symbol_id, parameter.clone());
            nested
                .semantic_zero_ended_order_symbols
                .insert(builder.symbol_id);
            if let Some(real) = exact_set_real_value(builder.set.as_ref(), &parameter) {
                nested.numeric_real_values.insert(builder.symbol_id, real);
            }
            if let Some(integer) = exact_set_integer_value(builder.set.as_ref(), &parameter) {
                nested
                    .numeric_integer_values
                    .insert(builder.symbol_id, integer);
            }
            if let Some(rational) = exact_set_rational_value(builder.set.as_ref(), &parameter) {
                nested
                    .numeric_rational_values
                    .insert(builder.symbol_id, rational);
            }
            if let Some(representation) = exact_set_numeric_value(builder.set.as_ref(), &parameter)
            {
                nested
                    .numeric_representations
                    .insert(builder.symbol_id, representation);
            }
            if let Some(proof) = exact_set_numeric_proof(builder.set.as_ref(), &parameter) {
                nested
                    .numeric_representation_memberships
                    .insert(builder.symbol_id, proof);
            }
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
        other => Err(format!(
            "unsupported compiler function domain/codomain `{other:?}`"
        )),
    }
}
