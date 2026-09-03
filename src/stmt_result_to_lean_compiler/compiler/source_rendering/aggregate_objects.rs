//! Aggregate operations and literal indexed access.

use super::super::*;

pub(in super::super) fn render_aggregate_object(
    source: &LeanTargetSourceObject,
    kind: LeanTargetAggregateObjectConstructor,
    arguments: &[LeanTargetObjectRepresentation],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if kind == LeanTargetAggregateObjectConstructor::Sum {
        let well_definedness = context
            .well_definedness
            .as_ref()
            .ok_or_else(|| "integer range sum has no active Result-owned WD context".to_string())?;
        let iteration = if let Some(exact) = well_definedness.iterations.get(&source.semantic_key) {
            exact
        } else {
            let mut matching = Vec::new();
            for candidate in well_definedness.iterations.values() {
                if matches_directly_or_after_one_transparent_definition_pass(
                    &candidate.source_aggregate,
                    &source.object,
                    context,
                )? {
                    matching.push(candidate);
                }
            }
            let [matching] = matching.as_slice() else {
                let available = well_definedness
                    .iterations
                    .values()
                    .map(|candidate| candidate.source_aggregate.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                let mut visible_symbol_aliases = context
                    .symbol_names
                    .iter()
                    .map(|(symbol_id, name)| format!("{symbol_id:?} -> {name}"))
                    .collect::<Vec<_>>();
                visible_symbol_aliases.sort();
                return Err(format!(
                    "sum `{}` has {} matching Iteration WD Results; available owners: [{available}]; visible symbol aliases: [{}]",
                    source.object,
                    matching.len(),
                    visible_symbol_aliases.join(", ")
                ));
            };
            *matching
        };
        let Obj::Sum(_) = &iteration.source_aggregate else {
            return Err("sum occurrence selected a non-sum Iteration WD owner".into());
        };
        let Obj::Sum(current_sum) = &source.object else {
            return Err("sum representation retained a non-sum semantic source".into());
        };
        if obj_equality_key(&iteration.source_aggregate) != source.semantic_key
            && !matches_directly_or_after_one_transparent_definition_pass(
                &iteration.source_aggregate,
                &source.object,
                context,
            )?
        {
            return Err("sum occurrence changed its semantic key after WD selection".into());
        }
        if iteration.operation != "sum"
            || !matches!(&iteration.parameter_set, Obj::StandardSet(StandardSet::Z))
            || !matches!(&iteration.return_carrier, Obj::StandardSet(StandardSet::Z))
            || iteration.parameter_count != 1
            || iteration.domain_count != 0
            || !iteration_has_reviewed_integer_callable_contract(iteration)
            || !iteration.has_exact_integer_coverage
        {
            return Err(
                "sum Iteration WD Result is outside the reviewed unary Z-to-Z integer-range contract"
                    .into(),
            );
        }
        let [start, end, function] = arguments else {
            return Err("sum aggregate changed its exact source arity".into());
        };
        if LeanTargetObjectRepresentation::lower(current_sum.start.as_ref())? != *start
            || LeanTargetObjectRepresentation::lower(current_sum.end.as_ref())? != *end
            || LeanTargetObjectRepresentation::lower(current_sum.func.as_ref())? != *function
        {
            return Err("sum Iteration WD Result changed its ordered source arguments".into());
        }
        let (rendered_function, _) = render_exact_unary_integer_function(function, context)?;
        let rendered_start = render_integer_obj(current_sum.start.as_ref(), context)?;
        let rendered_end = render_integer_obj(current_sum.end.as_ref(), context)?;
        return Ok(format!(
            "(Litex.sum {} {} {})",
            rendered_start, rendered_end, rendered_function,
        ));
    }
    let (name, arity) = match kind {
        LeanTargetAggregateObjectConstructor::Sum => unreachable!("sum handled above"),
        LeanTargetAggregateObjectConstructor::Product => ("Litex.product", 3),
        LeanTargetAggregateObjectConstructor::FiniteSetSum => ("Litex.finiteSetSum", 2),
        LeanTargetAggregateObjectConstructor::FiniteSetProduct => ("Litex.finiteSetProduct", 2),
        LeanTargetAggregateObjectConstructor::Reduce => ("Litex.reduce", 5),
        LeanTargetAggregateObjectConstructor::FiniteSetReduce => ("Litex.finiteSetReduce", 4),
    };
    if arguments.len() != arity {
        return Err(format!(
            "aggregate `{kind:?}` changed its exact source arity"
        ));
    }
    let rendered = arguments
        .iter()
        .map(|argument| render_lean_source_for_target_object_representation(argument, context))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(format!("({name} {})", rendered.join(" ")))
}

pub(in super::super) fn render_literal_indexed_access(
    object: &LeanTargetObjectRepresentation,
    index: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } = object {
        if let Some(binding) = context.indexed_tuple_bindings.get(symbol_id) {
            let tuple = render_lean_source_for_target_object_representation(object, context)?;
            let exact_index = match index {
                LeanTargetObjectRepresentation::Symbol {
                    symbol_id: index_symbol_id,
                    ..
                } => context
                    .exact_tuple_indices
                    .get(index_symbol_id)
                    .cloned()
                    .ok_or_else(|| {
                        "indexed tuple projection has no exact checked index representative"
                            .to_string()
                    })?,
                LeanTargetObjectRepresentation::Number { normalized_value } => {
                    let value = normalized_value.parse::<usize>().map_err(|_| {
                        "indexed tuple projection index is not a natural numeral".to_string()
                    })?;
                    if value == 0 || value > binding.dimension {
                        return Err(
                            "indexed tuple projection index is outside its checked dimension"
                                .into(),
                        );
                    }
                    format!("⟨({value} : ℤ), by norm_num⟩")
                }
                _ => {
                    return Err(
                        "indexed tuple projection needs a checked range representative".into(),
                    );
                }
            };
            return Ok(format!("(Litex.indexedTupleAt {tuple} {exact_index})"));
        }
    }
    let LeanTargetObjectRepresentation::Number { normalized_value } = index else {
        return Err("literal tuple access requires a closed natural index".into());
    };
    let index = normalized_value
        .parse::<usize>()
        .map_err(|_| "literal tuple access has an invalid natural index".to_string())?;
    let LeanTargetObjectRepresentation::Collection { items, .. } = object else {
        return Err(
            "generic heterogeneous indexed access needs a checked projection recipe".into(),
        );
    };
    let item = items.get(index.saturating_sub(1)).ok_or_else(|| {
        "literal tuple access index is outside the retained source arity".to_string()
    })?;
    render_lean_source_for_target_object_representation(item, context)
}
