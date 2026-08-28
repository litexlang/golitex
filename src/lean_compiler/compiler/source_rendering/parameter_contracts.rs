//! Parameter premise and function-contract validation.

use super::super::*;

pub(in super::super) fn validate_set_parameter_premise(
    symbol_id: SymbolId,
    premise: &Fact,
) -> Result<(), String> {
    let Fact::AtomicFact(AtomicFact::IsSetFact(is_set)) = premise else {
        return Err(format!(
            "set parameter retained non-set evidence `{premise}`"
        ));
    };
    let Obj::Atom(atom) = &is_set.set else {
        return Err("set parameter evidence targets a non-symbol object".into());
    };
    if atom.symbol_ref().map(|symbol| symbol.id()) != Some(symbol_id) {
        return Err("set parameter evidence changed its SymbolId".into());
    }
    Ok(())
}

pub(in super::super) fn validate_object_parameter_premise(
    symbol_id: SymbolId,
    expected_set: &Obj,
    premise: &Fact,
) -> Result<(), String> {
    let (element, set) = membership_parts(premise)?;
    if !object_is_symbol(element, symbol_id) {
        return Err("object parameter evidence changed its SymbolId".into());
    }
    if !object_parameter_carriers_align(expected_set, set) {
        return Err("object parameter evidence changed its carrier set".into());
    }
    Ok(())
}

pub(in super::super) fn object_parameter_carriers_align(expected: &Obj, retained: &Obj) -> bool {
    if obj_equality_key(expected) == obj_equality_key(retained) {
        return true;
    }
    let (Obj::SeqSet(expected_sequence), Obj::FnSet(retained_function)) = (expected, retained)
    else {
        return false;
    };
    let [parameter_group] = retained_function
        .body
        .set_bound_parameters
        .groups
        .as_slice()
    else {
        return false;
    };
    parameter_group.params.len() == 1
        && matches!(
            parameter_group.set_obj(),
            Obj::StandardSet(StandardSet::NPos)
        )
        && retained_function.body.dom_facts.is_empty()
        && obj_equality_key(retained_function.body.ret_set.as_ref())
            == obj_equality_key(expected_sequence.set.as_ref())
}

pub(in super::super) fn validate_refined_set_parameter_premise(
    symbol_id: SymbolId,
    param_type: &ParamType,
    premise: &Fact,
) -> Result<(), String> {
    let target = match (param_type, premise) {
        (ParamType::NonemptySet(_), Fact::AtomicFact(AtomicFact::IsNonemptySetFact(property))) => {
            &property.set
        }
        (ParamType::FiniteSet(_), Fact::AtomicFact(AtomicFact::IsFiniteSetFact(property))) => {
            &property.set
        }
        (ParamType::NonemptySet(_), _) => {
            return Err(format!(
                "nonempty-set parameter retained different evidence `{premise}`"
            ));
        }
        (ParamType::FiniteSet(_), _) => {
            return Err(format!(
                "finite-set parameter retained different evidence `{premise}`"
            ));
        }
        _ => return Err("refined-set validator received another parameter type".into()),
    };
    let Obj::Atom(atom) = target else {
        return Err("refined-set parameter evidence targets a non-symbol object".into());
    };
    if atom.symbol_ref().map(|symbol| symbol.id()) != Some(symbol_id) {
        return Err("refined-set parameter evidence changed its SymbolId".into());
    }
    Ok(())
}

pub(in super::super) fn set_requires_heterogeneous_carrier(set: &Obj) -> bool {
    matches!(set, Obj::Atom(AtomObj::Bound(_)))
}

pub(in super::super) fn validate_unary_function_type(
    function: &LeanTargetFunctionTypeRepresentation,
) -> Result<(), String> {
    if function.parameters.len() != 1 {
        return Err("compiler function-set MVP supports exactly one parameter".into());
    }
    if let LeanTargetObjectRepresentation::FunctionSet { function } = function.return_set.as_ref() {
        validate_unary_function_type(function)?;
    }
    Ok(())
}

pub(in super::super) fn validate_function_type(
    function: &LeanTargetFunctionTypeRepresentation,
) -> Result<(), String> {
    if function.parameters.is_empty() {
        return Err("compiler function set retained an empty source parameter layer".into());
    }
    if let LeanTargetObjectRepresentation::FunctionSet { function } = function.return_set.as_ref() {
        validate_function_type(function)?;
    }
    Ok(())
}

pub(in super::super) fn function_uses_telescope(
    function: &LeanTargetFunctionTypeRepresentation,
) -> bool {
    if function.parameters.len() != 1 {
        return true;
    }
    if !function.domain_facts.is_empty()
        && matches!(
            function.parameters[0].set,
            LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural)
        )
    {
        // The finite-sequence bound depends on the natural representative
        // selected by the parameter's `N+` membership proof. A `FnWhere`
        // predicate receives only the heterogeneous value, while the
        // telescope parameter node owns both that value and its membership.
        return true;
    }
    let parameter_symbols = function
        .parameters
        .iter()
        .map(|parameter| parameter.symbol_id)
        .collect::<HashSet<_>>();
    function
        .parameters
        .iter()
        .any(|parameter| !object_ir_is_independent_of_symbols(&parameter.set, &parameter_symbols))
        || !object_ir_is_independent_of_symbols(function.return_set.as_ref(), &parameter_symbols)
}

pub(in super::super) fn object_ir_is_independent_of_symbols(
    object: &LeanTargetObjectRepresentation,
    symbol_ids: &HashSet<SymbolId>,
) -> bool {
    match object {
        LeanTargetObjectRepresentation::Symbol { symbol_id, .. } => !symbol_ids.contains(symbol_id),
        LeanTargetObjectRepresentation::FunctionSet { function } => {
            function
                .parameters
                .iter()
                .all(|parameter| object_ir_is_independent_of_symbols(&parameter.set, symbol_ids))
                && object_ir_is_independent_of_symbols(function.return_set.as_ref(), symbol_ids)
        }
        LeanTargetObjectRepresentation::FunctionApplication(application) => {
            object_ir_is_independent_of_symbols(application.head.as_ref(), symbol_ids)
                && application.argument_layers.iter().all(|layer| {
                    layer
                        .iter()
                        .all(|argument| object_ir_is_independent_of_symbols(argument, symbol_ids))
                })
        }
        LeanTargetObjectRepresentation::ClosedRange { start, end }
        | LeanTargetObjectRepresentation::Range { start, end } => {
            object_ir_is_independent_of_symbols(start, symbol_ids)
                && object_ir_is_independent_of_symbols(end, symbol_ids)
        }
        LeanTargetObjectRepresentation::CartesianProduct { factors } => factors
            .iter()
            .all(|factor| object_ir_is_independent_of_symbols(factor, symbol_ids)),
        LeanTargetObjectRepresentation::GeneralCartesianProduct {
            index_set,
            family_set,
            family_function,
        } => {
            object_ir_is_independent_of_symbols(index_set, symbol_ids)
                && object_ir_is_independent_of_symbols(family_set, symbol_ids)
                && object_ir_is_independent_of_symbols(family_function, symbol_ids)
        }
        LeanTargetObjectRepresentation::SequenceSet { values, length } => {
            object_ir_is_independent_of_symbols(values, symbol_ids)
                && length
                    .as_ref()
                    .is_none_or(|length| object_ir_is_independent_of_symbols(length, symbol_ids))
        }
        LeanTargetObjectRepresentation::MatrixSet {
            values,
            row_count,
            column_count,
        } => {
            object_ir_is_independent_of_symbols(values, symbol_ids)
                && object_ir_is_independent_of_symbols(row_count, symbol_ids)
                && object_ir_is_independent_of_symbols(column_count, symbol_ids)
        }
        LeanTargetObjectRepresentation::Aggregate { arguments, .. } => arguments
            .iter()
            .all(|argument| object_ir_is_independent_of_symbols(argument, symbol_ids)),
        LeanTargetObjectRepresentation::TupleDimension(object) => {
            object_ir_is_independent_of_symbols(object, symbol_ids)
        }
        LeanTargetObjectRepresentation::IndexedAccess { object, index } => {
            object_ir_is_independent_of_symbols(object, symbol_ids)
                && object_ir_is_independent_of_symbols(index, symbol_ids)
        }
        LeanTargetObjectRepresentation::BuiltinApp { arguments, .. }
        | LeanTargetObjectRepresentation::Collection {
            items: arguments, ..
        } => arguments
            .iter()
            .all(|argument| object_ir_is_independent_of_symbols(argument, symbol_ids)),
        // Binder-owning objects are kept on the dependent telescope path. The
        // owned binder itself may hide a reference to an outer parameter in
        // one of its source facts, which the flattened IR does not erase.
        LeanTargetObjectRepresentation::SetBuilder(_)
        | LeanTargetObjectRepresentation::AnonymousFunction(_) => false,
        LeanTargetObjectRepresentation::Number { .. }
        | LeanTargetObjectRepresentation::Constant(_)
        | LeanTargetObjectRepresentation::StandardSet(_) => true,
    }
}
