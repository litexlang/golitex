//! Parameter binding maps and universal-fact argument-shape keys.

use super::*;

pub(super) fn arg_match_bindings_for_params(
    known_forall_params: &TypedParameterList,
    known_exist_params: Option<&TypedParameterList>,
) -> Vec<SymbolId> {
    let mut bindings = known_forall_params
        .collect_param_bindings()
        .into_iter()
        .map(|binding| binding.id())
        .collect::<Vec<_>>();
    if let Some(exist_params) = known_exist_params {
        bindings.extend(
            exist_params
                .collect_param_bindings()
                .into_iter()
                .map(|binding| binding.id()),
        );
    }
    bindings
}

pub(super) fn arg_match_map_for_params(
    raw_arg_map: &HashMap<String, Obj>,
    params: &TypedParameterList,
) -> HashMap<String, Obj> {
    let mut result = HashMap::new();
    for binding in params.collect_param_bindings() {
        let key = binding.substitution_key();
        if let Some(obj) = raw_arg_map.get(&key) {
            insert_symbol_substitution(&mut result, &binding, obj.clone());
        }
    }
    result
}

pub(super) fn arg_match_binding_key(symbol: &SymbolRef) -> String {
    symbol.substitution_key()
}

pub(super) fn atomic_fact_in_forall_lookup_arg_shape_keys(
    atomic_fact: &AtomicFact,
) -> Vec<ForallArgumentShape> {
    let exact_key = forall_argument_shape(atomic_fact);
    let forall_param_key_part = (ObjKind::BoundParam, String::new());
    let mut keys = Vec::new();
    push_forall_argument_shape_if_new(&mut keys, exact_key.clone());

    for index in 0..exact_key.len() {
        let known_keys_count = keys.len();
        for key_index in 0..known_keys_count {
            let mut key = keys[key_index].clone();
            key[index] = forall_param_key_part.clone();
            push_forall_argument_shape_if_new(&mut keys, key);
        }
    }

    keys
}

pub(super) fn push_forall_argument_shape_if_new(
    keys: &mut Vec<ForallArgumentShape>,
    key: ForallArgumentShape,
) {
    if !keys.contains(&key) {
        keys.push(key);
    }
}
