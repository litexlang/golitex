use crate::prelude::*;
use std::collections::HashMap;

/// Turn a [`FnSet`] (parser-level function-space type) into a [`FnSetClause`]-shaped bundle.
pub(crate) fn fn_set_to_fn_set_clause(fs: &FnSet) -> FnSetClause {
    FnSetClause::new(
        fs.body.params_def_with_set.clone(),
        fs.body.dom_facts.clone(),
        (*fs.body.ret_set).clone(),
    )
    .expect("fn set signature was already validated")
}

/// Forall parameters, `dom` [`Fact`]s, and curried `(...)(...)` argument layers (one vec per paren
/// group), matching [`HaveFnEqualStmt`]'s `forall` for that signature.
pub(crate) fn forall_binders_dom_and_curried_layers_from_fn_set_clause(
    runtime: &Runtime,
    clause: &FnSetClause,
) -> Result<(ParamDefWithType, Vec<Fact>, Vec<Vec<String>>), RuntimeError> {
    let mut type_groups: Vec<ParamGroupWithParamType> = Vec::new();
    let mut dom_facts: Vec<Fact> = Vec::new();
    let mut layers: Vec<Vec<String>> = Vec::new();
    let mut fn_set_param_to_forall_param: HashMap<String, Obj> = HashMap::new();

    append_fn_set_param_groups_as_forall_param_type_groups(
        runtime,
        &clause.params_def_with_set,
        &mut fn_set_param_to_forall_param,
        &mut type_groups,
    )?;
    for d in clause.dom_facts.iter() {
        dom_facts.push(
            runtime
                .inst_or_and_chain_atomic_fact(
                    d,
                    &fn_set_param_to_forall_param,
                    ParamObjType::FnSet,
                    None,
                )?
                .into(),
        );
    }
    layers.push(ParamGroupWithSet::collect_param_names(
        &clause.params_def_with_set,
    ));

    let mut ret_set = clause.ret_set.clone();
    while let Obj::FnSet(inner) = ret_set {
        append_fn_set_param_groups_as_forall_param_type_groups(
            runtime,
            &inner.body.params_def_with_set,
            &mut fn_set_param_to_forall_param,
            &mut type_groups,
        )?;

        for d in inner.body.dom_facts.iter() {
            dom_facts.push(
                runtime
                    .inst_or_and_chain_atomic_fact(
                        d,
                        &fn_set_param_to_forall_param,
                        ParamObjType::FnSet,
                        None,
                    )?
                    .into(),
            );
        }

        let layer_names: Vec<String> = inner
            .body
            .params_def_with_set
            .iter()
            .flat_map(|pg| pg.params.iter())
            .cloned()
            .collect();
        layers.push(layer_names);

        ret_set = runtime.inst_obj(
            inner.body.ret_set.as_ref(),
            &fn_set_param_to_forall_param,
            ParamObjType::FnSet,
        )?;
    }

    Ok((ParamDefWithType::new(type_groups), dom_facts, layers))
}

pub(crate) fn build_curried_function_obj_from_layers_with_binding(
    function_name: &str,
    layer_param_names: &[Vec<String>],
    binding: ParamObjType,
) -> Obj {
    let mut body_vectors: Vec<Vec<Box<Obj>>> = Vec::with_capacity(layer_param_names.len());
    for layer in layer_param_names {
        let mut group: Vec<Box<Obj>> = Vec::with_capacity(layer.len());
        for name in layer {
            group.push(Box::new(obj_for_bound_param_in_scope(
                name.clone(),
                binding,
            )));
        }
        body_vectors.push(group);
    }
    FnObj::new(
        FnObjHead::Identifier(Identifier::new(function_name.to_string())),
        body_vectors,
    )
    .into()
}

/// Anonymous function value with curried `forall` binders.
pub(crate) fn build_curried_anonymous_fn_from_layers_forall(
    af: &AnonymousFn,
    layer_param_names: &[Vec<String>],
) -> Obj {
    let mut body_vectors: Vec<Vec<Box<Obj>>> = Vec::with_capacity(layer_param_names.len());
    for layer in layer_param_names {
        let mut group: Vec<Box<Obj>> = Vec::with_capacity(layer.len());
        for name in layer {
            group.push(Box::new(obj_for_bound_param_in_scope(
                name.clone(),
                ParamObjType::Forall,
            )));
        }
        body_vectors.push(group);
    }
    FnObj::new(
        FnObjHead::AnonymousFnLiteral(Box::new(af.clone())),
        body_vectors,
    )
    .into()
}

/// Build `func` applied along `layers` using forall binders; `func` is a name, anonymous fn, or
/// other shape accepted by [`FnObjHead::given_an_atom_return_a_fn_obj_head`].
pub(crate) fn build_curried_fn_value_apply_for_fn_eq(
    func: &Obj,
    layer_param_names: &[Vec<String>],
) -> Option<Obj> {
    // Inside `verify_forall` with `define_params(..., Forall)`, curried args must be
    // `ForallFreeParamObj` so `f(x)` matches the same `x` as user `forall` facts (e.g. chains like
    // `f(x) = x = g(x)`). FnSet-tagged args would not unify with those citations.
    if let Some(id) = match func {
        Obj::Atom(AtomObj::Identifier(id)) => Some(id.name.as_str()),
        _ => None,
    } {
        return Some(build_curried_function_obj_from_layers_with_binding(
            id,
            layer_param_names,
            ParamObjType::Forall,
        ));
    }
    if let Obj::AnonymousFn(af) = func {
        return Some(build_curried_anonymous_fn_from_layers_forall(
            af,
            layer_param_names,
        ));
    }
    if let Some(head) = FnObjHead::given_an_atom_return_a_fn_obj_head(func.clone()) {
        let mut body_vectors: Vec<Vec<Box<Obj>>> = Vec::with_capacity(layer_param_names.len());
        for layer in layer_param_names {
            let mut group: Vec<Box<Obj>> = Vec::with_capacity(layer.len());
            for name in layer {
                group.push(Box::new(obj_for_bound_param_in_scope(
                    name.clone(),
                    ParamObjType::Forall,
                )));
            }
            body_vectors.push(group);
        }
        return Some(FnObj::new(head, body_vectors).into());
    }
    None
}

pub(crate) fn build_function_obj_with_param_names(
    function_name: &str,
    param_names: &[String],
) -> Obj {
    build_curried_function_obj_from_layers(function_name, &[param_names.to_vec()])
}

/// One entry per curried stage, e.g. `g(c)(a, b)` → `[vec!["c"], vec!["a", "b"]]`.
pub(crate) fn build_curried_function_obj_from_layers(
    function_name: &str,
    layer_param_names: &[Vec<String>],
) -> Obj {
    build_curried_function_obj_from_layers_with_binding(
        function_name,
        layer_param_names,
        ParamObjType::FnSet,
    )
}

pub(crate) fn forall_param_defs_dom_and_map_from_have_fn_clause(
    runtime: &Runtime,
    clause: &FnSetClause,
) -> Result<(ParamDefWithType, Vec<Fact>, HashMap<String, Obj>), RuntimeError> {
    let mut groups: Vec<ParamGroupWithParamType> =
        Vec::with_capacity(clause.params_def_with_set.len());
    let mut fn_set_param_to_forall_param: HashMap<String, Obj> = HashMap::new();
    append_fn_set_param_groups_as_forall_param_type_groups(
        runtime,
        &clause.params_def_with_set,
        &mut fn_set_param_to_forall_param,
        &mut groups,
    )?;

    let mut dom_facts = Vec::with_capacity(clause.dom_facts.len());
    for dom_fact in clause.dom_facts.iter() {
        dom_facts.push(
            runtime
                .inst_or_and_chain_atomic_fact(
                    dom_fact,
                    &fn_set_param_to_forall_param,
                    ParamObjType::FnSet,
                    None,
                )?
                .into(),
        );
    }

    Ok((
        ParamDefWithType::new(groups),
        dom_facts,
        fn_set_param_to_forall_param,
    ))
}

fn append_fn_set_param_groups_as_forall_param_type_groups(
    runtime: &Runtime,
    params_def_with_set: &ParamDefWithSet,
    fn_set_param_to_forall_param: &mut HashMap<String, Obj>,
    groups: &mut Vec<ParamGroupWithParamType>,
) -> Result<(), RuntimeError> {
    for param_def_with_set in params_def_with_set.iter() {
        let param_set = runtime.inst_obj(
            param_def_with_set.set_obj(),
            fn_set_param_to_forall_param,
            ParamObjType::FnSet,
        )?;
        groups.push(ParamGroupWithParamType::new(
            param_def_with_set.params.clone(),
            ParamType::Obj(param_set),
        ));
        for param_name in param_def_with_set.params.iter() {
            fn_set_param_to_forall_param.insert(
                param_name.clone(),
                obj_for_bound_param_in_scope(param_name.clone(), ParamObjType::Forall),
            );
        }
    }
    Ok(())
}
