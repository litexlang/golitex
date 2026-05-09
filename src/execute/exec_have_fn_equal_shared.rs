use crate::prelude::*;

/// Turn a [`FnSet`] (parser-level function-space type) into a [`FnSetClause`]-shaped bundle.
pub(crate) fn fn_set_to_fn_set_clause(fs: &FnSet) -> FnSetClause {
    FnSetClause::new(
        fs.body.params_def_with_set.clone(),
        fs.body.dom_facts.clone(),
        (*fs.body.ret_set).clone(),
    )
}

/// Forall parameters, `dom` [`Fact`]s, and curried `(...)(...)` argument layers (one vec per paren
/// group), matching [`HaveFnEqualStmt`]'s `forall` for that signature.
pub(crate) fn forall_binders_dom_and_curried_layers_from_fn_set_clause(
    clause: &FnSetClause,
) -> (ParamDefWithType, Vec<Fact>, Vec<Vec<String>>) {
    let mut type_groups: Vec<ParamGroupWithParamType> = Vec::new();
    let mut dom_facts: Vec<Fact> = Vec::new();
    let mut layers: Vec<Vec<String>> = Vec::new();

    for pg in clause.params_def_with_set.iter() {
        type_groups.push(ParamGroupWithParamType::new(
            pg.params.clone(),
            param_group_with_set_to_param_type(pg),
        ));
    }
    for d in clause.dom_facts.iter() {
        dom_facts.push(d.clone().into());
    }
    layers.push(ParamGroupWithSet::collect_param_names(
        &clause.params_def_with_set,
    ));

    let mut ret_set = clause.ret_set.clone();
    while let Obj::FnSet(inner) = ret_set {
        for pg in inner.body.params_def_with_set.iter() {
            type_groups.push(ParamGroupWithParamType::new(
                pg.params.clone(),
                param_group_with_set_to_param_type(pg),
            ));
        }

        for d in inner.body.dom_facts.iter() {
            dom_facts.push(d.clone().into());
        }

        let layer_names: Vec<String> = inner
            .body
            .params_def_with_set
            .iter()
            .flat_map(|pg| pg.params.iter())
            .cloned()
            .collect();
        layers.push(layer_names);

        ret_set = (*inner.body.ret_set).clone();
    }

    (ParamDefWithType::new(type_groups), dom_facts, layers)
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
/// other shape accepted by [`FnObjHead::from_name_obj`].
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

pub(crate) fn param_defs_with_type_from_have_fn_clause(clause: &FnSetClause) -> ParamDefWithType {
    let mut groups: Vec<ParamGroupWithParamType> =
        Vec::with_capacity(clause.params_def_with_set.len());
    for param_def_with_set in clause.params_def_with_set.iter() {
        groups.push(ParamGroupWithParamType::new(
            param_def_with_set.params.clone(),
            param_group_with_set_to_param_type(param_def_with_set),
        ));
    }
    ParamDefWithType::new(groups)
}

fn param_group_with_set_to_param_type(param_def: &ParamGroupWithSet) -> ParamType {
    match &param_def.param_type {
        ParamGroupWithSetTypeEnum::Set(set) => ParamType::Obj(set.clone()),
    }
}
