use crate::prelude::*;

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
    let fn_head_atom: Atom = Identifier::new(function_name.to_string()).into();
    let mut body_vectors: Vec<Vec<Box<Obj>>> = Vec::with_capacity(layer_param_names.len());
    for layer in layer_param_names {
        let mut group: Vec<Box<Obj>> = Vec::with_capacity(layer.len());
        for name in layer {
            group.push(Box::new(name.clone().into()));
        }
        body_vectors.push(group);
    }
    FnObj::new(fn_head_atom, body_vectors).into()
}

pub(crate) fn param_defs_with_type_from_have_fn_clause(clause: &FnSetClause) -> ParamDefWithType {
    let mut groups: Vec<ParamGroupWithParamType> =
        Vec::with_capacity(clause.params_def_with_set.len());
    for param_def_with_set in clause.params_def_with_set.iter() {
        groups.push(ParamGroupWithParamType::new(
            param_def_with_set.params.clone(),
            ParamType::Obj(param_def_with_set.set.clone()),
        ));
    }
    ParamDefWithType::new(groups)
}
