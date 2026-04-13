use crate::prelude::*;

pub(crate) fn build_function_obj_with_param_names(
    function_name: &str,
    param_names: &[String],
) -> Obj {
    let mut function_args: Vec<Box<Obj>> = Vec::with_capacity(param_names.len());
    for param_name in param_names.iter() {
        function_args.push(Box::new(param_name.clone().into()));
    }

    let fn_head_atom: Atom = Identifier::new(function_name.to_string()).into();
    let fn_body_groups = vec![function_args];
    FnObj::new(fn_head_atom, fn_body_groups).into()
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
