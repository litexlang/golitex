use crate::new_pipeline::ast::obj::{FnObj, FnObjHead, IdentifierObj, Literal, Obj, Number};
use crate::new_pipeline::ast::param::SetBoundParameterList;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use std::collections::HashSet;

pub const MAX_EVAL_DEPTH: usize = 64;

pub fn is_number_literal(obj: &Obj) -> bool {
    matches!(obj, Obj::Literal(Literal::Number(_)))
}

pub fn number_literal_key(obj: &Obj) -> Option<String> {
    match obj {
        Obj::Literal(Literal::Number(Number { normalized_value })) => {
            Some(normalized_value.clone())
        }
        _ => None,
    }
}

pub fn fn_obj_plain_name(fn_obj: &FnObj) -> Option<String> {
    match fn_obj.head.as_ref() {
        FnObjHead::Identifier(IdentifierObj::Plain { name, .. }) => Some(name.clone()),
        _ => None,
    }
}

pub fn flatten_fn_obj_args(fn_obj: &FnObj) -> Vec<Obj> {
    let mut out = Vec::new();
    for group in &fn_obj.body {
        for arg in group {
            out.push(arg.as_ref().clone());
        }
    }
    out
}

pub fn algo_call_key(fn_name: &str, evaluated_args: &[Obj]) -> Option<String> {
    let mut parts = Vec::with_capacity(evaluated_args.len());
    for arg in evaluated_args {
        parts.push(number_literal_key(arg)?);
    }
    Some(format!("{fn_name}({})", parts.join(",")))
}

pub fn set_bound_parameter_count(list: &SetBoundParameterList) -> usize {
    let mut n = 0;
    for group in &list.groups {
        n += group.params.len();
    }
    n
}

pub fn build_algo_param_subst(
    params: &SetBoundParameterList,
    evaluated_args: &[Obj],
) -> Option<std::collections::HashMap<IdentifierId, Obj>> {
    if set_bound_parameter_count(params) != evaluated_args.len() {
        return None;
    }
    let mut map = std::collections::HashMap::new();
    let mut i = 0;
    for group in &params.groups {
        for param in &group.params {
            map.insert(param.id, evaluated_args[i].clone());
            i += 1;
        }
    }
    Some(map)
}

pub type ActiveAlgoCalls = HashSet<String>;
