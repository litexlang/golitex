use crate::ast::obj::{FnObj, FnObjHead, IdentifierObj, Obj};
use crate::ast::param::SetBoundParameterList;
use crate::runtime::runtime_ids::IdentifierId;
use std::collections::HashMap;

pub(super) fn fn_app_identifier_and_args(fn_obj: &FnObj) -> Option<(IdentifierObj, Vec<Obj>)> {
    if fn_obj.body.len() != 1 {
        return None;
    }
    let FnObjHead::Identifier(head) = fn_obj.head.as_ref() else {
        return None;
    };
    let args: Vec<Obj> = fn_obj.body[0].iter().map(|a| a.as_ref().clone()).collect();
    Some((head.clone(), args))
}

pub(super) fn fn_app_args(fn_obj: &FnObj) -> Option<Vec<Obj>> {
    if fn_obj.body.len() != 1 {
        return None;
    }
    Some(fn_obj.body[0].iter().map(|a| a.as_ref().clone()).collect())
}

pub(in crate::execute) fn set_bound_parameter_count(list: &SetBoundParameterList) -> usize {
    let mut n = 0;
    for group in &list.groups {
        n += group.params.len();
    }
    n
}

pub(in crate::execute) fn set_bound_params_to_arg_map(
    list: &SetBoundParameterList,
    args: &[Obj],
) -> HashMap<IdentifierId, Obj> {
    let mut map = HashMap::new();
    let mut i = 0;
    for group in &list.groups {
        for param in &group.params {
            if i < args.len() {
                map.insert(param.id, args[i].clone());
                i += 1;
            }
        }
    }
    map
}
