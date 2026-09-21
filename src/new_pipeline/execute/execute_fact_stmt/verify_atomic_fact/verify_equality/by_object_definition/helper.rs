use crate::new_pipeline::ast::obj::{FnObj, FnObjHead, IdentifierObj, Obj};
use crate::new_pipeline::ast::param::SetBoundParameterList;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use std::collections::HashMap;

pub(super) fn identifier_plain_name(obj: &Obj) -> Option<&str> {
    let Obj::Identifier(identifier) = obj else {
        return None;
    };
    match identifier {
        IdentifierObj::Plain { name, .. }
        | IdentifierObj::WithExportFileId { name, .. }
        | IdentifierObj::WithModAndExportFileId { name, .. } => Some(name.as_str()),
    }
}

pub(super) fn fn_app_name_and_args(fn_obj: &FnObj) -> Option<(String, Vec<Obj>)> {
    if fn_obj.body.len() != 1 {
        return None;
    }
    let FnObjHead::Identifier(head) = fn_obj.head.as_ref() else {
        return None;
    };
    let name = match head {
        IdentifierObj::Plain { name, .. }
        | IdentifierObj::WithExportFileId { name, .. }
        | IdentifierObj::WithModAndExportFileId { name, .. } => name.as_str().to_string(),
    };
    let args: Vec<Obj> = fn_obj.body[0].iter().map(|a| a.as_ref().clone()).collect();
    Some((name, args))
}

pub(super) fn set_bound_parameter_count(list: &SetBoundParameterList) -> usize {
    let mut n = 0;
    for group in &list.groups {
        n += group.params.len();
    }
    n
}

pub(super) fn set_bound_params_to_arg_map(
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
