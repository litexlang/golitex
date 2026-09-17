use std::collections::HashMap;

use crate::new_pipeline::ast::names::BoundName;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::param::{ParamType, SetBoundParameterList, TypedParameterList};
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::Runtime;

use super::capture;
use super::error::InstError;

impl Runtime {
    pub(crate) fn inst_param_type(
        &mut self,
        param_type: &ParamType,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<ParamType, InstError> {
        match param_type {
            ParamType::Set(s) => Ok(ParamType::Set(s.clone())),
            ParamType::NonemptySet(s) => Ok(ParamType::NonemptySet(s.clone())),
            ParamType::FiniteSet(s) => Ok(ParamType::FiniteSet(s.clone())),
            ParamType::Obj(obj) => Ok(ParamType::Obj(self.inst_obj_rec(obj, param_to_arg_map)?)),
        }
    }

    pub(crate) fn inst_typed_parameter_list(
        &mut self,
        list: &TypedParameterList,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<TypedParameterList, InstError> {
        let mut groups = Vec::with_capacity(list.groups.len());
        for group in &list.groups {
            groups.push(crate::new_pipeline::ast::param::TypedParameterGroup {
                params: group.params.clone(),
                param_type: self.inst_param_type(&group.param_type, param_to_arg_map)?,
            });
        }
        Ok(TypedParameterList { groups })
    }

    pub(crate) fn inst_set_bound_parameter_list(
        &mut self,
        list: &SetBoundParameterList,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<SetBoundParameterList, InstError> {
        let mut groups = Vec::with_capacity(list.groups.len());
        for group in &list.groups {
            groups.push(crate::new_pipeline::ast::param::SetBoundParameterGroup {
                params: group.params.clone(),
                param_type: Box::new(self.inst_obj_rec(&group.param_type, param_to_arg_map)?),
            });
        }
        Ok(SetBoundParameterList { groups })
    }
}

pub fn typed_param_bound_names(list: &TypedParameterList) -> Vec<BoundName> {
    let mut names = Vec::new();
    for group in &list.groups {
        for param in &group.params {
            names.push(param.clone());
        }
    }
    names
}

pub fn typed_param_ids(list: &TypedParameterList) -> Vec<IdentifierId> {
    list.ordered_param_ids()
}

impl Runtime {
    pub(crate) fn inst_typed_parameter_list_under_binders(
        &mut self,
        list: &TypedParameterList,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<TypedParameterList, InstError> {
        let ids = typed_param_ids(list);
        let shadowed = capture::shadow_binder_ids(param_to_arg_map, &ids);
        self.inst_typed_parameter_list(list, &shadowed)
    }
}
