use std::collections::HashMap;

use crate::ast::obj::Obj;
use crate::ast::param::{ParamType, TypedParameterList};
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::Runtime;

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
            groups.push(crate::ast::param::TypedParameterGroup {
                params: group.params.clone(),
                param_type: self.inst_param_type(&group.param_type, param_to_arg_map)?,
            });
        }
        Ok(TypedParameterList { groups })
    }
}

pub fn typed_param_ids(list: &TypedParameterList) -> Vec<IdentifierId> {
    list.ordered_param_ids()
}
