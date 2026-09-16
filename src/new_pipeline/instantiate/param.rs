use std::collections::HashMap;

use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::param::{ParamType, SetBoundParameterList, TypedParameterList};
use crate::new_pipeline::runtime::Runtime;

use super::capture;
use super::error::InstError;

impl Runtime {
    pub(crate) fn inst_param_type(
        &mut self,
        param_type: &ParamType,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<ParamType, InstError> {
        match param_type {
            ParamType::Set(s) => Ok(ParamType::Set(s.clone())),
            ParamType::NonemptySet(s) => Ok(ParamType::NonemptySet(s.clone())),
            ParamType::FiniteSet(s) => Ok(ParamType::FiniteSet(s.clone())),
            ParamType::Obj(obj) => Ok(ParamType::Obj(
                self.inst_obj_rec(obj, param_to_arg_map, fresh, binder_renames)?,
            )),
        }
    }

    pub(crate) fn inst_typed_parameter_list(
        &mut self,
        list: &TypedParameterList,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<TypedParameterList, InstError> {
        let mut groups = Vec::with_capacity(list.groups.len());
        for group in &list.groups {
            groups.push(crate::new_pipeline::ast::param::TypedParameterGroup {
                params: group.params.clone(),
                param_type: self.inst_param_type(
                    &group.param_type,
                    param_to_arg_map,
                    fresh,
                    binder_renames,
                )?,
            });
        }
        Ok(TypedParameterList { groups })
    }

    pub(crate) fn inst_set_bound_parameter_list(
        &mut self,
        list: &SetBoundParameterList,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<SetBoundParameterList, InstError> {
        let mut groups = Vec::with_capacity(list.groups.len());
        for group in &list.groups {
            groups.push(crate::new_pipeline::ast::param::SetBoundParameterGroup {
                params: group.params.clone(),
                param_type: Box::new(self.inst_obj_rec(
                    &group.param_type,
                    param_to_arg_map,
                    fresh,
                    binder_renames,
                )?),
            });
        }
        Ok(SetBoundParameterList { groups })
    }
}

pub fn typed_param_names(list: &TypedParameterList) -> Vec<String> {
    let mut names = Vec::new();
    for group in &list.groups {
        for param in &group.params {
            names.push(param.clone());
        }
    }
    names
}

impl Runtime {
    pub(crate) fn inst_typed_parameter_list_under_binders(
        &mut self,
        list: &TypedParameterList,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<TypedParameterList, InstError> {
        let names = typed_param_names(list);
        let binders = capture::prepare_binders(names.as_slice(), param_to_arg_map, fresh);
        let (shadowed, new_renames) =
            capture::shadowed_subst_and_renames(param_to_arg_map, binder_renames, &binders);
        self.inst_typed_parameter_list(list, &shadowed, fresh, &new_renames)
    }
}
