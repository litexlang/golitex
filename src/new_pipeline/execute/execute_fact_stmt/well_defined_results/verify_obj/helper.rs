use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use crate::new_pipeline::ast::obj::{AnonymousFn, Obj};
use crate::new_pipeline::ast::param::{
    ParamType, SetBoundParameterList, TypedParameterGroup, TypedParameterList,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

impl Runtime {
    pub(super) fn verify_objs_as_children(
        &mut self,
        objs: &[&Obj],
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let mut child_obj_well_defined = Vec::new();
        for obj in objs {
            child_obj_well_defined.push((
                (*obj).clone(),
                self.verify_obj_well_definedness(obj, verify_state.clone())?,
            ));
        }
        Ok(ObjWellDefinedByDefCommonStages::from_children(
            child_obj_well_defined,
        ))
    }

    pub(super) fn verify_boxed_objs_as_children(
        &mut self,
        objs: &[Box<Obj>],
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let refs: Vec<&Obj> = objs.iter().map(|o| o.as_ref()).collect();
        self.verify_objs_as_children(&refs, verify_state)
    }

    pub(super) fn verify_unary_obj_well_definedness_by_def(
        &mut self,
        arg: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_objs_as_children(&[arg], verify_state)
    }

    pub(super) fn verify_binary_obj_well_definedness_by_def(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_objs_as_children(&[left, right], verify_state)
    }

    pub(super) fn with_requirements(
        &self,
        proof: ObjWellDefinedByDefCommonStages,
        requirement_fact_verified: Vec<VerifyFactResult>,
    ) -> ObjWellDefinedByDefCommonStages {
        proof.with_requirements(requirement_fact_verified)
    }
}

pub(super) fn set_bound_parameters_to_typed_parameter_list(
    list: &SetBoundParameterList,
) -> TypedParameterList {
    TypedParameterList {
        groups: list
            .groups
            .iter()
            .map(|group| TypedParameterGroup {
                params: group.params.clone(),
                param_type: ParamType::Obj(group.param_type.as_ref().clone()),
            })
            .collect(),
    }
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
            }
            i += 1;
        }
    }
    map
}

// True when `equal_to` is exactly one of the anonymous fn's bound parameters.
pub(super) fn anonymous_fn_body_is_bound_param(value: &AnonymousFn) -> bool {
    let Obj::Identifier(crate::new_pipeline::ast::obj::IdentifierObj::Plain { id, .. }) =
        value.equal_to.as_ref()
    else {
        return false;
    };
    for group in &value.body.set_bound_parameters.groups {
        for param in &group.params {
            if param.id == *id {
                return true;
            }
        }
    }
    false
}
