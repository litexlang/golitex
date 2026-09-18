use super::entry::ObjWellDefinedProofByDef;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::param::{
    ParamType, SetBoundParameterList, TypedParameterGroup, TypedParameterList,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn verify_objs_as_children(
        &mut self,
        objs: &[&Obj],
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let mut child_obj_well_defined = Vec::new();
        for obj in objs {
            child_obj_well_defined.push((
                (*obj).clone(),
                self.verify_obj_well_definedness(obj, verify_state.clone())?,
            ));
        }
        Ok(ObjWellDefinedProofByDef::from_children(
            child_obj_well_defined,
        ))
    }

    pub(super) fn verify_boxed_objs_as_children(
        &mut self,
        objs: &[Box<Obj>],
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let refs: Vec<&Obj> = objs.iter().map(|o| o.as_ref()).collect();
        self.verify_objs_as_children(&refs, verify_state)
    }

    pub(super) fn verify_unary_obj_well_definedness_by_def(
        &mut self,
        arg: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(&[arg], verify_state)
    }

    pub(super) fn verify_binary_obj_well_definedness_by_def(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(&[left, right], verify_state)
    }

    pub(super) fn with_requirements(
        &self,
        mut proof: ObjWellDefinedProofByDef,
        requirement_fact_verified: Vec<
            crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult,
        >,
    ) -> ObjWellDefinedProofByDef {
        proof.requirement_fact_verified = requirement_fact_verified;
        proof
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
