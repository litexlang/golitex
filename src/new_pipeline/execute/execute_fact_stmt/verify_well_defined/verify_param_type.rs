use super::VerifyObjResult;
use crate::new_pipeline::ast::param::{ParamType, TypedParameterList};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// WD of one parameter-type annotation (not a Fact).
pub enum ParamTypeWellDefinedProof {
    Set,
    NonemptySet,
    FiniteSet,
    Obj(VerifyObjResult),
}

impl Runtime {
    // One entry per TypedParameterGroup, in source order.
    pub fn verify_typed_parameters_well_definedness(
        &mut self,
        typed_parameters: &TypedParameterList,
        verify_state: VerifyState,
    ) -> RuntimeResult<Vec<ParamTypeWellDefinedProof>> {
        let mut out = Vec::new();
        for group in &typed_parameters.groups {
            out.push(
                self.verify_param_type_well_definedness(&group.param_type, verify_state.clone())?,
            );
        }
        Ok(out)
    }

    pub fn verify_param_type_well_definedness(
        &mut self,
        param_type: &ParamType,
        verify_state: VerifyState,
    ) -> RuntimeResult<ParamTypeWellDefinedProof> {
        match param_type {
            ParamType::Set(_) => Ok(ParamTypeWellDefinedProof::Set),
            ParamType::NonemptySet(_) => Ok(ParamTypeWellDefinedProof::NonemptySet),
            ParamType::FiniteSet(_) => Ok(ParamTypeWellDefinedProof::FiniteSet),
            ParamType::Obj(obj) => Ok(ParamTypeWellDefinedProof::Obj(
                self.verify_obj_well_definedness(obj, verify_state)?,
            )),
        }
    }
}
