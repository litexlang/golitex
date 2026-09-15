use crate::new_pipeline::runtime::runtime_ids::WellDefinednessId;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
use crate::prelude::*;

use super::verify_fact_result::VerifyFactResult;
use super::VerifyState;

pub enum WellDefinednessProofOfObj {
    ByReuse(WellDefinednessId),
    ByTrivial,
    ByAddDef(WellDefinednessProofOfAddObj),
}

pub struct WellDefinednessProofOfAddObj {
    pub well_defined_of_left: Box<WellDefinednessProofOfObj>,
    pub well_defined_of_right: Box<WellDefinednessProofOfObj>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

impl Runtime {
    pub fn verify_draft_obj_well_definedness(
        &mut self,
        obj: &Obj,
        _verify_state: VerifyState,
    ) -> RuntimeResult<WellDefinednessProofOfObj> {

        match obj {
            Obj::Number(_)
            | Obj::ImaginaryUnit(_)
            | Obj::EulerNumber(_)
            | Obj::Pi(_)
            | Obj::StandardSet(_)
            | Obj::Atom(_) => Ok(WellDefinednessProofOfObj::ByTrivial),
            Obj::Add(add) => self.verify_add_obj_well_definedness(add, _verify_state),
            _ => Err(RuntimeError::Unknown(
                "object well-definedness for this Obj variant is not wired yet".to_string(),
            )),
        }
    }

    fn verify_add_obj_well_definedness(
        &mut self,
        _add: &Add,
        _verify_state: VerifyState,
    ) -> RuntimeResult<WellDefinednessProofOfObj> {
        Err(RuntimeError::Unknown(
            "well-definedness for Add is not wired yet".to_string(),
        ))
    }
}
