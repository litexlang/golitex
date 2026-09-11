use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
use crate::new_pipeline::runtime::runtime_ids::WellDefinednessId;
use crate::prelude::*;

use super::verify_fact_result::VerifyFactResult2;
use super::VerifyState2;

pub enum WellDefinednessProofOfObj2 {
    ByReuse(WellDefinednessId),
    ByTrivial,
    ByAddDef(WellDefinednessProofOfAddObj2),
}

pub struct WellDefinednessProofOfAddObj2 {
    pub well_defined_of_left: Box<WellDefinednessProofOfObj2>,
    pub well_defined_of_right: Box<WellDefinednessProofOfObj2>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}

impl Runtime {
    pub fn verify_obj_well_definedness2(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState2,
    ) -> RuntimeResult<WellDefinednessProofOfObj2> {
        let _ = &verify_state;

        match obj {
            Obj::Number(_)
            | Obj::ImaginaryUnit(_)
            | Obj::EulerNumber(_)
            | Obj::Pi(_)
            | Obj::StandardSet(_)
            | Obj::Atom(_) => Ok(WellDefinednessProofOfObj2::ByTrivial),
            Obj::Add(add) => self.verify_add_obj_well_definedness2(add, verify_state),
            _ => Err(RuntimeError::Unknown(
                "object well-definedness for this Obj variant is not wired yet".to_string(),
            )),
        }
    }

    fn verify_add_obj_well_definedness2(
        &mut self,
        add: &Add,
        verify_state: VerifyState2,
    ) -> RuntimeResult<WellDefinednessProofOfObj2> {
        let _ = (add, verify_state);
        Err(RuntimeError::Unknown(
            "well-definedness for Add is not wired yet".to_string(),
        ))
    }
}
