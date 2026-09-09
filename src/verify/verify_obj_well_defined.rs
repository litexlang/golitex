use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub enum WellDefinednessProofOfObj2 {
    // Variants should match the fields of the Obj enum.
    // Example:
    Add(WellDefinednessProofOfAddObj2),
    // ...
}

pub struct WellDefinednessProofOfAddObj2 {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}

impl Runtime {
    pub fn verify_obj_well_definedness2(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState2,
    ) -> Result<WellDefinednessProofOfObj2, RuntimeError> {
        let _ = (obj, verify_state);
        todo!("verify object well-definedness")
    }
}
