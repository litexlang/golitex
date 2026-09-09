use crate::prelude::*;

pub enum WellDefinednessProofOfObj {
    // Variants should match the fields of the Obj enum.
    // Example:
    Add(WellDefinednessProofOfAddObj),
    // ...
}

pub struct WellDefinednessProofOfAddObj {
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

impl Runtime {
    pub fn verify_obj_well_definedness(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> Result<WellDefinednessProofOfObj, RuntimeError> {
        let _ = (obj, verify_state);
        todo!("verify object well-definedness")
    }
}
