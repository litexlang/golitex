use crate::fact::PlainExistFact;
use crate::prelude::*;
use crate::verify_rewrite::VerifyState;

impl Runtime {
    pub fn verify_not_exist_fact_well_definedness(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState,
    ) -> Result<ExistFactWellDefinedProof, RuntimeError> {
        self.verify_exist_fact_well_definedness(fact, verify_state)
    }
}
