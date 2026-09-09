use crate::fact::PlainExistFact;
use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

impl Runtime {
    pub fn verify_plain_exist_fact_well_definedness2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<ExistFactWellDefinedProof2, RuntimeError> {
        self.verify_exist_fact_well_definedness2(fact, verify_state)
    }
}
