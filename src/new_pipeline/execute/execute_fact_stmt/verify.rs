use super::verify_fact_result::VerifyFactResult;
use super::VerifyState;
use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn verify_fact(
        &mut self,
        fact: &Fact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        match fact {
            Fact::AtomicFact(fact) => self.verify_atomic_fact(fact, verify_state),
            Fact::AndFact(fact) => Ok(VerifyFactResult::AndFact(Box::new(
                self.verify_and_fact(fact, verify_state)?,
            ))),
            Fact::ChainFact(fact) => Ok(VerifyFactResult::ChainFact(Box::new(
                self.verify_chain_fact(fact, verify_state)?,
            ))),
            Fact::OrFact(fact) => Ok(VerifyFactResult::OrFact(Box::new(
                self.verify_or_fact(fact, verify_state)?,
            ))),
            Fact::ExistFact(fact) => Ok(VerifyFactResult::ExistFact(Box::new(
                self.verify_exist_fact(fact, verify_state)?,
            ))),
            Fact::ForallFact(fact) => Ok(VerifyFactResult::ForallFact(Box::new(
                self.verify_forall_fact(fact, verify_state)?,
            ))),
            Fact::ForallFactWithIff(fact) => Ok(VerifyFactResult::ForallFactWithIff(Box::new(
                self.verify_forall_fact_with_iff(fact, verify_state)?,
            ))),
            Fact::NotForall(fact) => Ok(VerifyFactResult::NotForall(Box::new(
                self.verify_not_forall_fact(fact, verify_state)?,
            ))),
        }
    }
}
