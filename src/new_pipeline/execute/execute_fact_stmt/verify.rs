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
            Fact::AndFact(fact) => match self.verify_and_fact(fact, verify_state)? {
                Some(r) => Ok(VerifyFactResult::AndFact(Box::new(r))),
                None => Ok(VerifyFactResult::FailToSearchProof),
            },
            Fact::ChainFact(fact) => match self.verify_chain_fact(fact, verify_state)? {
                Some(r) => Ok(VerifyFactResult::ChainFact(Box::new(r))),
                None => Ok(VerifyFactResult::FailToSearchProof),
            },
            Fact::OrFact(fact) => match self.verify_or_fact(fact, verify_state)? {
                Some(r) => Ok(VerifyFactResult::OrFact(Box::new(r))),
                None => Ok(VerifyFactResult::FailToSearchProof),
            },
            Fact::ExistFact(fact) => match self.verify_exist_fact(fact, verify_state)? {
                Some(r) => Ok(VerifyFactResult::ExistFact(Box::new(r))),
                None => Ok(VerifyFactResult::FailToSearchProof),
            },
            Fact::ForallFact(fact) => match self.verify_forall_fact(fact, verify_state)? {
                Some(r) => Ok(VerifyFactResult::ForallFact(Box::new(r))),
                None => Ok(VerifyFactResult::FailToSearchProof),
            },
            Fact::ForallFactWithIff(fact) => {
                match self.verify_forall_fact_with_iff(fact, verify_state)? {
                    Some(r) => Ok(VerifyFactResult::ForallFactWithIff(Box::new(r))),
                    None => Ok(VerifyFactResult::FailToSearchProof),
                }
            }
            Fact::NotForall(fact) => match self.verify_not_forall_fact(fact, verify_state)? {
                Some(r) => Ok(VerifyFactResult::NotForall(Box::new(r))),
                None => Ok(VerifyFactResult::FailToSearchProof),
            },
        }
    }
}
