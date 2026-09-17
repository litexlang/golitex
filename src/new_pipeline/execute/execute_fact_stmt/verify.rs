use super::verify_fact_result::VerifyFactResult;
use super::verify_forall_fact_with_iff::forall_fact_with_iff_result_from_search_fail;
use super::verify_not_forall_fact::not_forall_fact_result_from_search_fail;
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
            Fact::AndFact(fact) => self.verify_and_fact(fact, verify_state),
            Fact::ChainFact(fact) => self.verify_chain_fact(fact, verify_state),
            Fact::OrFact(fact) => self.verify_or_fact(fact, verify_state),
            Fact::ExistFact(fact) => self.verify_exist_fact(fact, verify_state),
            Fact::ForallFact(fact) => self.verify_forall_fact(fact, verify_state),
            Fact::ForallFactWithIff(fact) => {
                match self.verify_forall_fact_with_iff(fact, verify_state)? {
                    Some(r) => Ok(VerifyFactResult::ForallFactWithIff(Box::new(r))),
                    None => Ok(forall_fact_with_iff_result_from_search_fail()),
                }
            }
            Fact::NotForall(fact) => match self.verify_not_forall_fact(fact, verify_state)? {
                Some(r) => Ok(VerifyFactResult::NotForall(Box::new(r))),
                None => Ok(not_forall_fact_result_from_search_fail()),
            },
        }
    }
}
