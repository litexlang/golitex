use super::verify_fact_result::{
    VerifyAndFactResult, VerifyChainFactResult, VerifyExistFactResult,
    VerifyFactResult, VerifyForallFactResult, VerifyForallFactWithIffResult,
    VerifyNotForallFactResult, VerifyOrFactResult,
};
use super::VerifyState;
use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn verify_fact(
        &mut self,
        fact: &Fact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        // Exact FactIR ByCache applies to every closed Fact shape.
        if !matches!(fact, Fact::AtomicFact(_)) {
            if let Some(cache) = self.search_fact_proof_by_cache(fact) {
                return Ok(match fact {
                    Fact::AndFact(_) => VerifyFactResult::AndFact(Box::new(
                        VerifyAndFactResult::ByCache(cache),
                    )),
                    Fact::ChainFact(_) => VerifyFactResult::ChainFact(Box::new(
                        VerifyChainFactResult::ByCache(cache),
                    )),
                    Fact::OrFact(_) => {
                        VerifyFactResult::OrFact(Box::new(VerifyOrFactResult::ByCache(cache)))
                    }
                    Fact::ExistFact(_) => VerifyFactResult::ExistFact(Box::new(
                        VerifyExistFactResult::ByCache(cache),
                    )),
                    Fact::ForallFact(_) => VerifyFactResult::ForallFact(Box::new(
                        VerifyForallFactResult::ByCache(cache),
                    )),
                    Fact::ForallFactWithIff(_) => VerifyFactResult::ForallFactWithIff(Box::new(
                        VerifyForallFactWithIffResult::ByCache(cache),
                    )),
                    Fact::NotForall(_) => VerifyFactResult::NotForall(Box::new(
                        VerifyNotForallFactResult::ByCache(cache),
                    )),
                    Fact::AtomicFact(_) => unreachable!(),
                });
            }
        }

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
