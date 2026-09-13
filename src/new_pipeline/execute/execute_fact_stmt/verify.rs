use super::verify_atomic_fact::VerifyAtomicFactResult;
use super::verify_fact_result::{
    VerifyAndFactResult, VerifyChainFactResult, VerifyExistFactResult, VerifyFactResult,
    VerifyForallFactResult, VerifyForallFactWithIffResult, VerifyNotForallFactResult,
    VerifyOrFactResult,
};
use super::VerifyState;
use crate::new_pipeline::ast::fact::{
    AndFact, AtomicFact, ChainFact, ExistFact, Fact, ForallFact, ForallFactWithIff, NotForallFact,
    OrFact,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn verify_fact(
        &mut self,
        fact: &Fact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        match fact {
            Fact::AtomicFact(fact) => Ok(VerifyFactResult::AtomicFact(Box::new(
                self.verify_atomic_fact(fact, verify_state)?,
            ))),
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

    // EqualFact → Equality; other atomics → NonEquational.
    pub fn verify_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyAtomicFactResult> {
        match fact {
            AtomicFact::EqualFact(equal_fact) => Ok(VerifyAtomicFactResult::Equality(
                self.verify_equal_fact(equal_fact, verify_state)?,
            )),
            _ => Ok(VerifyAtomicFactResult::NonEquational(
                self.verify_non_equational_fact(fact, verify_state)?,
            )),
        }
    }

    pub fn verify_and_fact(
        &mut self,
        fact: &AndFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyAndFactResult> {
        let _ = (fact, verify_state);
        Ok(VerifyAndFactResult { _wire: () })
    }

    pub fn verify_chain_fact(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyChainFactResult> {
        let _ = (fact, verify_state);
        Ok(VerifyChainFactResult { _wire: () })
    }

    pub fn verify_or_fact(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyOrFactResult> {
        let _ = (fact, verify_state);
        Ok(VerifyOrFactResult { _wire: () })
    }

    pub fn verify_exist_fact(
        &mut self,
        fact: &ExistFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyExistFactResult> {
        let _ = (fact, verify_state);
        Ok(VerifyExistFactResult { _wire: () })
    }

    pub fn verify_forall_fact(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyForallFactResult> {
        let _ = (fact, verify_state);
        Ok(VerifyForallFactResult { _wire: () })
    }

    pub fn verify_forall_fact_with_iff(
        &mut self,
        fact: &ForallFactWithIff,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyForallFactWithIffResult> {
        let _ = (fact, verify_state);
        Ok(VerifyForallFactWithIffResult { _wire: () })
    }

    pub fn verify_not_forall_fact(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyNotForallFactResult> {
        let _ = (fact, verify_state);
        Ok(VerifyNotForallFactResult { _wire: () })
    }
}
