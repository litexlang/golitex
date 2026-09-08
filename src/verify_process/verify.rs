use crate::prelude::*;

impl Runtime {
    pub fn execute_fact_statement(
        &mut self,
        fact: &Fact,
    ) -> Result<ExecFactStmtResult, RuntimeError> {
        let verify_state = self.current_verify_state();
        let verify_result = self.verify_fact(fact, verify_state)?;
        let store_and_infer_result = self.store_and_infer_fact(fact)?;
        Ok(ExecFactStmtResult {
            verify_result,
            store_and_infer_result,
        })
    }

    pub fn verify_fact(
        &mut self,
        fact: &Fact,
        verify_state: VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        match fact {
            Fact::AtomicFact(fact) => Ok(VerifyFactResult::AtomicFact(
                self.verify_atomic_fact(fact, verify_state)?,
            )),
            Fact::ExistFact(fact) => Ok(VerifyFactResult::ExistFact(
                self.verify_exist_fact(fact, verify_state)?,
            )),
            Fact::OrFact(fact) => Ok(VerifyFactResult::OrFact(
                self.verify_or_fact(fact, verify_state)?,
            )),
            Fact::AndFact(fact) => Ok(VerifyFactResult::AndFact(
                self.verify_and_fact(fact, verify_state)?,
            )),
            Fact::ChainFact(fact) => Ok(VerifyFactResult::ChainFact(
                self.verify_chain_fact(fact, verify_state)?,
            )),
            Fact::ForallFact(fact) => Ok(VerifyFactResult::ForallFact(
                self.verify_forall_fact(fact, verify_state)?,
            )),
            Fact::ForallFactWithIff(fact) => Ok(VerifyFactResult::ForallFactWithIff(
                self.verify_forall_fact_with_iff(fact, verify_state)?,
            )),
            Fact::NotForall(fact) => Ok(VerifyFactResult::NotForall(
                self.verify_not_forall_fact(fact, verify_state)?,
            )),
        }
    }

    pub fn verify_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<VerifyAtomicFactResult, RuntimeError> {
        match fact {
            AtomicFact::EqualFact(equal_fact) => Ok(VerifyAtomicFactResult::Equality(
                self.verify_equal_fact(equal_fact, verify_state)?,
            )),
            _ => Ok(VerifyAtomicFactResult::NonEquationalAtomicFact(
                self.verify_non_equational_atomic_fact(fact, verify_state)?,
            )),
        }
    }
}
