use crate::prelude::*;
use crate::new_pipeline::execute_fact_stmt::VerifyState2;

impl Runtime {
    pub fn execute_fact_statement2(
        &mut self,
        fact: &Fact,
    ) -> Result<ExecFactStmtResult2, RuntimeError> {
        let verify_state = VerifyState2 {
            can_use_forall_fact: true,
            can_use_known_algebraic_rewrite: true,
        };
        let verify_result = self.verify_fact2(fact, verify_state)?;
        let store_and_infer_result = self.store_fact_then_infer(verify_result)?;
        Ok(ExecFactStmtResult2 {
            verify_result,
            store_and_infer_result,
        })
    }

    pub fn verify_fact2(
        &mut self,
        fact: &Fact,
        verify_state: VerifyState2,
    ) -> Result<VerifyFactResult2, RuntimeError> {
        match fact {
            Fact::AtomicFact(fact) => Ok(VerifyFactResult2::AtomicFact(
                self.verify_atomic_fact2(fact, verify_state)?,
            )),
            Fact::ExistFact(fact) => Ok(VerifyFactResult2::ExistFact(
                self.verify_exist_fact2(fact, verify_state)?,
            )),
            Fact::OrFact(fact) => Ok(VerifyFactResult2::OrFact(
                self.verify_or_fact2(fact, verify_state)?,
            )),
            Fact::AndFact(fact) => Ok(VerifyFactResult2::AndFact(
                self.verify_and_fact2(fact, verify_state)?,
            )),
            Fact::ChainFact(fact) => Ok(VerifyFactResult2::ChainFact(
                self.verify_chain_fact2(fact, verify_state)?,
            )),
            Fact::ForallFact(fact) => Ok(VerifyFactResult2::ForallFact(
                self.verify_forall_fact2(fact, verify_state)?,
            )),
            Fact::ForallFactWithIff(fact) => Ok(VerifyFactResult2::ForallFactWithIff(
                self.verify_forall_fact_with_iff2(fact, verify_state)?,
            )),
            Fact::NotForall(fact) => Ok(VerifyFactResult2::NotForall(
                self.verify_not_forall_fact2(fact, verify_state)?,
            )),
        }
    }

    pub fn verify_atomic_fact2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<VerifyAtomicFactResult2, RuntimeError> {
        match fact {
            AtomicFact::EqualFact(equal_fact) => Ok(VerifyAtomicFactResult2::Equality(
                self.verify_equal_fact2(equal_fact, verify_state)?,
            )),
            _ => Ok(VerifyAtomicFactResult2::NonEquationalAtomicFact(
                self.verify_non_equational_atomic_fact2(fact, verify_state)?,
            )),
        }
    }
}
