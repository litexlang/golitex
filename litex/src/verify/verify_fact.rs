use crate::error::VerifyError;
use crate::execute::Runtime;
use crate::fact::ExistOrAndChainAtomicFact;
use crate::fact::Fact;
use crate::result::NonErrStmtExecResult;
use crate::verify::VerifyState;
use std::result::Result;

impl<'a> Runtime<'a> {
    pub fn verify_fact(
        &mut self,
        fact: &Fact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.verify_atomic_fact(atomic_fact, verify_state),
            Fact::AndFact(and_fact) => self.verify_and_fact(and_fact, verify_state),
            Fact::ChainFact(chain_fact) => self.verify_chain_fact(chain_fact, verify_state),
            Fact::ForallFact(forall_fact) => self.verify_forall_fact(forall_fact, verify_state),
            Fact::ForallFactWithIff(forall_fact_with_iff) => {
                self.verify_forall_fact_with_iff(forall_fact_with_iff, verify_state)
            }
            Fact::ExistFact(exists_fact) => self.verify_exist_fact(exists_fact, verify_state),
            Fact::OrFact(or_fact) => self.verify_or_fact(or_fact, verify_state),
        }
    }
}

impl<'a> Runtime<'a> {
    pub fn verify_exist_or_and_chain_atomic_fact(
        &mut self,
        exist_or_and_chain_atomic_fact: &ExistOrAndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        match exist_or_and_chain_atomic_fact {
            ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => {
                self.verify_atomic_fact(atomic_fact, verify_state)
            }
            ExistOrAndChainAtomicFact::AndFact(and_fact) => {
                self.verify_and_fact(and_fact, verify_state)
            }
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => {
                self.verify_chain_fact(chain_fact, verify_state)
            }
            ExistOrAndChainAtomicFact::OrFact(or_fact) => {
                self.verify_or_fact(or_fact, verify_state)
            }
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => {
                self.verify_exist_fact(exist_fact, verify_state)
            }
        }
    }
}
