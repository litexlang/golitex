use crate::prelude::*;
use std::result::Result;

impl Runtime {
    pub fn verify_fact_return_err_if_not_true(
        &mut self,
        fact: &Fact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let result = match fact {
            Fact::AtomicFact(atomic_fact) => self.verify_atomic_fact(atomic_fact, verify_state),
            Fact::AndFact(and_fact) => self.verify_and_fact(and_fact, verify_state),
            Fact::ChainFact(chain_fact) => self.verify_chain_fact(chain_fact, verify_state),
            Fact::ForallFact(forall_fact) => self.verify_forall_fact(forall_fact, verify_state),
            Fact::ForallFactWithIff(forall_fact_with_iff) => {
                self.verify_forall_fact_with_iff(forall_fact_with_iff, verify_state)
            }
            Fact::ExistFact(exists_fact) => self.verify_exist_fact(exists_fact, verify_state),
            Fact::OrFact(or_fact) => self.verify_or_fact(or_fact, verify_state),
        }?;

        if result.is_unknown() {
            let fact_owned = fact.clone();
            let line_file = fact_owned.line_file();
            return Err(RuntimeError::new_verify_error_with_fact_msg_position_previous_error(
                fact_owned.clone(),
                String::new(),
                line_file,
                Some(RuntimeError::new_verify_result_unknown_with_fact_previous_error(
                    fact_owned, None,
                )),
            ));
        } else {
            Ok(result)
        }
    }
}

impl Runtime {
    pub fn verify_exist_or_and_chain_atomic_fact(
        &mut self,
        exist_or_and_chain_atomic_fact: &ExistOrAndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
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

    pub fn verify_or_and_chain_atomic_fact(
        &mut self,
        or_and_chain_atomic_fact: &OrAndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        match or_and_chain_atomic_fact {
            OrAndChainAtomicFact::AtomicFact(atomic_fact) => {
                self.verify_atomic_fact(atomic_fact, verify_state)
            }
            OrAndChainAtomicFact::AndFact(and_fact) => self.verify_and_fact(and_fact, verify_state),
            OrAndChainAtomicFact::ChainFact(chain_fact) => {
                self.verify_chain_fact(chain_fact, verify_state)
            }
            OrAndChainAtomicFact::OrFact(or_fact) => self.verify_or_fact(or_fact, verify_state),
        }
    }

    pub fn verify_and_chain_atomic_fact(
        &mut self,
        and_chain_atomic_fact: &AndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        match and_chain_atomic_fact {
            AndChainAtomicFact::AtomicFact(atomic_fact) => {
                self.verify_atomic_fact(atomic_fact, verify_state)
            }
            AndChainAtomicFact::AndFact(and_fact) => self.verify_and_fact(and_fact, verify_state),
            AndChainAtomicFact::ChainFact(chain_fact) => {
                self.verify_chain_fact(chain_fact, verify_state)
            }
        }
    }
}
