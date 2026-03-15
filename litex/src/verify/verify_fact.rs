use crate::error::StmtError;
use crate::fact::Fact;
use crate::result::{FactVerifiedByFact, NonErrStmtResult};
use crate::verify::VerifyState;
use std::result::Result;
use crate::error::VerifyError;
use crate::execute::Executor;

impl<'a> Executor<'a> {
    pub fn verify_fact(&mut self, fact: &Fact, verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_fact_well_defined(fact, verify_state) {
                return Err(VerifyError::new(fact.to_string(), vec![StmtError::WellDefinedError(e)], fact.line_file()));
            }
        }

        if let Some(cached_result) = self.verify_fact_from_cache(fact) {
            return Ok(cached_result);
        }
        
        let next_verify_state = verify_state.new_state_with_req_ok_set_to_true();

        let result = match fact {
            Fact::AtomicFact(atomic_fact) => self.verify_atomic_fact(atomic_fact, &next_verify_state),
            Fact::AndFact(and_fact) => self.verify_and_fact(and_fact, &next_verify_state),
            Fact::ChainFact(chain_fact) => self.verify_chain_fact(chain_fact, &next_verify_state),
            Fact::ForallFact(forall_fact) => self.verify_forall_fact(forall_fact, &next_verify_state),
            Fact::ForallFactWithIff(forall_fact_with_iff) => self.verify_forall_fact_with_iff(forall_fact_with_iff, &next_verify_state),
            Fact::ExistFact(exists_fact) => self.verify_exist_fact(exists_fact, &next_verify_state),
            Fact::OrFact(or_fact) => self.verify_or_fact(or_fact, &next_verify_state),
        }?;

        Ok(result)
    }

    fn verify_fact_from_cache(&self, fact: &Fact) -> Option<NonErrStmtResult> {
        let key = fact.to_string();
        let (cache_ok, cache_line_file) = self.runtime_context.cache_known_or_and_atomic_fact_contains(&key);
        if cache_ok {
            Some(NonErrStmtResult::FactVerifiedByFact(FactVerifiedByFact::new(
                key,
                fact.to_string(),
                cache_line_file,
            )))
        } else {
            None
        }
    }
    
}