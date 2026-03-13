use crate::error::StmtError;
use crate::fact::Fact;
use crate::result::{FactVerifiedByFact, NonErrStmtResult};
use crate::verify::VerifyState;
use std::result::Result;
use crate::error::VerifyError;
use crate::execute::Executor;

impl<'a> Executor<'a> {
    pub fn verify_fact(&mut self, fact: &Fact, verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        // 如果 cache 里写过这个fact是ok的，那就OK了
        let key = fact.to_string();
        if self.runtime_context.cache_well_defined_obj_contains(&key) {
            return Ok(NonErrStmtResult::FactVerifiedByFact(FactVerifiedByFact::new(fact.to_string(), "fact is well-defined".to_string(), fact.line_file())));
        }
        
        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_fact_well_defined(fact, verify_state) {
                return Err(VerifyError::new(fact.to_string().as_str(), vec![StmtError::WellDefinedError(e)], fact.line_file()));
            }
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

        if result.is_true() {
            self.runtime_context.top_level_env().cache_well_defined_obj.insert(key, ());
        }

        Ok(result)
    }
}