use crate::prelude::*;

impl Runtime {
    pub fn verify_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&Fact::AtomicFact(fact.clone()))
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_atomic_fact_well_defined(fact, verify_state) {
                return Err(RuntimeError::new_verify_error_with_fact_msg_position_previous_error(
                    Fact::AtomicFact(fact.clone()),
                    String::new(),
                    fact.line_file(),
                    Some(e.into()),
                ));
            }
        }

        let next_verify_state = verify_state.make_state_with_req_ok_set_to_true();

        match fact {
            AtomicFact::EqualFact(equal_fact) => {
                self.verify_equal_fact(equal_fact, &next_verify_state)
            }
            _ => self.verify_non_equational_atomic_fact(fact, &next_verify_state),
        }
    }
}
