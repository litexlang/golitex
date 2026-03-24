use crate::error::StmtError;
use crate::error::VerifyError;
use crate::execute::Runtime;
use crate::fact::AtomicFact;
use crate::result::NonErrStmtExecResult;
use crate::verify::VerifyState;

impl<'a> Runtime<'a> {
    pub fn verify_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&fact.to_string(), fact.line_file())
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_atomic_fact_well_defined(fact, verify_state) {
                return Err(VerifyError::new(
                    fact.to_string(),
                    Some(StmtError::WellDefinedError(e)),
                    fact.line_file(),
                ));
            }
        }

        let next_verify_state = verify_state.make_state_with_req_ok_set_to_true();

        match fact {
            AtomicFact::EqualFact(equal_fact) => {
                self.verify_equal_fact(equal_fact, &next_verify_state)
            }
            _ => self.verify_non_equational_atomic_fact(
                fact,
                &next_verify_state,
                Some(fact.calculate_args()),
            ),
        }
    }
}
