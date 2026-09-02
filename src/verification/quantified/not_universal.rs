//! Verification for negated universal facts.

use crate::prelude::*;
use std::result::Result;

impl Runtime {
    pub(crate) fn prove_not_forall_fact(
        &mut self,
        not_forall: &NotForallFact,
        _verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        if let Some(cached_result) =
            self.verification_result_from_known_fact_cache(&not_forall.clone().into())
        {
            return Ok(cached_result);
        }

        Ok(UnknownGenericStmtResult::new().into())
    }
}
