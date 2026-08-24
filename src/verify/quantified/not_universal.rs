//! Verification for negated universal facts.

use crate::prelude::*;
use std::result::Result;

impl Runtime {
    pub fn verify_not_forall_fact(
        &mut self,
        not_forall: &NotForallFact,
        verify_state: &ProofSearchState,
    ) -> Result<StmtResult, RuntimeError> {
        if !verify_state.well_definedness_verified {
            self.verify_not_forall_fact_well_defined(not_forall, verify_state)?;
        }

        if let Some(cached_result) =
            self.verification_result_from_known_fact_cache(&not_forall.clone().into())
        {
            return Ok(cached_result);
        }

        Ok(UnknownGenericStmtResult::new().into())
    }
}
