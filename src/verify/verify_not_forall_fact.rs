use crate::prelude::*;
use std::result::Result;

impl Runtime {
    pub fn verify_not_forall_fact(
        &mut self,
        not_forall: &NotForallFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if !verify_state.well_defined_already_verified {
            self.verify_not_forall_fact_well_defined(not_forall, verify_state)?;
        }

        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&not_forall.clone().into())
        {
            return Ok(cached_result);
        }

        Ok(StmtUnknown::new().into())
    }
}
