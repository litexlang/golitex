use crate::prelude::*;
use std::result::Result;

impl Runtime {
    pub fn verify_forall_fact_with_iff(
        &mut self,
        forall_iff: &ForallFactWithIff,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&forall_iff.clone().into())
        {
            return Ok(cached_result);
        }

        let (forall_then_implies_iff, forall_iff_implies_then) =
            forall_iff.to_two_forall_facts()?;
        let verification_steps = [&forall_then_implies_iff, &forall_iff_implies_then];
        for forall_step in verification_steps {
            let result = self.verify_forall_fact(forall_step, verify_state)?;
            if result.is_unknown() {
                return Ok(result);
            }
        }

        Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
            forall_iff.clone().into(),
            VerifiedByResult::wrap_bys(vec![VerifiedByResult::Fact(
                forall_iff.clone().into(),
                "forall iff: then=>iff and iff=>then verified".to_string(),
            )]),
            Vec::new(),
        ))
        .into())
    }
}
