use crate::prelude::*;
use std::result::Result;

impl Runtime {
    pub fn verify_and_fact(
        &mut self,
        and_fact: &AndFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&Fact::AndFact(and_fact.clone()))
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_and_fact_well_defined(and_fact, verify_state) {
                return Err(VerifyError::new(
                    Fact::AndFact(and_fact.clone()),
                    String::new(),
                    and_fact.line_file(),
                    Some(RuntimeError::WellDefinedError(e)),
                ));
            }
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        let mut verify_what = Vec::with_capacity(and_fact.facts.len());
        for fact in &and_fact.facts {
            let result = self.verify_atomic_fact(fact, &verify_state_for_children)?;
            if result.is_unknown() {
                return Ok(result);
            }
            verify_what.push(fact.to_string());
        }
        Ok(NonErrStmtExecResult::FactVerifiedByFact(
            FactVerifiedByFact::new(
                Fact::AndFact(and_fact.clone()),
                format!("{} are verified", verify_what.join(", ")),
                InferResult::new(),
                DEFAULT_LINE_FILE.clone(),
            ),
        ))
    }

    pub fn verify_chain_fact(
        &mut self,
        chain_fact: &ChainFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&Fact::ChainFact(chain_fact.clone()))
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_chain_fact_well_defined(chain_fact, verify_state) {
                return Err(VerifyError::new(
                    Fact::ChainFact(chain_fact.clone()),
                    String::new(),
                    chain_fact.line_file(),
                    Some(RuntimeError::WellDefinedError(e)),
                ));
            }
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        let facts = chain_fact.facts().map_err(|e| {
            VerifyError::new(
                Fact::ChainFact(chain_fact.clone()),
                String::new(),
                Fact::ChainFact(chain_fact.clone()).line_file(),
                Some(RuntimeError::NewAtomicFactError(e)),
            )
        })?;
        let mut verify_what = Vec::with_capacity(facts.len());
        for fact in &facts {
            let result = self.verify_atomic_fact(fact, &verify_state_for_children)?;
            if result.is_unknown() {
                return Ok(result);
            }

            verify_what.push(fact.to_string());
        }
        Ok(NonErrStmtExecResult::FactVerifiedByFact(
            FactVerifiedByFact::new(
                Fact::ChainFact(chain_fact.clone()),
                format!("{} are verified", verify_what.join(", ")),
                InferResult::new(),
                DEFAULT_LINE_FILE.clone(),
            ),
        ))
    }
}
