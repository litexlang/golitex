use crate::common::defaults::DEFAULT_LINE_FILE;
use crate::error::{RuntimeError, VerifyError};
use crate::execute::Runtime;
use crate::fact::{AndFact, ChainFact};
use crate::infer::InferResult;
use crate::result::{FactVerifiedByFact, NonErrStmtExecResult};
use crate::verify::VerifyState;
use std::result::Result;

impl<'a> Runtime<'a> {
    pub fn verify_and_fact(
        &mut self,
        and_fact: &AndFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let fact_display_string = and_fact.to_string();
        let fact_line_file = and_fact.line_file();
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&fact_display_string, fact_line_file)
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_and_fact_well_defined(and_fact, verify_state) {
                return Err(VerifyError::new(
                    fact_display_string,
                    Some(RuntimeError::WellDefinedError(e)),
                    fact_line_file,
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
                fact_display_string,
                format!("{} are verified", verify_what.join(", ")),
                InferResult::new(),
                fact_line_file,
                DEFAULT_LINE_FILE.clone(),
            ),
        ))
    }

    pub fn verify_chain_fact(
        &mut self,
        chain_fact: &ChainFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let fact_display_string = chain_fact.to_string();
        let fact_line_file = chain_fact.line_file();
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&fact_display_string, fact_line_file)
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_chain_fact_well_defined(chain_fact, verify_state) {
                return Err(VerifyError::new(
                    fact_display_string,
                    Some(RuntimeError::WellDefinedError(e)),
                    fact_line_file,
                ));
            }
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        let facts = chain_fact
            .facts()
            .map_err(|e| VerifyError::new(e.to_string(), None, fact_line_file))?;
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
                fact_display_string,
                format!("{} are verified", verify_what.join(", ")),
                InferResult::new(),
                fact_line_file,
                DEFAULT_LINE_FILE.clone(),
            ),
        ))
    }
}
