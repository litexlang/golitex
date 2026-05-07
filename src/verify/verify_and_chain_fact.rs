use crate::prelude::*;
use std::result::Result;

impl Runtime {
    pub fn verify_and_fact(
        &mut self,
        and_fact: &AndFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&and_fact.clone().into())
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_and_fact_well_defined(and_fact, verify_state) {
                return Err(RuntimeError::from(VerifyRuntimeError(
                    RuntimeErrorStruct::new(
                        Some(Fact::from(and_fact.clone()).into_stmt()),
                        String::new(),
                        and_fact.line_file(),
                        Some(e),
                        vec![],
                    ),
                )));
            }
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        let mut child_results: Vec<StmtResult> = Vec::with_capacity(and_fact.facts.len());
        for fact in &and_fact.facts {
            let result = self.verify_atomic_fact(fact, &verify_state_for_children)?;
            if result.is_unknown() {
                return Ok(result);
            }
            child_results.push(result);
        }
        Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
            and_fact.clone().into(),
            VerifiedByResult::wrap_bys(
                and_fact.clone().into(),
                vec![VerifiedByResult::fact_with_note(
                    and_fact.clone().into(),
                    Some("and: each conjunct verified in order".to_string()),
                )],
            ),
            child_results,
        ))
        .into())
    }

    pub fn verify_chain_fact(
        &mut self,
        chain_fact: &ChainFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&chain_fact.clone().into())
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_chain_fact_well_defined(chain_fact, verify_state) {
                return Err(RuntimeError::from(VerifyRuntimeError(
                    RuntimeErrorStruct::new(
                        Some(Fact::from(chain_fact.clone()).into_stmt()),
                        String::new(),
                        chain_fact.line_file(),
                        Some(e),
                        vec![],
                    ),
                )));
            }
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        let facts = chain_fact.facts().map_err(|e| {
            RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                Some(Fact::ChainFact(chain_fact.clone()).into_stmt()),
                String::new(),
                chain_fact.line_file(),
                Some(e),
                vec![],
            )))
        })?;
        let mut child_results: Vec<StmtResult> = Vec::with_capacity(facts.len());
        for fact in &facts {
            let result = self.verify_atomic_fact(fact, &verify_state_for_children)?;
            if result.is_unknown() {
                return Ok((StmtUnknown::new_with_detail(format!(
                    "unverified chain step: {}",
                    fact
                )))
                .into());
            }

            child_results.push(result);
        }
        Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
            chain_fact.clone().into(),
            VerifiedByResult::wrap_bys(
                chain_fact.clone().into(),
                vec![VerifiedByResult::fact_with_note(
                    chain_fact.clone().into(),
                    Some("chain: each step verified in order".to_string()),
                )],
            ),
            child_results,
        ))
        .into())
    }
}
