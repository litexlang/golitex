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
                return Err(
                    {
            let __fact: Fact = (and_fact.clone().into());
            let __stmt = __fact.into_stmt();
            VerifyRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt),
                String::new(),
                and_fact.line_file(),
                Some(e),
                vec![],
            ))
            .into()
        },
                );
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
        Ok(
            (FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
                and_fact.clone().into(),
                format!("{} are verified", verify_what.join(", ")),
                None,
                Some(default_line_file()),
                Vec::new(),
            ))
            .into(),
        )
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
                return Err(
                    {
            let __fact: Fact = (chain_fact.clone().into());
            let __stmt = __fact.into_stmt();
            VerifyRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt),
                String::new(),
                chain_fact.line_file(),
                Some(e),
                vec![],
            ))
            .into()
        },
                );
            }
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        let facts = chain_fact.facts().map_err(|e| {
            {
            let __fact: Fact = (Fact::ChainFact(chain_fact.clone()));
            let __stmt = __fact.into_stmt();
            RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt),
                String::new(),
                chain_fact.line_file(),
                Some(e),
                vec![],
            )))
        }
        })?;
        let mut verify_what = Vec::with_capacity(facts.len());
        for fact in &facts {
            let result = self.verify_atomic_fact(fact, &verify_state_for_children)?;
            if result.is_unknown() {
                return Ok((StmtUnknown::new_with_detail(format!(
                    "unverified chain step: {}",
                    fact
                )))
                .into());
            }

            verify_what.push(fact.to_string());
        }
        Ok(
            (FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
                chain_fact.clone().into(),
                format!("{} are verified", verify_what.join(", ")),
                None,
                Some(default_line_file()),
                Vec::new(),
            ))
            .into(),
        )
    }
}
