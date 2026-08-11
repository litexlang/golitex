use crate::prelude::*;

impl Runtime {
    pub fn verify_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if self.known_equality_candidate_replay_depth != 0 {
            return self
                .verify_atomic_fact_with_non_forall_facts_then_with_builtin_computation(fact);
        }

        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&fact.clone().into())
        {
            return Ok(
                if self.well_definedness_capture_depth != 0
                    && self.captures_litex_to_lean_well_definedness()
                {
                    self.remember_successful_atomic_fact_for_statement(fact, cached_result)
                } else {
                    cached_result
                },
            );
        }

        if !verify_state.well_defined_already_verified {
            let well_defined_state = verify_state.without_known_forall_for_equality();
            if let Err(e) = self.verify_atomic_fact_well_defined(fact, &well_defined_state) {
                return Err({
                    VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(fact.clone()).into_stmt()),
                        String::new(),
                        fact.line_file(),
                        Some(e),
                        vec![],
                    ))
                    .into()
                });
            }
        }

        let next_verify_state = verify_state.with_well_defined_already_verified();

        let result = match fact {
            AtomicFact::EqualFact(equal_fact) => {
                self.verify_equal_fact(equal_fact, &next_verify_state)
            }
            _ => self.verify_non_equational_atomic_fact(fact, &next_verify_state, true),
        }?;
        Ok(self.remember_successful_atomic_fact_for_statement(fact, result))
    }
}
