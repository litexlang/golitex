use crate::prelude::*;

impl Runtime {
    pub fn verify_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&fact.clone().into())
        {
            return Ok(cached_result);
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

        match fact {
            AtomicFact::EqualFact(equal_fact) => {
                self.verify_equal_fact(equal_fact, &next_verify_state)
            }
            _ => self.verify_non_equational_atomic_fact(fact, &next_verify_state, true),
        }
    }
}
