impl Runtime {
    pub fn execute_fact_statement(&mut self, fact: &FactStmt) -> Result<StmtResult, RuntimeError> {
        let verify_state = self.current_verify_state();
        
        let verify_result = self.verify_fact(fact, verify_state)?;
        let store_and_infer_result = self.store_and_infer_fact(fact);

        return Ok(StmtResult::FactStmtResult(FactStmtResult {
            verify_result,
            store_and_infer_result,
        }));
    }

    pub fn verify_fact(&mut self, fact: &FactStmt, verify_state: VerifyState) -> Result<VerifyResult, RuntimeError> {
        match fact {
            FactStmt::AtomicFact(fact) => self.verify_atomic_fact(fact, verify_state),
            FactStmt::ForallFact(fact) => self.verify_forall_fact(fact, verify_state),
            FactStmt::ExistUniqueFact(fact) => self.verify_exist_unique_fact(fact, verify_state),
            FactStmt::ExistFact(fact) => self.verify_exist_fact(fact, verify_state),
            // ....
        }
    }

    pub fn verify_atomic_fact(&mut self, fact: &AtomicFact, verify_state: VerifyState) -> Result<VerifyResult, RuntimeError> {
        match fact {
            AtomicFact::EqualFact(equal_fact) => self.verify_equal_fact(equal_fact, verify_state),
            _ => self.verify_non_equational_atomic_fact(
                fact, 
                verify_state
            ),
        }
    }

    pub fn verify_non_equational_atomic_fact(&mut self, fact: &AtomicFact, verify_state: VerifyState) -> Result<VerifyResult, RuntimeError> {
    }

    pub fn verify_forall_fact(&mut self, fact: &ForallFact, verify_state: VerifyState) -> Result<VerifyResult, RuntimeError> {
        self.execute_in_local_scope(|runtime| {
        })
    }
}