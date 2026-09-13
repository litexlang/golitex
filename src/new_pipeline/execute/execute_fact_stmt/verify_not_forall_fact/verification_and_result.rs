use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

pub struct VerifyNotForallFactResult {
    pub fact: NotForallFact,
    pub well_defined_proof: NotForallFactWellDefinedProof,
    pub searched_proof: NotForallFactSearchedProof,
}

pub enum NotForallFactSearchedProof {
    ByCache(CacheSearchProof),
}

impl Runtime {
    pub fn verify_not_forall_fact(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState,
    ) -> Result<VerifyNotForallFactResult, RuntimeError> {
        let well_defined_proof =
            self.verify_not_forall_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_not_forall_fact_proof(fact, verify_state)?;
        Ok(VerifyNotForallFactResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    // Currently only known-fact cache proves `not forall`.
    pub fn search_not_forall_fact_proof(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState,
    ) -> Result<NotForallFactSearchedProof, RuntimeError> {
        if let Some(result) =
            self.search_not_forall_fact_proof_by_cache(fact, verify_state)?
        {
            return Ok(NotForallFactSearchedProof::ByCache(result));
        }

        todo!()
    }

    pub fn search_not_forall_fact_proof_by_cache(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState,
    ) -> Result<Option<CacheSearchProof>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search not forall by cache")
    }
}
