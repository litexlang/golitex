use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct VerifyNotForallFactResult2 {
    pub fact: NotForallFact,
    pub well_defined_proof: NotForallFactWellDefinedProof2,
    pub searched_proof: NotForallFactSearchedProof2,
}

pub enum NotForallFactSearchedProof2 {
    ByCache(CacheSearchProof2),
}

impl Runtime {
    pub fn verify_not_forall_fact2(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState2,
    ) -> Result<VerifyNotForallFactResult2, RuntimeError> {
        let well_defined_proof =
            self.verify_not_forall_fact_well_definedness2(fact, verify_state.clone())?;
        let searched_proof = self.search_not_forall_fact_proof2(fact, verify_state)?;
        Ok(VerifyNotForallFactResult2 {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    // Currently only known-fact cache proves `not forall`.
    pub fn search_not_forall_fact_proof2(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState2,
    ) -> Result<NotForallFactSearchedProof2, RuntimeError> {
        if let Some(result) =
            self.search_not_forall_fact_proof_by_cache2(fact, verify_state)?
        {
            return Ok(NotForallFactSearchedProof2::ByCache(result));
        }

        todo!()
    }

    pub fn search_not_forall_fact_proof_by_cache2(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState2,
    ) -> Result<Option<CacheSearchProof2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search not forall by cache")
    }
}
