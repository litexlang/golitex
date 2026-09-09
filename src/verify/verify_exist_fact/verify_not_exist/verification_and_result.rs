use crate::fact::PlainExistFact;
use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct VerifyNotExistFactResult2 {
    pub fact: PlainExistFact,
    pub well_defined_proof: ExistFactWellDefinedProof2,
    pub searched_proof: NotExistFactSearchedProof2,
}

pub enum NotExistFactSearchedProof2 {
    ByCache(CacheSearchProof2),
    ByDemorganForall(VerifyForallFactResult2),
}

impl Runtime {
    pub fn verify_not_exist_fact2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<VerifyNotExistFactResult2, RuntimeError> {
        let well_defined_proof =
            self.verify_exist_fact_well_definedness2(fact, verify_state.clone())?;
        let searched_proof = self.search_not_exist_fact_proof2(fact, verify_state)?;
        Ok(VerifyNotExistFactResult2 {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_not_exist_fact_proof2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<NotExistFactSearchedProof2, RuntimeError> {
        if let Some(result) =
            self.search_not_exist_fact_proof_by_cache2(fact, verify_state.clone())?
        {
            return Ok(NotExistFactSearchedProof2::ByCache(result));
        }

        if let Some(result) =
            self.search_not_exist_fact_proof_by_demorgan_forall2(fact, verify_state)?
        {
            return Ok(NotExistFactSearchedProof2::ByDemorganForall(result));
        }

        todo!()
    }

    pub fn search_not_exist_fact_proof_by_cache2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<Option<CacheSearchProof2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search not exist by cache")
    }

    pub fn search_not_exist_fact_proof_by_demorgan_forall2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<Option<VerifyForallFactResult2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search not exist by demorgan forall")
    }
}
