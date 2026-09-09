use crate::fact::PlainExistFact;
use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct VerifyExistUniqueFactResult2 {
    pub fact: PlainExistFact,
    pub well_defined_proof: ExistFactWellDefinedProof2,
    pub searched_proof: ExistUniqueFactSearchedProof2,
}

pub enum ExistUniqueFactSearchedProof2 {
    ByCache(CacheSearchProof2),
    ProveAsExistFactWithUniqueness(ExistUniqueFactSearchedProofByExistAndUniqueness2),
}

pub struct ExistUniqueFactSearchedProofByExistAndUniqueness2 {
    pub proof_of_exist_fact: VerifyPlainExistFactResult2,
    pub proof_of_uniqueness: VerifyForallFactResult2,
}

impl Runtime {
    pub fn verify_exist_unique_fact2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<VerifyExistUniqueFactResult2, RuntimeError> {
        let well_defined_proof =
            self.verify_exist_unique_fact_well_definedness2(fact, verify_state.clone())?;
        let searched_proof = self.search_exist_unique_fact_proof2(fact, verify_state)?;
        Ok(VerifyExistUniqueFactResult2 {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_exist_unique_fact_proof2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<ExistUniqueFactSearchedProof2, RuntimeError> {
        if let Some(result) =
            self.search_exist_unique_fact_proof_by_cache2(fact, verify_state.clone())?
        {
            return Ok(ExistUniqueFactSearchedProof2::ByCache(result));
        }

        if let Some(result) = self
            .search_exist_unique_fact_proof_by_exist_and_uniqueness2(fact, verify_state)?
        {
            return Ok(ExistUniqueFactSearchedProof2::ProveAsExistFactWithUniqueness(
                result,
            ));
        }

        todo!()
    }

    pub fn search_exist_unique_fact_proof_by_cache2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<Option<CacheSearchProof2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search exist unique by cache")
    }

    pub fn search_exist_unique_fact_proof_by_exist_and_uniqueness2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<Option<ExistUniqueFactSearchedProofByExistAndUniqueness2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search exist unique by exist and uniqueness")
    }
}
