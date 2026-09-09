use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct VerifyOrFactResult2 {
    pub fact: OrFact,
    pub well_defined_proof: OrFactWellDefinedProof2,
    pub searched_proof: OrFactSearchedProof2,
}

pub enum OrFactSearchedProof2 {
    ByCache(CacheSearchProof2),
    ByChosenBranch {
        chosen_branch_index: usize,
        proof_of_chosen_branch: VerifyFactResult2,
    },
}

impl Runtime {
    pub fn verify_or_fact2(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState2,
    ) -> Result<VerifyOrFactResult2, RuntimeError> {
        let well_defined_proof =
            self.verify_or_fact_well_definedness2(fact, verify_state.clone())?;
        let searched_proof = self.search_or_fact_proof2(fact, verify_state)?;
        Ok(VerifyOrFactResult2 {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    // Try known-fact cache, then prove by selecting one verified disjunct.
    pub fn search_or_fact_proof2(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState2,
    ) -> Result<OrFactSearchedProof2, RuntimeError> {
        if let Some(result) = self.search_or_fact_proof_by_cache2(fact, verify_state.clone())? {
            return Ok(OrFactSearchedProof2::ByCache(result));
        }

        if let Some(result) =
            self.search_or_fact_proof_by_chosen_branch2(fact, verify_state)?
        {
            return Ok(OrFactSearchedProof2::ByChosenBranch {
                chosen_branch_index: result.0,
                proof_of_chosen_branch: result.1,
            });
        }

        todo!()
    }

    pub fn search_or_fact_proof_by_cache2(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState2,
    ) -> Result<Option<CacheSearchProof2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search or fact by cache")
    }

    pub fn search_or_fact_proof_by_chosen_branch2(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState2,
    ) -> Result<Option<(usize, VerifyFactResult2)>, RuntimeError> {
        for (chosen_branch_index, branch) in fact.facts.iter().enumerate() {
            let proof_of_chosen_branch =
                self.verify_and_chain_atomic_fact2(branch, verify_state.clone())?;
            // A successful branch closes the or-fact. Unknown branches are skipped.
            if matches!(proof_of_chosen_branch, VerifyFactResult2::Unknown(_)) {
                continue;
            }
            return Ok(Some((chosen_branch_index, proof_of_chosen_branch)));
        }
        Ok(None)
    }

    pub fn verify_and_chain_atomic_fact2(
        &mut self,
        fact: &AndChainAtomicFact,
        verify_state: VerifyState2,
    ) -> Result<VerifyFactResult2, RuntimeError> {
        match fact {
            AndChainAtomicFact::AtomicFact(fact) => Ok(VerifyFactResult2::AtomicFact(
                self.verify_atomic_fact2(fact, verify_state)?,
            )),
            AndChainAtomicFact::AndFact(fact) => Ok(VerifyFactResult2::AndFact(
                self.verify_and_fact2(fact, verify_state)?,
            )),
            AndChainAtomicFact::ChainFact(fact) => Ok(VerifyFactResult2::ChainFact(
                self.verify_chain_fact2(fact, verify_state)?,
            )),
        }
    }
}
