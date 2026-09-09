use crate::prelude::*;
use crate::verify_rewrite::VerifyState;

pub struct VerifyOrFactResult {
    pub fact: OrFact,
    pub well_defined_proof: OrFactWellDefinedProof,
    pub searched_proof: OrFactSearchedProof,
}

pub enum OrFactSearchedProof {
    ByCache(CacheSearchProof),
    ByChosenBranch {
        chosen_branch_index: usize,
        proof_of_chosen_branch: VerifyFactResult,
    },
}

impl Runtime {
    pub fn verify_or_fact(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> Result<VerifyOrFactResult, RuntimeError> {
        let well_defined_proof =
            self.verify_or_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_or_fact_proof(fact, verify_state)?;
        Ok(VerifyOrFactResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    // Try known-fact cache, then prove by selecting one verified disjunct.
    pub fn search_or_fact_proof(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> Result<OrFactSearchedProof, RuntimeError> {
        if let Some(result) = self.search_or_fact_proof_by_cache(fact, verify_state.clone())? {
            return Ok(OrFactSearchedProof::ByCache(result));
        }

        if let Some(result) =
            self.search_or_fact_proof_by_chosen_branch(fact, verify_state)?
        {
            return Ok(OrFactSearchedProof::ByChosenBranch {
                chosen_branch_index: result.0,
                proof_of_chosen_branch: result.1,
            });
        }

        todo!()
    }

    pub fn search_or_fact_proof_by_cache(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> Result<Option<CacheSearchProof>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search or fact by cache")
    }

    pub fn search_or_fact_proof_by_chosen_branch(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> Result<Option<(usize, VerifyFactResult)>, RuntimeError> {
        for (chosen_branch_index, branch) in fact.facts.iter().enumerate() {
            let proof_of_chosen_branch =
                self.verify_and_chain_atomic_fact(branch, verify_state.clone())?;
            // A successful branch closes the or-fact. Unknown branches are skipped.
            if matches!(proof_of_chosen_branch, VerifyFactResult::Unknown(_)) {
                continue;
            }
            return Ok(Some((chosen_branch_index, proof_of_chosen_branch)));
        }
        Ok(None)
    }

    pub fn verify_and_chain_atomic_fact(
        &mut self,
        fact: &AndChainAtomicFact,
        verify_state: VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        match fact {
            AndChainAtomicFact::AtomicFact(fact) => Ok(VerifyFactResult::AtomicFact(
                self.verify_atomic_fact(fact, verify_state)?,
            )),
            AndChainAtomicFact::AndFact(fact) => Ok(VerifyFactResult::AndFact(
                self.verify_and_fact(fact, verify_state)?,
            )),
            AndChainAtomicFact::ChainFact(fact) => Ok(VerifyFactResult::ChainFact(
                self.verify_chain_fact(fact, verify_state)?,
            )),
        }
    }
}
