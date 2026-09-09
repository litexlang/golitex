use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub enum AndChainAtomicFactWellDefinedProof2 {
    AtomicFact(AtomicFactWellDefinedProof2),
    AndFact(AndFactWellDefinedProof2),
    ChainFact(ChainFactWellDefinedProof2),
}

pub struct OrFactWellDefinedProof2 {
    pub well_defined_of_each_branch: Vec<AndChainAtomicFactWellDefinedProof2>,
}

impl Runtime {
    pub fn verify_or_fact_well_definedness2(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState2,
    ) -> Result<OrFactWellDefinedProof2, RuntimeError> {
        let mut well_defined_of_each_branch = Vec::new();
        for branch in fact.facts.iter() {
            well_defined_of_each_branch.push(
                self.verify_and_chain_atomic_fact_well_definedness2(branch, verify_state.clone())?,
            );
        }
        Ok(OrFactWellDefinedProof2 {
            well_defined_of_each_branch,
        })
    }

    pub fn verify_and_chain_atomic_fact_well_definedness2(
        &mut self,
        fact: &AndChainAtomicFact,
        verify_state: VerifyState2,
    ) -> Result<AndChainAtomicFactWellDefinedProof2, RuntimeError> {
        match fact {
            AndChainAtomicFact::AtomicFact(fact) => Ok(AndChainAtomicFactWellDefinedProof2::AtomicFact(
                self.verify_atomic_fact_well_definedness2(fact, verify_state)?,
            )),
            AndChainAtomicFact::AndFact(fact) => Ok(AndChainAtomicFactWellDefinedProof2::AndFact(
                self.verify_and_fact_well_definedness2(fact, verify_state)?,
            )),
            AndChainAtomicFact::ChainFact(fact) => Ok(AndChainAtomicFactWellDefinedProof2::ChainFact(
                self.verify_chain_fact_well_definedness2(fact, verify_state)?,
            )),
        }
    }
}
