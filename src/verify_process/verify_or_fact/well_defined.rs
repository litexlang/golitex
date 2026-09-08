use crate::prelude::*;

pub enum AndChainAtomicFactWellDefinedProof {
    AtomicFact(AtomicFactWellDefinedProof),
    AndFact(AndFactWellDefinedProof),
    ChainFact(ChainFactWellDefinedProof),
}

pub struct OrFactWellDefinedProof {
    pub well_defined_of_each_branch: Vec<AndChainAtomicFactWellDefinedProof>,
}

impl Runtime {
    pub fn verify_or_fact_well_definedness(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> Result<OrFactWellDefinedProof, RuntimeError> {
    }

    pub fn verify_and_chain_atomic_fact_well_definedness(
        &mut self,
        fact: &AndChainAtomicFact,
        verify_state: VerifyState,
    ) -> Result<AndChainAtomicFactWellDefinedProof, RuntimeError> {
    }
}
