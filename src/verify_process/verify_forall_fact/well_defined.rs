use crate::prelude::*;

pub enum ExistOrAndChainAtomicFactWellDefinedProof {
    AtomicFact(AtomicFactWellDefinedProof),
    AndFact(AndFactWellDefinedProof),
    ChainFact(ChainFactWellDefinedProof),
    OrFact(OrFactWellDefinedProof),
    ExistFact(ExistFactWellDefinedProof),
}

pub struct ForallFactWellDefinedProof {
    pub well_defined_of_each_premise: Vec<ExistOrAndChainAtomicFactWellDefinedProof>,
    pub well_defined_of_each_then_fact: Vec<ExistOrAndChainAtomicFactWellDefinedProof>,
}

impl Runtime {
    pub fn verify_forall_fact_well_definedness(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> Result<ForallFactWellDefinedProof, RuntimeError> {
    }

    pub fn verify_exist_or_and_chain_atomic_fact_well_definedness(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        verify_state: VerifyState,
    ) -> Result<ExistOrAndChainAtomicFactWellDefinedProof, RuntimeError> {
    }
}
