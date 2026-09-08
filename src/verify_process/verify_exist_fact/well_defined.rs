use crate::prelude::*;

pub enum QuantifierFreeFactWellDefinedProof {
    AtomicFact(AtomicFactWellDefinedProof),
    AndFact(AndFactWellDefinedProof),
    ChainFact(ChainFactWellDefinedProof),
    OrFact(OrFactWellDefinedProof),
}

pub enum ExistFactWellDefinedProof {
    Plain(PlainExistFactWellDefinedProof),
    ExistUnique(ExistUniqueFactWellDefinedProof),
    NotExist(NotExistFactWellDefinedProof),
}

impl Runtime {
    pub fn verify_quantifier_free_fact_well_definedness(
        &mut self,
        fact: &QuantifierFreeFact,
        verify_state: VerifyState,
    ) -> Result<QuantifierFreeFactWellDefinedProof, RuntimeError> {
    }

    pub fn verify_existential_spec_body_well_definedness(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<Vec<QuantifierFreeFactWellDefinedProof>, RuntimeError> {
    }
}
