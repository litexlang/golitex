use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

pub enum AndChainAtomicFactWellDefinedProof {
    AtomicFact(DraftAtomicFactWellDefinedProof),
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
        let mut well_defined_of_each_branch = Vec::new();
        for branch in fact.facts.iter() {
            well_defined_of_each_branch.push(
                self.verify_and_chain_atomic_fact_well_definedness(branch, verify_state.clone())?,
            );
        }
        Ok(OrFactWellDefinedProof {
            well_defined_of_each_branch,
        })
    }

    pub fn verify_and_chain_atomic_fact_well_definedness(
        &mut self,
        fact: &AndChainAtomicFact,
        verify_state: VerifyState,
    ) -> Result<AndChainAtomicFactWellDefinedProof, RuntimeError> {
        match fact {
            AndChainAtomicFact::AtomicFact(fact) => Ok(AndChainAtomicFactWellDefinedProof::AtomicFact(
                self.verify_draft_atomic_fact_well_definedness(fact, verify_state)?,
            )),
            AndChainAtomicFact::AndFact(fact) => Ok(AndChainAtomicFactWellDefinedProof::AndFact(
                self.verify_and_fact_well_definedness(fact, verify_state)?,
            )),
            AndChainAtomicFact::ChainFact(fact) => Ok(AndChainAtomicFactWellDefinedProof::ChainFact(
                self.verify_chain_fact_well_definedness(fact, verify_state)?,
            )),
        }
    }
}
