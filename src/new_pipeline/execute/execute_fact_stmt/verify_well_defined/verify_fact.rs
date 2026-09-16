use super::{
    AtomicFactWellDefinedProof, FailToVerifyObjWellDefinedResult, VerifyAtomicFactWellDefinedResult,
};
use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Success-only evidence that a Fact is well-defined.
pub enum FactWellDefinedProof {
    AtomicFact(AtomicFactWellDefinedProof),
    AndFact {
        components: Vec<AtomicFactWellDefinedProof>,
    },
    ChainFact {
        adjacent: Vec<AtomicFactWellDefinedProof>,
    },
    // Temporary: remaining composite WD pipelines are still draft-only.
    CompositePending,
}

// Soft miss vs success for fact WD. Proof never embeds Fail.
pub enum VerifyFactWellDefinedResult {
    Success(FactWellDefinedProof),
    Failed(FailToVerifyObjWellDefinedResult),
}

impl VerifyFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // Main WD entry for facts: match Fact shape, then dispatch.
    pub fn verify_fact_well_definedness(
        &mut self,
        fact: &Fact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactWellDefinedResult> {
        match fact {
            Fact::AtomicFact(fact) => {
                match self.verify_atomic_fact_well_definedness(fact, verify_state)? {
                    VerifyAtomicFactWellDefinedResult::Success(proof) => {
                        Ok(VerifyFactWellDefinedResult::Success(
                            FactWellDefinedProof::AtomicFact(proof),
                        ))
                    }
                    VerifyAtomicFactWellDefinedResult::Failed(reason) => {
                        Ok(VerifyFactWellDefinedResult::Failed(reason))
                    }
                }
            }
            Fact::AndFact(and_fact) => {
                let mut components = Vec::with_capacity(and_fact.facts.len());
                for atomic in &and_fact.facts {
                    match self.verify_atomic_fact_well_definedness(atomic, verify_state.clone())? {
                        VerifyAtomicFactWellDefinedResult::Success(proof) => {
                            components.push(proof);
                        }
                        VerifyAtomicFactWellDefinedResult::Failed(reason) => {
                            return Ok(VerifyFactWellDefinedResult::Failed(reason));
                        }
                    }
                }
                Ok(VerifyFactWellDefinedResult::Success(
                    FactWellDefinedProof::AndFact { components },
                ))
            }
            Fact::ChainFact(chain_fact) => {
                let adjacent_atomics = self.chain_adjacent_atomics(chain_fact)?;
                let mut adjacent = Vec::with_capacity(adjacent_atomics.len());
                for atomic in &adjacent_atomics {
                    match self.verify_atomic_fact_well_definedness(atomic, verify_state.clone())? {
                        VerifyAtomicFactWellDefinedResult::Success(proof) => {
                            adjacent.push(proof);
                        }
                        VerifyAtomicFactWellDefinedResult::Failed(reason) => {
                            return Ok(VerifyFactWellDefinedResult::Failed(reason));
                        }
                    }
                }
                Ok(VerifyFactWellDefinedResult::Success(
                    FactWellDefinedProof::ChainFact { adjacent },
                ))
            }
            Fact::OrFact(_)
            | Fact::ExistFact(_)
            | Fact::ForallFact(_)
            | Fact::ForallFactWithIff(_)
            | Fact::NotForall(_) => Ok(VerifyFactWellDefinedResult::Success(
                FactWellDefinedProof::CompositePending,
            )),
        }
    }
}
