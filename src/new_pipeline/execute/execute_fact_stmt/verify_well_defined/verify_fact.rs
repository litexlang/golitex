use super::AtomicFactWellDefinedProof;
use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Result of classifying a Fact and running its WD path.
pub enum FactWellDefinedProof {
    AtomicFact(AtomicFactWellDefinedProof),
    // Temporary: full composite WD pipelines are still draft-only. Allows
    // `trust` / store of closed composite facts so exact FactIR ByCache works.
    CompositePending,
}

impl FactWellDefinedProof {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::AtomicFact(proof) => proof.is_failed(),
            Self::CompositePending => false,
        }
    }
}

impl Runtime {
    // Main WD entry for facts: match Fact shape, then dispatch.
    pub fn verify_fact_well_definedness(
        &mut self,
        fact: &Fact,
        verify_state: VerifyState,
    ) -> RuntimeResult<FactWellDefinedProof> {
        match fact {
            Fact::AtomicFact(fact) => Ok(FactWellDefinedProof::AtomicFact(
                self.verify_atomic_fact_well_definedness(fact, verify_state)?,
            )),
            Fact::AndFact(_)
            | Fact::ChainFact(_)
            | Fact::OrFact(_)
            | Fact::ExistFact(_)
            | Fact::ForallFact(_)
            | Fact::ForallFactWithIff(_)
            | Fact::NotForall(_) => Ok(FactWellDefinedProof::CompositePending),
        }
    }
}
