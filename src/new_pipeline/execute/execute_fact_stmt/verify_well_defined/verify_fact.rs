use super::AtomicFactWellDefinedProof;
use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

// Result of classifying a Fact and running its WD path.
pub enum FactWellDefinedProof {
    AtomicFact(AtomicFactWellDefinedProof),
    // AndFact / ChainFact / OrFact / Exist / Forall / ... filled in next.
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
            Fact::AndFact(_) => Err(RuntimeError::Unsupported(
                "verify_fact_well_definedness: AndFact not wired yet".to_string(),
            )),
            Fact::ChainFact(_) => Err(RuntimeError::Unsupported(
                "verify_fact_well_definedness: ChainFact not wired yet".to_string(),
            )),
            Fact::OrFact(_) => Err(RuntimeError::Unsupported(
                "verify_fact_well_definedness: OrFact not wired yet".to_string(),
            )),
            Fact::ExistFact(_) => Err(RuntimeError::Unsupported(
                "verify_fact_well_definedness: ExistFact not wired yet".to_string(),
            )),
            Fact::ForallFact(_) => Err(RuntimeError::Unsupported(
                "verify_fact_well_definedness: ForallFact not wired yet".to_string(),
            )),
            Fact::ForallFactWithIff(_) => Err(RuntimeError::Unsupported(
                "verify_fact_well_definedness: ForallFactWithIff not wired yet".to_string(),
            )),
            Fact::NotForall(_) => Err(RuntimeError::Unsupported(
                "verify_fact_well_definedness: NotForall not wired yet".to_string(),
            )),
        }
    }
}
