use crate::fact::Fact;
use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

pub enum DraftFactWellDefinedProof {
    AtomicFact(DraftAtomicFactWellDefinedProof),
    AndFact(AndFactWellDefinedProof),
    ChainFact(ChainFactWellDefinedProof),
    OrFact(OrFactWellDefinedProof),
    ExistFact(ExistFactWellDefinedProof),
    ForallFact(ForallFactWellDefinedProof),
    ForallFactWithIff(ForallFactWithIffWellDefinedProof),
    NotForall(NotForallFactWellDefinedProof),
}

impl Runtime {
    pub fn verify_draft_fact_well_definedness(
        &mut self,
        fact: &Fact,
        verify_state: VerifyState,
    ) -> Result<DraftFactWellDefinedProof, RuntimeError> {
        match fact {
            Fact::AtomicFact(fact) => Ok(DraftFactWellDefinedProof::AtomicFact(
                self.verify_draft_atomic_fact_well_definedness(fact, verify_state)?,
            )),
            Fact::AndFact(fact) => Ok(DraftFactWellDefinedProof::AndFact(
                self.verify_and_fact_well_definedness(fact, verify_state)?,
            )),
            Fact::ChainFact(fact) => Ok(DraftFactWellDefinedProof::ChainFact(
                self.verify_chain_fact_well_definedness(fact, verify_state)?,
            )),
            Fact::OrFact(fact) => Ok(DraftFactWellDefinedProof::OrFact(
                self.verify_or_fact_well_definedness(fact, verify_state)?,
            )),
            Fact::ExistFact(fact) => Ok(DraftFactWellDefinedProof::ExistFact(
                self.verify_exist_fact_well_definedness(fact.spec(), verify_state)?,
            )),
            Fact::ForallFact(fact) => Ok(DraftFactWellDefinedProof::ForallFact(
                self.verify_forall_fact_well_definedness(fact, verify_state)?,
            )),
            Fact::ForallFactWithIff(fact) => Ok(DraftFactWellDefinedProof::ForallFactWithIff(
                self.verify_forall_fact_with_iff_well_definedness(fact, verify_state)?,
            )),
            Fact::NotForall(fact) => Ok(DraftFactWellDefinedProof::NotForall(
                self.verify_not_forall_fact_well_definedness(fact, verify_state)?,
            )),
        }
    }
}
