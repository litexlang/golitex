use crate::fact::Fact;
use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub enum FactWellDefinedProof2 {
    AtomicFact(AtomicFactWellDefinedProof2),
    AndFact(AndFactWellDefinedProof2),
    ChainFact(ChainFactWellDefinedProof2),
    OrFact(OrFactWellDefinedProof2),
    ExistFact(ExistFactWellDefinedProof2),
    ForallFact(ForallFactWellDefinedProof2),
    ForallFactWithIff(ForallFactWithIffWellDefinedProof2),
    NotForall(NotForallFactWellDefinedProof2),
}

impl Runtime {
    pub fn verify_fact_well_definedness2(
        &mut self,
        fact: &Fact,
        verify_state: VerifyState2,
    ) -> Result<FactWellDefinedProof2, RuntimeError> {
        match fact {
            Fact::AtomicFact(fact) => Ok(FactWellDefinedProof2::AtomicFact(
                self.verify_atomic_fact_well_definedness2(fact, verify_state)?,
            )),
            Fact::AndFact(fact) => Ok(FactWellDefinedProof2::AndFact(
                self.verify_and_fact_well_definedness2(fact, verify_state)?,
            )),
            Fact::ChainFact(fact) => Ok(FactWellDefinedProof2::ChainFact(
                self.verify_chain_fact_well_definedness2(fact, verify_state)?,
            )),
            Fact::OrFact(fact) => Ok(FactWellDefinedProof2::OrFact(
                self.verify_or_fact_well_definedness2(fact, verify_state)?,
            )),
            Fact::ExistFact(fact) => Ok(FactWellDefinedProof2::ExistFact(
                self.verify_exist_fact_well_definedness2(fact.spec(), verify_state)?,
            )),
            Fact::ForallFact(fact) => Ok(FactWellDefinedProof2::ForallFact(
                self.verify_forall_fact_well_definedness2(fact, verify_state)?,
            )),
            Fact::ForallFactWithIff(fact) => Ok(FactWellDefinedProof2::ForallFactWithIff(
                self.verify_forall_fact_with_iff_well_definedness2(fact, verify_state)?,
            )),
            Fact::NotForall(fact) => Ok(FactWellDefinedProof2::NotForall(
                self.verify_not_forall_fact_well_definedness2(fact, verify_state)?,
            )),
        }
    }
}
