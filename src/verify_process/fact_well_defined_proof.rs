use crate::prelude::*;

pub enum FactWellDefinedProof {
    AtomicFact(AtomicFactWellDefinedProof),
    AndFact(AndFactWellDefinedProof),
    ChainFact(ChainFactWellDefinedProof),
    OrFact(OrFactWellDefinedProof),
    ExistFact(ExistFactWellDefinedProof),
    ForallFact(ForallFactWellDefinedProof),
    ForallFactWithIff(ForallFactWithIffWellDefinedProof),
    NotForall(NotForallFactWellDefinedProof),
}

impl Runtime {
    pub fn verify_fact_well_definedness(
        &mut self,
        fact: &Fact,
        verify_state: VerifyState,
    ) -> Result<FactWellDefinedProof, RuntimeError> {
        match fact {
            Fact::AtomicFact(fact) => Ok(FactWellDefinedProof::AtomicFact(
                self.verify_atomic_fact_well_definedness(fact, verify_state)?,
            )),
            Fact::AndFact(fact) => Ok(FactWellDefinedProof::AndFact(
                self.verify_and_fact_well_definedness(fact, verify_state)?,
            )),
            Fact::ChainFact(fact) => Ok(FactWellDefinedProof::ChainFact(
                self.verify_chain_fact_well_definedness(fact, verify_state)?,
            )),
            Fact::OrFact(fact) => Ok(FactWellDefinedProof::OrFact(
                self.verify_or_fact_well_definedness(fact, verify_state)?,
            )),
            Fact::ExistFact(fact) => Ok(FactWellDefinedProof::ExistFact(
                self.verify_exist_fact_enum_well_definedness(fact, verify_state)?,
            )),
            Fact::ForallFact(fact) => Ok(FactWellDefinedProof::ForallFact(
                self.verify_forall_fact_well_definedness(fact, verify_state)?,
            )),
            Fact::ForallFactWithIff(fact) => Ok(FactWellDefinedProof::ForallFactWithIff(
                self.verify_forall_fact_with_iff_well_definedness(fact, verify_state)?,
            )),
            Fact::NotForall(fact) => Ok(FactWellDefinedProof::NotForall(
                self.verify_not_forall_fact_well_definedness(fact, verify_state)?,
            )),
        }
    }

    pub fn verify_exist_fact_enum_well_definedness(
        &mut self,
        fact: &ExistFactEnum,
        verify_state: VerifyState,
    ) -> Result<ExistFactWellDefinedProof, RuntimeError> {
        match fact {
            ExistFactEnum::ExistFact(spec)
            | ExistFactEnum::ExistUniqueFact(spec)
            | ExistFactEnum::NotExistFact(spec) => {
                self.verify_exist_fact_well_definedness(spec, verify_state)
            }
        }
    }
}
