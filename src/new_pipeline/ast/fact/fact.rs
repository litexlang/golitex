use super::{
    AndFact, AtomicFact, ChainFact, ExistFact, ForallFact, ForallFactWithIff, NotForallFact,
    OrFact,
};
use crate::new_pipeline::runtime::FactId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fact {
    AtomicFact(AtomicFact),
    ExistFact(ExistFact),
    OrFact(OrFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    ForallFact(ForallFact),
    ForallFactWithIff(ForallFactWithIff),
    NotForall(NotForallFact),
}

impl Fact {
    pub fn fact_id(&self) -> FactId {
        match self {
            Fact::AtomicFact(f) => f.fact_id(),
            Fact::AndFact(f) => f.fact_id,
            Fact::ChainFact(f) => f.fact_id,
            Fact::OrFact(f) => f.fact_id,
            Fact::ExistFact(f) => match f {
                ExistFact::PlainExistFact(p)
                | ExistFact::ExistUniqueFact(p)
                | ExistFact::NotExistFact(p) => p.fact_id,
            },
            Fact::ForallFact(f) => f.fact_id,
            Fact::ForallFactWithIff(f) => f.fact_id,
            Fact::NotForall(f) => f.fact_id,
        }
    }
}
