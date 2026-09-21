use super::{
    AndFact, AtomicFact, ChainFact, ForallFact, ForallFactWithIff, NotForallFact, OrFact,
    PlainExistFact,
};
use crate::new_pipeline::runtime::FactId;

// Proposition about objects. Membership, equality, forall, … live here — not as Obj "types".
// Contrast: Obj = value/expression; Stmt = env-changing action that may assert or define.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fact {
    AtomicFact(AtomicFact),
    ExistFact(PlainExistFact),
    ExistUniqueFact(PlainExistFact),
    NotExistFact(PlainExistFact),
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
            Fact::ExistFact(p) | Fact::ExistUniqueFact(p) | Fact::NotExistFact(p) => p.fact_id,
            Fact::ForallFact(f) => f.fact_id,
            Fact::ForallFactWithIff(f) => f.fact_id,
            Fact::NotForall(f) => f.fact_id,
        }
    }
}
