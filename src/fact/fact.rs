//! Top-level fact sum type.

use crate::prelude::*;

#[derive(Clone)]
pub enum Fact {
    AtomicFact(AtomicFact),
    ExistFact(ExistFactEnum),
    OrFact(OrFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    ForallFact(ForallFact),
    ForallFactWithIff(ForallFactWithIff),
    NotForall(NotForallFact),
}
