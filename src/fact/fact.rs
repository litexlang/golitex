//! Top-level fact sum type.

use crate::prelude::*;

#[derive(Clone)]
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
