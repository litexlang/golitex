use crate::prelude::*;

pub enum VerifyFactResult {
    Unknown(UnknownVerifyFactResult),
    AtomicFact(VerifyAtomicFactResult),
    ExistFact(VerifyExistFactResult),
    OrFact(VerifyOrFactResult),
    AndFact(VerifyAndFactResult),
    ChainFact(VerifyChainFactResult),
    ForallFact(VerifyForallFactResult),
    ForallFactWithIff(VerifyForallFactWithIffResult),
    NotForall(VerifyNotForallFactResult),
}

pub enum UnknownVerifyFactResult {
    WellDefinedKnown,
    UnableToSearchProof,
}
