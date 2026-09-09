use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub enum VerifyFactResult2 {
    Unknown(UnknownVerifyFactResult2),
    AtomicFact(VerifyAtomicFactResult2),
    ExistFact(VerifyExistFactResult2),
    OrFact(VerifyOrFactResult2),
    AndFact(VerifyAndFactResult2),
    ChainFact(VerifyChainFactResult2),
    ForallFact(VerifyForallFactResult2),
    ForallFactWithIff(VerifyForallFactWithIffResult2),
    NotForall(VerifyNotForallFactResult2),
}

pub enum UnknownVerifyFactResult2 {
    WellDefinedKnown,
    UnableToSearchProof,
}
