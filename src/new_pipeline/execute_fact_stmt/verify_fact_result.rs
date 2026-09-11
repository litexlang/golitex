use crate::prelude::*;

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

impl VerifyFactResult2 {
    pub fn fact(&self) -> Fact {
        match self {
            Self::Unknown(_) => {
                panic!("VerifyFactResult2::Unknown has no fact")
            }
            Self::AtomicFact(result) => match result {
                VerifyAtomicFactResult2::Equality(result) => result.fact.clone().into(),
                VerifyAtomicFactResult2::NonEquationalAtomicFact(result) => {
                    result.fact.clone().into()
                }
            },
            Self::ExistFact(result) => match result {
                VerifyExistFactResult2::Exist(result) => {
                    ExistFact::PlainExistFact(result.fact.clone()).into()
                }
                VerifyExistFactResult2::ExistUnique(result) => {
                    ExistFact::ExistUniqueFact(result.fact.clone()).into()
                }
                VerifyExistFactResult2::NotExist(result) => {
                    ExistFact::NotExistFact(result.fact.clone()).into()
                }
            },
            Self::OrFact(result) => result.fact.clone().into(),
            Self::AndFact(result) => result.fact.clone().into(),
            Self::ChainFact(result) => result.fact.clone().into(),
            Self::ForallFact(result) => result.fact.clone().into(),
            Self::ForallFactWithIff(result) => result.fact.clone().into(),
            Self::NotForall(result) => result.fact.clone().into(),
        }
    }
}
