use super::native_equal::NativeVerifyEqualResult;
use super::verify_atomic_fact::VerifyAtomicFactResult2;
use crate::prelude::*;

pub enum VerifyFactResult2 {
    Unknown(UnknownVerifyFactResult2),
    AtomicFact(Box<VerifyAtomicFactResult2>),
    NativeEqual(NativeVerifyEqualResult),
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
            Self::NativeEqual(_) => {
                panic!("VerifyFactResult2::NativeEqual has no legacy Fact")
            }
            Self::AtomicFact(result) => match result.as_ref() {
                VerifyAtomicFactResult2::Equality(result) => result.fact.clone().into(),
                VerifyAtomicFactResult2::NonEquationalAtomicFact(result) => {
                    result.fact.clone().into()
                }
            },
        }
    }
}
