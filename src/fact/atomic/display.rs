//! Atomic fact source rendering.

use crate::prelude::*;
use std::fmt;
impl fmt::Display for AtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            AtomicFact::NormalAtomicFact(x) => write!(f, "{}", x),
            AtomicFact::EqualFact(x) => write!(f, "{}", x),
            AtomicFact::LessFact(x) => write!(f, "{}", x),
            AtomicFact::GreaterFact(x) => write!(f, "{}", x),
            AtomicFact::LessEqualFact(x) => write!(f, "{}", x),
            AtomicFact::GreaterEqualFact(x) => write!(f, "{}", x),
            AtomicFact::IsSetFact(x) => write!(f, "{}", x),
            AtomicFact::IsNonemptySetFact(x) => write!(f, "{}", x),
            AtomicFact::IsFiniteSetFact(x) => write!(f, "{}", x),
            AtomicFact::NotNormalAtomicFact(x) => write!(f, "{}", x),
            AtomicFact::NotEqualFact(x) => write!(f, "{}", x),
            AtomicFact::NotLessFact(x) => write!(f, "{}", x),
            AtomicFact::NotGreaterFact(x) => write!(f, "{}", x),
            AtomicFact::NotLessEqualFact(x) => write!(f, "{}", x),
            AtomicFact::NotGreaterEqualFact(x) => write!(f, "{}", x),
            AtomicFact::NotIsSetFact(x) => write!(f, "{}", x),
            AtomicFact::NotIsNonemptySetFact(x) => write!(f, "{}", x),
            AtomicFact::NotIsFiniteSetFact(x) => write!(f, "{}", x),
            AtomicFact::InFact(x) => write!(f, "{}", x),
            AtomicFact::NotInFact(x) => write!(f, "{}", x),
            AtomicFact::IsCartFact(x) => write!(f, "{}", x),
            AtomicFact::NotIsCartFact(x) => write!(f, "{}", x),
            AtomicFact::IsTupleFact(x) => write!(f, "{}", x),
            AtomicFact::NotIsTupleFact(x) => write!(f, "{}", x),
            AtomicFact::SubsetFact(x) => write!(f, "{}", x),
            AtomicFact::NotSubsetFact(x) => write!(f, "{}", x),
            AtomicFact::SupersetFact(x) => write!(f, "{}", x),
            AtomicFact::NotSupersetFact(x) => write!(f, "{}", x),
            AtomicFact::FnEqualFact(x) => write!(f, "{}", x),
        }
    }
}
