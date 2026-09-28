//! Atomic fact sum type and result classification.

use crate::prelude::*;
#[derive(Clone)]
pub enum AtomicFact {
    NormalAtomicFact(NormalAtomicFact),
    EqualFact(EqualFact),
    LessFact(LessFact),
    GreaterFact(GreaterFact),
    LessEqualFact(LessEqualFact),
    GreaterEqualFact(GreaterEqualFact),
    IsSetFact(IsSetFact),
    IsNonemptySetFact(IsNonemptySetFact),
    IsFiniteSetFact(IsFiniteSetFact),
    InFact(InFact),
    IsCartFact(IsCartFact),
    IsTupleFact(IsTupleFact),
    SubsetFact(SubsetFact),
    SupersetFact(SupersetFact),
    NotNormalAtomicFact(NotNormalAtomicFact),
    NotEqualFact(NotEqualFact),
    NotLessFact(NotLessFact),
    NotGreaterFact(NotGreaterFact),
    NotLessEqualFact(NotLessEqualFact),
    NotGreaterEqualFact(NotGreaterEqualFact),
    NotIsSetFact(NotIsSetFact),
    NotIsNonemptySetFact(NotIsNonemptySetFact),
    NotIsFiniteSetFact(NotIsFiniteSetFact),
    NotInFact(NotInFact),
    NotIsCartFact(NotIsCartFact),
    NotIsTupleFact(NotIsTupleFact),
    NotSubsetFact(NotSubsetFact),
    NotSupersetFact(NotSupersetFact),
    FnEqualFact(FnEqualFact),
}

impl AtomicFact {
    pub fn output_type_string(&self) -> String {
        match self {
            AtomicFact::NormalAtomicFact(_) => "prop fact".to_string(),
            AtomicFact::EqualFact(_) => "equality fact".to_string(),
            AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => "comparison fact".to_string(),
            AtomicFact::IsSetFact(_) => "set fact".to_string(),
            AtomicFact::IsNonemptySetFact(_) => "nonempty set fact".to_string(),
            AtomicFact::IsFiniteSetFact(_) => "finite set fact".to_string(),
            AtomicFact::InFact(_) => "membership fact".to_string(),
            AtomicFact::IsCartFact(_) => "cartesian product fact".to_string(),
            AtomicFact::IsTupleFact(_) => "tuple fact".to_string(),
            AtomicFact::SubsetFact(_) => "subset fact".to_string(),
            AtomicFact::SupersetFact(_) => "superset fact".to_string(),
            AtomicFact::NotNormalAtomicFact(_) => "negated prop fact".to_string(),
            AtomicFact::NotEqualFact(_) => "negated equality fact".to_string(),
            AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_) => "negated comparison fact".to_string(),
            AtomicFact::NotIsSetFact(_) => "negated set fact".to_string(),
            AtomicFact::NotIsNonemptySetFact(_) => "negated nonempty set fact".to_string(),
            AtomicFact::NotIsFiniteSetFact(_) => "negated finite set fact".to_string(),
            AtomicFact::NotInFact(_) => "negated membership fact".to_string(),
            AtomicFact::NotIsCartFact(_) => "negated cartesian product fact".to_string(),
            AtomicFact::NotIsTupleFact(_) => "negated tuple fact".to_string(),
            AtomicFact::NotSubsetFact(_) => "negated subset fact".to_string(),
            AtomicFact::NotSupersetFact(_) => "negated superset fact".to_string(),
            AtomicFact::FnEqualFact(_) => "function equality fact".to_string(),
        }
    }
}
