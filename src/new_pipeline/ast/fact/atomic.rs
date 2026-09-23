use super::super::line_file::LineFile;
use super::super::names::AtomicName;
use super::super::obj::Obj;
use crate::new_pipeline::runtime::FactId;

#[derive(Clone, Debug, PartialEq, Eq)]
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
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InFact {
    pub fact_id: FactId,
    pub element: Obj,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotInFact {
    pub fact_id: FactId,
    pub element: Obj,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LessFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotLessFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GreaterFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotGreaterFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LessEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotLessEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GreaterEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotGreaterEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormalAtomicFact {
    pub fact_id: FactId,
    pub predicate: AtomicName,
    pub body: Vec<Obj>,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotNormalAtomicFact {
    pub fact_id: FactId,
    pub predicate: AtomicName,
    pub body: Vec<Obj>,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsNonemptySetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsNonemptySetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsFiniteSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsFiniteSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SupersetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotSupersetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubsetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotSubsetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsTupleFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsTupleFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsCartFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsCartFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

impl AtomicFact {
    pub fn fact_id(&self) -> FactId {
        match self {
            AtomicFact::NormalAtomicFact(f) => f.fact_id,
            AtomicFact::EqualFact(f) => f.fact_id,
            AtomicFact::LessFact(f) => f.fact_id,
            AtomicFact::GreaterFact(f) => f.fact_id,
            AtomicFact::LessEqualFact(f) => f.fact_id,
            AtomicFact::GreaterEqualFact(f) => f.fact_id,
            AtomicFact::IsSetFact(f) => f.fact_id,
            AtomicFact::IsNonemptySetFact(f) => f.fact_id,
            AtomicFact::IsFiniteSetFact(f) => f.fact_id,
            AtomicFact::InFact(f) => f.fact_id,
            AtomicFact::IsCartFact(f) => f.fact_id,
            AtomicFact::IsTupleFact(f) => f.fact_id,
            AtomicFact::SubsetFact(f) => f.fact_id,
            AtomicFact::SupersetFact(f) => f.fact_id,
            AtomicFact::NotNormalAtomicFact(f) => f.fact_id,
            AtomicFact::NotEqualFact(f) => f.fact_id,
            AtomicFact::NotLessFact(f) => f.fact_id,
            AtomicFact::NotGreaterFact(f) => f.fact_id,
            AtomicFact::NotLessEqualFact(f) => f.fact_id,
            AtomicFact::NotGreaterEqualFact(f) => f.fact_id,
            AtomicFact::NotIsSetFact(f) => f.fact_id,
            AtomicFact::NotIsNonemptySetFact(f) => f.fact_id,
            AtomicFact::NotIsFiniteSetFact(f) => f.fact_id,
            AtomicFact::NotInFact(f) => f.fact_id,
            AtomicFact::NotIsCartFact(f) => f.fact_id,
            AtomicFact::NotIsTupleFact(f) => f.fact_id,
            AtomicFact::NotSubsetFact(f) => f.fact_id,
            AtomicFact::NotSupersetFact(f) => f.fact_id,
        }
    }

    // Predicate-family name shared by a fact and its negation (e.g. both use `in`).
    pub fn prop_name(&self) -> AtomicName {
        use crate::new_pipeline::parse::keywords::{
            EQUAL, GREATER, GREATER_EQUAL, IN, IS_CART, IS_FINITE_SET, IS_NONEMPTY_SET, IS_SET,
            IS_TUPLE, LESS, LESS_EQUAL, SUBSET, SUPERSET,
        };
        match self {
            AtomicFact::NormalAtomicFact(f) => f.predicate.clone(),
            AtomicFact::NotNormalAtomicFact(f) => f.predicate.clone(),
            AtomicFact::EqualFact(_) | AtomicFact::NotEqualFact(_) => AtomicName::Plain {
                name: EQUAL.into(),
            },
            AtomicFact::LessFact(_) | AtomicFact::NotLessFact(_) => AtomicName::Plain {
                name: LESS.into(),
            },
            AtomicFact::GreaterFact(_) | AtomicFact::NotGreaterFact(_) => AtomicName::Plain {
                name: GREATER.into(),
            },
            AtomicFact::LessEqualFact(_) | AtomicFact::NotLessEqualFact(_) => AtomicName::Plain {
                name: LESS_EQUAL.into(),
            },
            AtomicFact::GreaterEqualFact(_) | AtomicFact::NotGreaterEqualFact(_) => {
                AtomicName::Plain {
                    name: GREATER_EQUAL.into(),
                }
            }
            AtomicFact::IsSetFact(_) | AtomicFact::NotIsSetFact(_) => AtomicName::Plain {
                name: IS_SET.into(),
            },
            AtomicFact::IsNonemptySetFact(_) | AtomicFact::NotIsNonemptySetFact(_) => {
                AtomicName::Plain {
                    name: IS_NONEMPTY_SET.into(),
                }
            }
            AtomicFact::IsFiniteSetFact(_) | AtomicFact::NotIsFiniteSetFact(_) => {
                AtomicName::Plain {
                    name: IS_FINITE_SET.into(),
                }
            }
            AtomicFact::InFact(_) | AtomicFact::NotInFact(_) => AtomicName::Plain {
                name: IN.into(),
            },
            AtomicFact::IsCartFact(_) | AtomicFact::NotIsCartFact(_) => AtomicName::Plain {
                name: IS_CART.into(),
            },
            AtomicFact::IsTupleFact(_) | AtomicFact::NotIsTupleFact(_) => AtomicName::Plain {
                name: IS_TUPLE.into(),
            },
            AtomicFact::SubsetFact(_) | AtomicFact::NotSubsetFact(_) => AtomicName::Plain {
                name: SUBSET.into(),
            },
            AtomicFact::SupersetFact(_) | AtomicFact::NotSupersetFact(_) => AtomicName::Plain {
                name: SUPERSET.into(),
            },
        }
    }
}
