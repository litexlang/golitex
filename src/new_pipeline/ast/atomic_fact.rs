//! Atomic facts for new_pipeline AST.
//! Structs first; helpers and From wrappers after.

use super::line_file::LineFile;
use super::names::AtomicName;
use super::obj::Obj;
use crate::new_pipeline::runtime::FactId;

// from fact/atomic/atomic_fact.rs
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
    FnEqualInFact(FnEqualInFact),
    FnEqualFact(FnEqualFact),
}

// from fact/atomic/equality.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/equality.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/function_equality.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnEqualInFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/function_equality.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/membership.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InFact {
    pub fact_id: FactId,
    pub element: Obj,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/membership.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotInFact {
    pub fact_id: FactId,
    pub element: Obj,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LessFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotLessFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GreaterFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotGreaterFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LessEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotLessEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GreaterEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotGreaterEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/predicate.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormalAtomicFact {
    pub fact_id: FactId,
    pub predicate: AtomicName,
    pub body: Vec<Obj>,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/predicate.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotNormalAtomicFact {
    pub fact_id: FactId,
    pub predicate: AtomicName,
    pub body: Vec<Obj>,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/set_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/set_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/set_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsNonemptySetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/set_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsNonemptySetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/set_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsFiniteSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/set_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsFiniteSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/set_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SupersetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/set_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotSupersetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/set_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubsetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/set_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotSubsetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/structure_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsTupleFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/structure_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsTupleFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/structure_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsCartFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<LineFile>,
}

// from fact/atomic/structure_properties.rs
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
            AtomicFact::FnEqualInFact(f) => f.fact_id,
            AtomicFact::FnEqualFact(f) => f.fact_id,
        }
    }

    // Predicate-family name shared by a fact and its negation (e.g. both use `in`).
    pub fn prop_name(&self) -> String {
        use crate::new_pipeline::parse::keywords::{
            EQUAL, FN_EQ, FN_EQ_IN, GREATER, GREATER_EQUAL, IN, IS_CART, IS_FINITE_SET,
            IS_NONEMPTY_SET, IS_SET, IS_TUPLE, LESS, LESS_EQUAL, SUBSET, SUPERSET,
        };
        match self {
            AtomicFact::NormalAtomicFact(f) => match &f.predicate {
                AtomicName::WithoutMod(name) => name.clone(),
                AtomicName::WithMod(module, name) => format!("{module}::{name}"),
            },
            AtomicFact::NotNormalAtomicFact(f) => match &f.predicate {
                AtomicName::WithoutMod(name) => name.clone(),
                AtomicName::WithMod(module, name) => format!("{module}::{name}"),
            },
            AtomicFact::EqualFact(_) | AtomicFact::NotEqualFact(_) => EQUAL.to_string(),
            AtomicFact::LessFact(_) | AtomicFact::NotLessFact(_) => LESS.to_string(),
            AtomicFact::GreaterFact(_) | AtomicFact::NotGreaterFact(_) => GREATER.to_string(),
            AtomicFact::LessEqualFact(_) | AtomicFact::NotLessEqualFact(_) => {
                LESS_EQUAL.to_string()
            }
            AtomicFact::GreaterEqualFact(_) | AtomicFact::NotGreaterEqualFact(_) => {
                GREATER_EQUAL.to_string()
            }
            AtomicFact::IsSetFact(_) | AtomicFact::NotIsSetFact(_) => IS_SET.to_string(),
            AtomicFact::IsNonemptySetFact(_) | AtomicFact::NotIsNonemptySetFact(_) => {
                IS_NONEMPTY_SET.to_string()
            }
            AtomicFact::IsFiniteSetFact(_) | AtomicFact::NotIsFiniteSetFact(_) => {
                IS_FINITE_SET.to_string()
            }
            AtomicFact::InFact(_) | AtomicFact::NotInFact(_) => IN.to_string(),
            AtomicFact::IsCartFact(_) | AtomicFact::NotIsCartFact(_) => IS_CART.to_string(),
            AtomicFact::IsTupleFact(_) | AtomicFact::NotIsTupleFact(_) => IS_TUPLE.to_string(),
            AtomicFact::SubsetFact(_) | AtomicFact::NotSubsetFact(_) => SUBSET.to_string(),
            AtomicFact::SupersetFact(_) | AtomicFact::NotSupersetFact(_) => SUPERSET.to_string(),
            AtomicFact::FnEqualInFact(_) => FN_EQ_IN.to_string(),
            AtomicFact::FnEqualFact(_) => FN_EQ.to_string(),
        }
    }

    pub fn has_positive_polarity(&self) -> bool {
        !matches!(
            self,
            AtomicFact::NotNormalAtomicFact(_)
                | AtomicFact::NotEqualFact(_)
                | AtomicFact::NotLessFact(_)
                | AtomicFact::NotGreaterFact(_)
                | AtomicFact::NotLessEqualFact(_)
                | AtomicFact::NotGreaterEqualFact(_)
                | AtomicFact::NotIsSetFact(_)
                | AtomicFact::NotIsNonemptySetFact(_)
                | AtomicFact::NotIsFiniteSetFact(_)
                | AtomicFact::NotInFact(_)
                | AtomicFact::NotIsCartFact(_)
                | AtomicFact::NotIsTupleFact(_)
                | AtomicFact::NotSubsetFact(_)
                | AtomicFact::NotSupersetFact(_)
        )
    }

    pub fn args_ref(&self) -> Vec<&Obj> {
        match self {
            AtomicFact::NormalAtomicFact(f) => f.body.iter().collect(),
            AtomicFact::NotNormalAtomicFact(f) => f.body.iter().collect(),
            AtomicFact::EqualFact(f) => vec![&f.left, &f.right],
            AtomicFact::NotEqualFact(f) => vec![&f.left, &f.right],
            AtomicFact::LessFact(f) => vec![&f.left, &f.right],
            AtomicFact::NotLessFact(f) => vec![&f.left, &f.right],
            AtomicFact::GreaterFact(f) => vec![&f.left, &f.right],
            AtomicFact::NotGreaterFact(f) => vec![&f.left, &f.right],
            AtomicFact::LessEqualFact(f) => vec![&f.left, &f.right],
            AtomicFact::NotLessEqualFact(f) => vec![&f.left, &f.right],
            AtomicFact::GreaterEqualFact(f) => vec![&f.left, &f.right],
            AtomicFact::NotGreaterEqualFact(f) => vec![&f.left, &f.right],
            AtomicFact::IsSetFact(f) => vec![&f.set],
            AtomicFact::NotIsSetFact(f) => vec![&f.set],
            AtomicFact::IsNonemptySetFact(f) => vec![&f.set],
            AtomicFact::NotIsNonemptySetFact(f) => vec![&f.set],
            AtomicFact::IsFiniteSetFact(f) => vec![&f.set],
            AtomicFact::NotIsFiniteSetFact(f) => vec![&f.set],
            AtomicFact::InFact(f) => vec![&f.element, &f.set],
            AtomicFact::NotInFact(f) => vec![&f.element, &f.set],
            AtomicFact::IsCartFact(f) => vec![&f.set],
            AtomicFact::NotIsCartFact(f) => vec![&f.set],
            AtomicFact::IsTupleFact(f) => vec![&f.set],
            AtomicFact::NotIsTupleFact(f) => vec![&f.set],
            AtomicFact::SubsetFact(f) => vec![&f.left, &f.right],
            AtomicFact::NotSubsetFact(f) => vec![&f.left, &f.right],
            AtomicFact::SupersetFact(f) => vec![&f.left, &f.right],
            AtomicFact::NotSupersetFact(f) => vec![&f.left, &f.right],
            AtomicFact::FnEqualInFact(f) => vec![&f.left, &f.right, &f.set],
            AtomicFact::FnEqualFact(f) => vec![&f.left, &f.right],
        }
    }
}

// Enum wrapping: prefer leaf.into() over AtomicFact::Variant(leaf).
// Enum wrapping: prefer leaf.into() over AtomicFact::Variant(leaf).
impl From<NormalAtomicFact> for AtomicFact {
    fn from(f: NormalAtomicFact) -> Self {
        AtomicFact::NormalAtomicFact(f)
    }
}

impl From<EqualFact> for AtomicFact {
    fn from(f: EqualFact) -> Self {
        AtomicFact::EqualFact(f)
    }
}

impl From<LessFact> for AtomicFact {
    fn from(f: LessFact) -> Self {
        AtomicFact::LessFact(f)
    }
}

impl From<GreaterFact> for AtomicFact {
    fn from(f: GreaterFact) -> Self {
        AtomicFact::GreaterFact(f)
    }
}

impl From<LessEqualFact> for AtomicFact {
    fn from(f: LessEqualFact) -> Self {
        AtomicFact::LessEqualFact(f)
    }
}

impl From<GreaterEqualFact> for AtomicFact {
    fn from(f: GreaterEqualFact) -> Self {
        AtomicFact::GreaterEqualFact(f)
    }
}

impl From<IsSetFact> for AtomicFact {
    fn from(f: IsSetFact) -> Self {
        AtomicFact::IsSetFact(f)
    }
}

impl From<IsNonemptySetFact> for AtomicFact {
    fn from(f: IsNonemptySetFact) -> Self {
        AtomicFact::IsNonemptySetFact(f)
    }
}

impl From<IsFiniteSetFact> for AtomicFact {
    fn from(f: IsFiniteSetFact) -> Self {
        AtomicFact::IsFiniteSetFact(f)
    }
}

impl From<InFact> for AtomicFact {
    fn from(f: InFact) -> Self {
        AtomicFact::InFact(f)
    }
}

impl From<IsCartFact> for AtomicFact {
    fn from(f: IsCartFact) -> Self {
        AtomicFact::IsCartFact(f)
    }
}

impl From<IsTupleFact> for AtomicFact {
    fn from(f: IsTupleFact) -> Self {
        AtomicFact::IsTupleFact(f)
    }
}

impl From<SubsetFact> for AtomicFact {
    fn from(f: SubsetFact) -> Self {
        AtomicFact::SubsetFact(f)
    }
}

impl From<SupersetFact> for AtomicFact {
    fn from(f: SupersetFact) -> Self {
        AtomicFact::SupersetFact(f)
    }
}

impl From<NotNormalAtomicFact> for AtomicFact {
    fn from(f: NotNormalAtomicFact) -> Self {
        AtomicFact::NotNormalAtomicFact(f)
    }
}

impl From<NotEqualFact> for AtomicFact {
    fn from(f: NotEqualFact) -> Self {
        AtomicFact::NotEqualFact(f)
    }
}

impl From<NotLessFact> for AtomicFact {
    fn from(f: NotLessFact) -> Self {
        AtomicFact::NotLessFact(f)
    }
}

impl From<NotGreaterFact> for AtomicFact {
    fn from(f: NotGreaterFact) -> Self {
        AtomicFact::NotGreaterFact(f)
    }
}

impl From<NotLessEqualFact> for AtomicFact {
    fn from(f: NotLessEqualFact) -> Self {
        AtomicFact::NotLessEqualFact(f)
    }
}

impl From<NotGreaterEqualFact> for AtomicFact {
    fn from(f: NotGreaterEqualFact) -> Self {
        AtomicFact::NotGreaterEqualFact(f)
    }
}

impl From<NotIsSetFact> for AtomicFact {
    fn from(f: NotIsSetFact) -> Self {
        AtomicFact::NotIsSetFact(f)
    }
}

impl From<NotIsNonemptySetFact> for AtomicFact {
    fn from(f: NotIsNonemptySetFact) -> Self {
        AtomicFact::NotIsNonemptySetFact(f)
    }
}

impl From<NotIsFiniteSetFact> for AtomicFact {
    fn from(f: NotIsFiniteSetFact) -> Self {
        AtomicFact::NotIsFiniteSetFact(f)
    }
}

impl From<NotInFact> for AtomicFact {
    fn from(f: NotInFact) -> Self {
        AtomicFact::NotInFact(f)
    }
}

impl From<NotIsCartFact> for AtomicFact {
    fn from(f: NotIsCartFact) -> Self {
        AtomicFact::NotIsCartFact(f)
    }
}

impl From<NotIsTupleFact> for AtomicFact {
    fn from(f: NotIsTupleFact) -> Self {
        AtomicFact::NotIsTupleFact(f)
    }
}

impl From<NotSubsetFact> for AtomicFact {
    fn from(f: NotSubsetFact) -> Self {
        AtomicFact::NotSubsetFact(f)
    }
}

impl From<NotSupersetFact> for AtomicFact {
    fn from(f: NotSupersetFact) -> Self {
        AtomicFact::NotSupersetFact(f)
    }
}

impl From<FnEqualInFact> for AtomicFact {
    fn from(f: FnEqualInFact) -> Self {
        AtomicFact::FnEqualInFact(f)
    }
}

impl From<FnEqualFact> for AtomicFact {
    fn from(f: FnEqualFact) -> Self {
        AtomicFact::FnEqualFact(f)
    }
}
