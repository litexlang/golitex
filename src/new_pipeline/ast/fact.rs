//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: String names, FactId, LineFile (name is identity; no IdentifierId).

use super::line_file::LineFile;
use super::names::AtomicName;
use super::obj::Obj;
use super::param::TypedParameterList;
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

// from fact/composite/conjunction_and_chain.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AndFact {
    pub fact_id: FactId,
    pub facts: Vec<AtomicFact>,
    pub line_file: Option<LineFile>,
}

// from fact/composite/conjunction_and_chain.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainFact {
    pub fact_id: FactId,
    pub objs: Vec<Obj>,
    pub prop_names: Vec<AtomicName>,
    pub line_file: Option<LineFile>,
}

// from fact/composite/conjunction_and_chain.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChainAtomicFact {
    AtomicFact(AtomicFact),
    ChainFact(ChainFact),
}

// from fact/composite/conjunction_and_chain.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AndChainAtomicFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
}

// from fact/composite/disjunction.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrFact {
    pub fact_id: FactId,
    pub facts: Vec<AndChainAtomicFact>,
    pub line_file: Option<LineFile>,
}

// from fact/composite/order_closure.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NumericOrderChainClosureStep {
    pub start_object_index: usize,
    pub end_object_index: usize,
    pub premises: Vec<Fact>,
    pub conclusion: AtomicFact,
}

// from fact/composite/quantifier_free.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuantifierFreeFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    OrFact(OrFact),
}

// from fact/fact.rs
#[derive(Clone, Debug, PartialEq, Eq)]
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

// from fact/forall_conclusion_location.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForallConclusionLocation {
    DirectThenFact(DirectForallConclusionLocation),
    AndFactComponent(AndFactComponentForallConclusionLocation),
    ChainFactComponent(ChainFactComponentForallConclusionLocation),
}

// from fact/forall_conclusion_location.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DirectForallConclusionLocation {
    pub then_fact_index: usize,
}

// from fact/forall_conclusion_location.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AndFactComponentForallConclusionLocation {
    pub then_fact_index: usize,
    pub component_index: usize,
}

// from fact/forall_conclusion_location.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainFactComponentForallConclusionLocation {
    pub then_fact_index: usize,
    pub component_index: usize,
}

// from fact/not_forall.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotForallFact {
    pub fact_id: FactId,
    pub forall_fact: ForallFact,
}

// from fact/quantified/existential.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExistFact {
    PlainExistFact(PlainExistFact),
    ExistUniqueFact(PlainExistFact),
    NotExistFact(PlainExistFact),
}

// from fact/quantified/existential.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlainExistFact {
    pub fact_id: FactId,
    pub typed_parameters: TypedParameterList,
    pub facts: Vec<QuantifierFreeFact>,
    pub line_file: Option<LineFile>,
}

// from fact/quantified/nested.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExistOrAndChainAtomicFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    OrFact(OrFact),
    ExistFact(ExistFact),
}

// from fact/quantified/universal.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForallFact {
    pub fact_id: FactId,
    pub typed_parameters: TypedParameterList,
    pub dom_facts: Vec<Fact>,
    pub then_facts: Vec<ExistOrAndChainAtomicFact>,
    pub line_file: Option<LineFile>,
}

// from fact/quantified/universal_iff.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForallFactWithIff {
    pub fact_id: FactId,
    pub forall_fact: ForallFact,
    pub iff_facts: Vec<ExistOrAndChainAtomicFact>,
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
}

impl Fact {
    pub fn fact_id(&self) -> FactId {
        match self {
            Fact::AtomicFact(f) => f.fact_id(),
            Fact::AndFact(f) => f.fact_id,
            Fact::ChainFact(f) => f.fact_id,
            Fact::OrFact(f) => f.fact_id,
            Fact::ExistFact(f) => match f {
                ExistFact::PlainExistFact(p)
                | ExistFact::ExistUniqueFact(p)
                | ExistFact::NotExistFact(p) => p.fact_id,
            },
            Fact::ForallFact(f) => f.fact_id,
            Fact::ForallFactWithIff(f) => f.fact_id,
            Fact::NotForall(f) => f.fact_id,
        }
    }
}
