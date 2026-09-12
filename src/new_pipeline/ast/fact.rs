//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: String names, FactId, SourceSpan — no SymbolId / AtomId.

use super::names::AtomicName;
use super::obj::Obj;
use super::param::TypedParameterList;
use super::source_span::SourceSpan;
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
pub struct EqualFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/equality.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotEqualFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/function_equality.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnEqualInFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub set: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/function_equality.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnEqualFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/membership.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InFact {    pub fact_id: FactId,
    pub element: Obj,
    pub set: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/membership.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotInFact {    pub fact_id: FactId,
    pub element: Obj,
    pub set: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LessFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotLessFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GreaterFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotGreaterFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LessEqualFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotLessEqualFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GreaterEqualFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/order_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotGreaterEqualFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/predicate.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormalAtomicFact {    pub fact_id: FactId,
    pub predicate: AtomicName,
    pub body: Vec<Obj>,
    pub span: SourceSpan,
}

// from fact/atomic/predicate.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotNormalAtomicFact {    pub fact_id: FactId,
    pub predicate: AtomicName,
    pub body: Vec<Obj>,
    pub span: SourceSpan,
}

// from fact/atomic/set_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsSetFact {    pub fact_id: FactId,
    pub set: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/set_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsSetFact {    pub fact_id: FactId,
    pub set: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/set_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsNonemptySetFact {    pub fact_id: FactId,
    pub set: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/set_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsNonemptySetFact {    pub fact_id: FactId,
    pub set: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/set_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsFiniteSetFact {    pub fact_id: FactId,
    pub set: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/set_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsFiniteSetFact {    pub fact_id: FactId,
    pub set: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/set_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SupersetFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/set_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotSupersetFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/set_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubsetFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/set_relations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotSubsetFact {    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/structure_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsTupleFact {    pub fact_id: FactId,
    pub set: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/structure_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsTupleFact {    pub fact_id: FactId,
    pub set: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/structure_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsCartFact {    pub fact_id: FactId,
    pub set: Obj,
    pub span: SourceSpan,
}

// from fact/atomic/structure_properties.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsCartFact {    pub fact_id: FactId,
    pub set: Obj,
    pub span: SourceSpan,
}

// from fact/composite/conjunction_and_chain.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AndFact {    pub fact_id: FactId,
    pub facts: Vec<AtomicFact>,
    pub span: SourceSpan,
}

// from fact/composite/conjunction_and_chain.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainFact {    pub fact_id: FactId,
    pub objs: Vec<Obj>,
    pub prop_names: Vec<AtomicName>,
    pub span: SourceSpan,
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
pub struct OrFact {    pub fact_id: FactId,
    pub facts: Vec<AndChainAtomicFact>,
    pub span: SourceSpan,
}

// from fact/composite/order_closure.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NumericOrderChainClosureStep {    pub start_object_index: usize,
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
pub struct DirectForallConclusionLocation {    pub then_fact_index: usize,
}

// from fact/forall_conclusion_location.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AndFactComponentForallConclusionLocation {    pub then_fact_index: usize,
    pub component_index: usize,
}

// from fact/forall_conclusion_location.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainFactComponentForallConclusionLocation {    pub then_fact_index: usize,
    pub component_index: usize,
}

// from fact/not_forall.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotForallFact {    pub fact_id: FactId,
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
pub struct PlainExistFact {    pub fact_id: FactId,
    pub typed_parameters: TypedParameterList,
    pub facts: Vec<QuantifierFreeFact>,
    pub span: SourceSpan,
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
pub struct ForallFact {    pub fact_id: FactId,
    pub typed_parameters: TypedParameterList,
    pub dom_facts: Vec<Fact>,
    pub then_facts: Vec<ExistOrAndChainAtomicFact>,
    pub span: SourceSpan,
}

// from fact/quantified/universal_iff.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForallFactWithIff {    pub fact_id: FactId,
    pub forall_fact: ForallFact,
    pub iff_facts: Vec<ExistOrAndChainAtomicFact>,
    pub span: SourceSpan,
}

