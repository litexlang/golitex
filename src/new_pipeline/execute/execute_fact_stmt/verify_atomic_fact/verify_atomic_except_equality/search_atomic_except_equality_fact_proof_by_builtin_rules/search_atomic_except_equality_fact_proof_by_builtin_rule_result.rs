use super::greater::GreaterFactSearchProofByBuiltinRule;
use super::greater_equal::GreaterEqualFactSearchProofByBuiltinRule;
use super::in_fact::InFactSearchProofByBuiltinRule;
use super::is_cart::IsCartFactSearchProofByBuiltinRule;
use super::is_finite_set::IsFiniteSetFactSearchProofByBuiltinRule;
use super::is_nonempty_set::IsNonemptySetFactSearchProofByBuiltinRule;
use super::is_set::IsSetFactSearchProofByBuiltinRule;
use super::is_tuple::IsTupleFactSearchProofByBuiltinRule;
use super::less::LessFactSearchProofByBuiltinRule;
use super::less_equal::LessEqualFactSearchProofByBuiltinRule;
use super::not_equal::NotEqualFactSearchProofByBuiltinRule;
use super::not_is_nonempty_set::NotIsNonemptySetFactSearchProofByBuiltinRule;
use super::subset::SubsetFactSearchProofByBuiltinRule;
use super::superset::SupersetFactSearchProofByBuiltinRule;

/// Builtin-rule search proof for a atomic-except-equality atomic fact.
/// Mirrors atomic-except-equality `AtomicFact` constructors; each variant owns that
/// fact family's builtin-rule evidence.
pub enum AtomicExceptEqualityFactSearchProofByBuiltinRule {
    NormalAtomicFact(NormalAtomicFactSearchProofByBuiltinRule),
    LessFact(LessFactSearchProofByBuiltinRule),
    GreaterFact(GreaterFactSearchProofByBuiltinRule),
    LessEqualFact(LessEqualFactSearchProofByBuiltinRule),
    GreaterEqualFact(GreaterEqualFactSearchProofByBuiltinRule),
    IsSetFact(IsSetFactSearchProofByBuiltinRule),
    IsNonemptySetFact(IsNonemptySetFactSearchProofByBuiltinRule),
    IsFiniteSetFact(IsFiniteSetFactSearchProofByBuiltinRule),
    InFact(InFactSearchProofByBuiltinRule),
    IsCartFact(IsCartFactSearchProofByBuiltinRule),
    IsTupleFact(IsTupleFactSearchProofByBuiltinRule),
    SubsetFact(SubsetFactSearchProofByBuiltinRule),
    SupersetFact(SupersetFactSearchProofByBuiltinRule),
    NotNormalAtomicFact(NotNormalAtomicFactSearchProofByBuiltinRule),
    NotEqualFact(NotEqualFactSearchProofByBuiltinRule),
    NotLessFact(NotLessFactSearchProofByBuiltinRule),
    NotGreaterFact(NotGreaterFactSearchProofByBuiltinRule),
    NotLessEqualFact(NotLessEqualFactSearchProofByBuiltinRule),
    NotGreaterEqualFact(NotGreaterEqualFactSearchProofByBuiltinRule),
    NotIsSetFact(NotIsSetFactSearchProofByBuiltinRule),
    NotIsNonemptySetFact(NotIsNonemptySetFactSearchProofByBuiltinRule),
    NotIsFiniteSetFact(NotIsFiniteSetFactSearchProofByBuiltinRule),
    NotInFact(NotInFactSearchProofByBuiltinRule),
    NotIsCartFact(NotIsCartFactSearchProofByBuiltinRule),
    NotIsTupleFact(NotIsTupleFactSearchProofByBuiltinRule),
    NotSubsetFact(NotSubsetFactSearchProofByBuiltinRule),
    NotSupersetFact(NotSupersetFactSearchProofByBuiltinRule),
    FnEqualInFact(FnEqualInFactSearchProofByBuiltinRule),
    FnEqualFact(FnEqualFactSearchProofByBuiltinRule),
}

// Uninhabited stubs: split into a predicate file when the first builtin rule is added.
pub enum NormalAtomicFactSearchProofByBuiltinRule {}
pub enum NotNormalAtomicFactSearchProofByBuiltinRule {}
pub enum NotLessFactSearchProofByBuiltinRule {}
pub enum NotGreaterFactSearchProofByBuiltinRule {}
pub enum NotLessEqualFactSearchProofByBuiltinRule {}
pub enum NotGreaterEqualFactSearchProofByBuiltinRule {}
pub enum NotIsSetFactSearchProofByBuiltinRule {}
pub enum NotIsFiniteSetFactSearchProofByBuiltinRule {}
pub enum NotInFactSearchProofByBuiltinRule {}
pub enum NotIsCartFactSearchProofByBuiltinRule {}
pub enum NotIsTupleFactSearchProofByBuiltinRule {}
pub enum NotSubsetFactSearchProofByBuiltinRule {}
pub enum NotSupersetFactSearchProofByBuiltinRule {}
pub enum FnEqualInFactSearchProofByBuiltinRule {}
pub enum FnEqualFactSearchProofByBuiltinRule {}
