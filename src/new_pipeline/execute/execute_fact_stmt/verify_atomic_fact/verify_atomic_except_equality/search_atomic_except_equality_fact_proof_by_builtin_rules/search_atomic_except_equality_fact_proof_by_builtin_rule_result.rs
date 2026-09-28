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
pub use super::not_in_fact::NotInFactSearchProofByBuiltinRule;
use super::not_greater::NotGreaterFactSearchProofByBuiltinRule;
use super::not_greater_equal::NotGreaterEqualFactSearchProofByBuiltinRule;
pub use super::not_is_finite_set::NotIsFiniteSetFactSearchProofByBuiltinRule;
use super::not_is_nonempty_set::NotIsNonemptySetFactSearchProofByBuiltinRule;
use super::not_less::NotLessFactSearchProofByBuiltinRule;
use super::not_less_equal::NotLessEqualFactSearchProofByBuiltinRule;
use super::not_subset::NotSubsetFactSearchProofByBuiltinRule;
use super::not_superset::NotSupersetFactSearchProofByBuiltinRule;
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
}

// Uninhabited stubs: split into a predicate file when the first builtin rule is added.
pub enum NormalAtomicFactSearchProofByBuiltinRule {}
pub enum NotNormalAtomicFactSearchProofByBuiltinRule {}
pub enum NotIsSetFactSearchProofByBuiltinRule {}
pub enum NotIsCartFactSearchProofByBuiltinRule {}
pub enum NotIsTupleFactSearchProofByBuiltinRule {}
