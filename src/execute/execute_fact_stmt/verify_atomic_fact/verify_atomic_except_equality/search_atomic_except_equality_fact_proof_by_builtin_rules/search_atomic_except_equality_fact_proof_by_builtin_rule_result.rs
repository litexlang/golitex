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
    ProperSubsetFact(ProperSubsetFactSearchProofByBuiltinRule),
    ProperSupersetFact(ProperSupersetFactSearchProofByBuiltinRule),
    PrimeFact(PrimeFactSearchProofByBuiltinRule),
    CoprimeFact(CoprimeFactSearchProofByBuiltinRule),
    DvdFact(DvdFactSearchProofByBuiltinRule),
    InjectiveFact(InjectiveFactSearchProofByBuiltinRule),
    SurjectiveFact(SurjectiveFactSearchProofByBuiltinRule),
    BijectiveFact(BijectiveFactSearchProofByBuiltinRule),
    IsChoiceFunctionForFact(IsChoiceFunctionForFactSearchProofByBuiltinRule),
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
    NotProperSubsetFact(NotProperSubsetFactSearchProofByBuiltinRule),
    NotProperSupersetFact(NotProperSupersetFactSearchProofByBuiltinRule),
    NotPrimeFact(NotPrimeFactSearchProofByBuiltinRule),
    NotCoprimeFact(NotCoprimeFactSearchProofByBuiltinRule),
    NotDvdFact(NotDvdFactSearchProofByBuiltinRule),
    NotInjectiveFact(NotInjectiveFactSearchProofByBuiltinRule),
    NotSurjectiveFact(NotSurjectiveFactSearchProofByBuiltinRule),
    NotBijectiveFact(NotBijectiveFactSearchProofByBuiltinRule),
    NotIsChoiceFunctionForFact(NotIsChoiceFunctionForFactSearchProofByBuiltinRule),
}

// User-defined `$prop(...)` only; official builtins use dedicated families.
pub enum NormalAtomicFactSearchProofByBuiltinRule {}

pub enum NotNormalAtomicFactSearchProofByBuiltinRule {}

pub enum ProperSubsetFactSearchProofByBuiltinRule {}
pub enum ProperSupersetFactSearchProofByBuiltinRule {}
pub enum DvdFactSearchProofByBuiltinRule {}
pub enum InjectiveFactSearchProofByBuiltinRule {}
pub enum SurjectiveFactSearchProofByBuiltinRule {}
pub enum BijectiveFactSearchProofByBuiltinRule {}
pub enum IsChoiceFunctionForFactSearchProofByBuiltinRule {}
pub enum NotProperSubsetFactSearchProofByBuiltinRule {}
pub enum NotProperSupersetFactSearchProofByBuiltinRule {}
pub enum NotDvdFactSearchProofByBuiltinRule {}
pub enum NotInjectiveFactSearchProofByBuiltinRule {}
pub enum NotSurjectiveFactSearchProofByBuiltinRule {}
pub enum NotBijectiveFactSearchProofByBuiltinRule {}
pub enum NotIsChoiceFunctionForFactSearchProofByBuiltinRule {}

pub enum PrimeFactSearchProofByBuiltinRule {
    // Closed u64 primality computation.
    // Mathematical property: `$prime(n)` for a resolved nonnegative integer prime.
    // Example: `$prime(17)`.
    PrimeByComputation(PrimeByComputation),
}

pub struct PrimeByComputation {
    pub resolved_value: String,
}

pub enum CoprimeFactSearchProofByBuiltinRule {
    // Closed natural coprimality via gcd-one.
    // Mathematical property: `$coprime(a, b)` when resolved nonnegative integers
    // satisfy `gcd(a, b) = 1` and are not both zero.
    // Example: `$coprime(14, 25)`.
    CoprimeByComputation(CoprimeByComputation),
}

pub struct CoprimeByComputation {
    pub left_resolved: String,
    pub right_resolved: String,
}

pub enum NotPrimeFactSearchProofByBuiltinRule {
    // Closed u64 non-primality computation.
    // Mathematical property: `not $prime(n)` for a resolved nonnegative non-prime.
    // Example: `not $prime(1)`.
    NotPrimeByComputation(NotPrimeByComputation),
}

pub struct NotPrimeByComputation {
    pub resolved_value: String,
}

pub enum NotCoprimeFactSearchProofByBuiltinRule {
    // Closed natural non-coprimality via gcd.
    // Mathematical property: `not $coprime(a, b)` when resolved nonnegative
    // integers fail the gcd-one criterion.
    // Example: `not $coprime(14, 21)`.
    NotCoprimeByComputation(NotCoprimeByComputation),
}

pub struct NotCoprimeByComputation {
    pub left_resolved: String,
    pub right_resolved: String,
}

pub enum NotIsSetFactSearchProofByBuiltinRule {}
pub enum NotIsCartFactSearchProofByBuiltinRule {}
pub enum NotIsTupleFactSearchProofByBuiltinRule {}
