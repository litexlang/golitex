use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;

// Equality proofs that need one or more requirement subgoals (unlike pure
// Calculation builtins). Each variant owns its requirement facts and their
// VerifyFactResult proofs.
pub enum EqualitySearchProofByBuiltinStrategy {
    ExtremumEquality(ExtremumEqualityStrategySingleStep),
    FiniteSetProductPointwiseEquality(FiniteSetProductPointwiseEqualityStrategySingleStep),
    ModCongruence(ModCongruenceStrategySingleStep),
    RationalWithNonzeroPremises(RationalWithNonzeroPremisesStrategySingleStep),
}

// Prove an equality about min/max (or similar extremum) by discharging both
// weak-order directions.
// Mathematical property: if L <= R and R <= L, then L = R (antisymmetry).
// Restricted to goals whose left or right is FiniteSetMax / FiniteSetMin /
// Max / Min so ordinary equalities do not fall into open-ended order search.
//
// Example:
//   trust a <= max(a, a)
//   trust max(a, a) <= a
//   max(a, a) = a
pub struct ExtremumEqualityStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Prove `finite_set_product(X, f) = finite_set_product(Y, g)` by set equality
// and one pointwise factor equality under a fresh binder `x X`.
// Mathematical property: if X = Y and forall x in X, f(x) = g(x), then the
// finite products agree (here the pointwise goal is checked in a local binder).
//
// Example:
//   finite_set_product({1}, fn(x {1}) Z {1})
//     = finite_set_product({1}, fn(x {1}) Z {0 + 1})
// via `{1} = {1}` and local `1 = 0 + 1`.
pub struct FiniteSetProductPointwiseEqualityStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Prove a congruence equality modulo n by discharging modulus identity and
// immediate operand congruences.
// Mathematical property: if x ≡ x' (mod m) and y ≡ y' (mod m), then
// x+y ≡ x'+y' (mod m) (and likewise for -, *).
//
// Example:
//   trust a % m = b % m
//   trust c % m = d % m
//   (a + c) % m = (b + d) % m
pub struct ModCongruenceStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin strategy: rational/polynomial identity that is sound only after
// proving every denominator and negative-power base nonzero.
//
// Mathematical property: if left and right have the same monomial normal form
// after denominator clearing, and each collected obligation `d` satisfies
// `d != 0`, then `left = right`.
//
// Examples:
// - From `x != 0`, prove `x / x = 1`.
// - From `b != 0`, prove `a / b + c / b = (a + c) / b`.
//
// `requirement_facts` are exactly those `d != 0` facts (ordered); each entry in
// `proof_of_requirement_facts` is the successful verify result for the same index.
pub struct RationalWithNonzeroPremisesStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
