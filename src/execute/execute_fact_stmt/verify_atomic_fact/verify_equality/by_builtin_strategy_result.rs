use crate::ast::fact::Fact;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;

// Equality proofs that need one or more requirement subgoals (unlike pure
// Calculation builtins). Each variant owns its requirement facts and their
// VerifyFactResult proofs.
pub enum EqualitySearchProofByBuiltinStrategy {
    CosZeroIntegerOffset(CosZeroIntegerOffsetStrategySingleStep),
    TupleComponentEquality(TupleComponentEqualityStrategySingleStep),
    ArithmeticCongruence(ArithmeticCongruenceStrategySingleStep),
    ExtremumEquality(ExtremumEqualityStrategySingleStep),
    FiniteSetProductPointwiseEquality(FiniteSetProductPointwiseEqualityStrategySingleStep),
    ModCongruence(ModCongruenceStrategySingleStep),
    RationalWithNonzeroPremises(RationalWithNonzeroPremisesStrategySingleStep),
    ComplexWithNonzeroPremises(ComplexWithNonzeroPremisesStrategySingleStep),
}

// cos(x) = 0 follows from (x - pi/2)/pi in Z. Requirements are either that
// membership itself, or an equality to an integer witness followed by its Z
// membership. Example: cos(3*pi/2) = 0, with offset = 1 and 1 in Z.
pub struct CosZeroIntegerOffsetStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Equal-length tuples are equal when every corresponding component is equal.
// Example: (1 + 3, 2 + 4) = (4, 6), with two checked calculation children.
pub struct TupleComponentEqualityStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Same arithmetic constructor, with every operand equality proved separately.
// Example: (1,2)[1] + (3,4)[1] = 1 + 3, using checked tuple projections.
pub struct ArithmeticCongruenceStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
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

// Rational complex identities use i²=-1 only after every denominator / negative
// power base has checked nonzero evidence. Example: 1/i = -i; never 1/i = -1.
pub struct ComplexWithNonzeroPremisesStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
