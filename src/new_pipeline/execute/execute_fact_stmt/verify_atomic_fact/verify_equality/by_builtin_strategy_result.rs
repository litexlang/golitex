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

// Prove an equality about min/max (or similar extremum) by discharging side
// conditions. (Search not wired yet.)
pub struct ExtremumEqualityStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Prove pointwise equality on a finite cartesian product by discharging
// component requirements. (Search not wired yet.)
pub struct FiniteSetProductPointwiseEqualityStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Prove a congruence equality modulo n by discharging side conditions.
// (Search not wired yet.)
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
