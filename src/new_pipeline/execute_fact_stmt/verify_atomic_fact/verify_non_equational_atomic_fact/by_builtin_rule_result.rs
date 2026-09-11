use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

// Each builtin rule gets its own variant and payload struct.
pub enum NonEquationalAtomicFactSearchProofByBuiltinRule2 {
    ClosedNumericComparison(NonEquationalAtomicFactSearchProofByClosedNumericComparison2),
    OrderReflexivity(NonEquationalAtomicFactSearchProofByOrderReflexivity2),
    ClosedNumericMembership(NonEquationalAtomicFactSearchProofByClosedNumericMembership2),
    SetBuilderMembership(NonEquationalAtomicFactSearchProofBySetBuilderMembership2),
    NotEqualSymmetry(NonEquationalAtomicFactSearchProofByNotEqualSymmetry2),
}

// Closed numeric comparison by evaluation, e.g. prove `1 < 2`.
pub struct NonEquationalAtomicFactSearchProofByClosedNumericComparison2 {}

// Order reflexivity on one object, e.g. prove `x <= x`.
pub struct NonEquationalAtomicFactSearchProofByOrderReflexivity2 {
    pub repeated_object: Obj,
}

// Closed numeric membership by evaluation, e.g. prove `2 $in N`.
pub struct NonEquationalAtomicFactSearchProofByClosedNumericMembership2 {}

// Set-builder membership from base membership plus defining facts.
// Example: prove `x $in {t R: t > 0}` from `x $in R` and `x > 0`.
pub struct NonEquationalAtomicFactSearchProofBySetBuilderMembership2 {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}

// Not-equal symmetry, e.g. prove `a != b` from a proved `b != a`.
pub struct NonEquationalAtomicFactSearchProofByNotEqualSymmetry2 {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult2,
}
