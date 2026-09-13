use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

// Each builtin rule gets its own variant and payload struct.
pub enum NonEquationalAtomicFactSearchProofByBuiltinRule {
    ClosedNumericComparison(NonEquationalAtomicFactSearchProofByClosedNumericComparison),
    OrderReflexivity(NonEquationalAtomicFactSearchProofByOrderReflexivity),
    ClosedNumericMembership(NonEquationalAtomicFactSearchProofByClosedNumericMembership),
    SetBuilderMembership(NonEquationalAtomicFactSearchProofBySetBuilderMembership),
    NotEqualSymmetry(NonEquationalAtomicFactSearchProofByNotEqualSymmetry),
}

// Closed numeric comparison by evaluation, e.g. prove `1 < 2`.
pub struct NonEquationalAtomicFactSearchProofByClosedNumericComparison {}

// Order reflexivity on one object, e.g. prove `x <= x`.
pub struct NonEquationalAtomicFactSearchProofByOrderReflexivity {
    pub repeated_object: Obj,
}

// Closed numeric membership by evaluation, e.g. prove `2 $in N`.
pub struct NonEquationalAtomicFactSearchProofByClosedNumericMembership {}

// Set-builder membership from base membership plus defining facts.
// Example: prove `x $in {t R: t > 0}` from `x $in R` and `x > 0`.
pub struct NonEquationalAtomicFactSearchProofBySetBuilderMembership {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Not-equal symmetry, e.g. prove `a != b` from a proved `b != a`.
pub struct NonEquationalAtomicFactSearchProofByNotEqualSymmetry {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}
