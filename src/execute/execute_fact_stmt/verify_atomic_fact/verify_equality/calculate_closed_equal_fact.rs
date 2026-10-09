use crate::prelude::*;

// Pure closed evaluation, without Runtime, permissions or proof premises.
pub fn calculate_closed_equal_fact(fact: &EqualFact) -> Option<ClosedEqualityCalculationProof> {
    let (values, equal) = calculate_value_pair(&fact.left, &fact.right)?;
    equal.then_some(ClosedEqualityCalculationProof { values })
}
