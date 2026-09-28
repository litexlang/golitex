//! Finite-set enumeration proof outcomes.

use crate::prelude::*;
use std::fmt;

pub struct SuccessVerifyByEnumerateFiniteSetResult {
    pub parameters: Vec<String>,
    /// Exact list-set values selected by execution, including named source
    /// types that were resolved through equality before enumeration.
    pub parameter_sets: Vec<ListSet>,
    pub prove_goal: String,
    pub assignments: Vec<SuccessVerifyByAssignmentResult>,
    pub generated_forall: String,
}

impl fmt::Debug for SuccessVerifyByEnumerateFiniteSetResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByEnumerateFiniteSetResult")
            .field("parameters", &self.parameters)
            .field(
                "parameter_sets",
                &self
                    .parameter_sets
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .field("prove_goal", &self.prove_goal)
            .field("assignments", &self.assignments)
            .field("generated_forall", &self.generated_forall)
            .finish()
    }
}

impl SuccessVerifyByEnumerateFiniteSetResult {
    pub fn new(
        parameters: Vec<String>,
        parameter_sets: Vec<ListSet>,
        prove_goal: String,
        assignments: Vec<SuccessVerifyByAssignmentResult>,
        generated_forall: String,
    ) -> Self {
        SuccessVerifyByEnumerateFiniteSetResult {
            parameters,
            parameter_sets,
            prove_goal,
            assignments,
            generated_forall,
        }
    }
}
