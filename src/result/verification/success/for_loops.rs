//! Range and Cartesian-product for-loop proof outcomes.

use crate::prelude::*;
use std::fmt;

pub struct SuccessVerifyByForRangesResult {
    pub parameters: Vec<SuccessVerifyByForRangeParameterResult>,
    pub prove_goal: String,
    pub assignments: Vec<SuccessVerifyByAssignmentResult>,
    pub generated_forall: String,
}

pub struct SuccessVerifyByForRangeParameterResult {
    pub parameter: String,
    pub range: ClosedRangeOrRange,
    pub evaluated_start: String,
    pub evaluated_end: String,
    pub enumerated_values: Vec<String>,
}

pub struct SuccessVerifyByForCartesianProductOfListSetsResult {
    pub parameter: String,
    pub factors: Vec<ListSet>,
    pub prove_goal: String,
    pub assignments: Vec<SuccessVerifyByAssignmentResult>,
    pub generated_forall: String,
}

pub enum SuccessVerifyByForResult {
    Ranges(Box<SuccessVerifyByForRangesResult>),
    CartesianProductOfListSets(Box<SuccessVerifyByForCartesianProductOfListSetsResult>),
}

impl fmt::Debug for SuccessVerifyByForRangesResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByForRangesResult")
            .field("parameters", &self.parameters)
            .field("prove_goal", &self.prove_goal)
            .field("assignments", &self.assignments)
            .field("generated_forall", &self.generated_forall)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByForRangeParameterResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByForRangeParameterResult")
            .field("parameter", &self.parameter)
            .field("range", &self.range.to_string())
            .field("evaluated_start", &self.evaluated_start)
            .field("evaluated_end", &self.evaluated_end)
            .field("enumerated_values", &self.enumerated_values)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByForCartesianProductOfListSetsResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByForCartesianProductOfListSetsResult")
            .field("parameter", &self.parameter)
            .field(
                "factors",
                &self
                    .factors
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

impl fmt::Debug for SuccessVerifyByForResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Ranges(result) => result.fmt(f),
            Self::CartesianProductOfListSets(result) => result.fmt(f),
        }
    }
}

impl SuccessVerifyByForResult {
    pub fn assignments(&self) -> &[SuccessVerifyByAssignmentResult] {
        match self {
            Self::Ranges(result) => &result.assignments,
            Self::CartesianProductOfListSets(result) => &result.assignments,
        }
    }

    pub fn assignments_mut(&mut self) -> &mut Vec<SuccessVerifyByAssignmentResult> {
        match self {
            Self::Ranges(result) => &mut result.assignments,
            Self::CartesianProductOfListSets(result) => &mut result.assignments,
        }
    }

    pub fn into_assignments(self) -> Vec<SuccessVerifyByAssignmentResult> {
        match self {
            Self::Ranges(result) => result.assignments,
            Self::CartesianProductOfListSets(result) => result.assignments,
        }
    }

    pub fn ranges(
        parameters: Vec<SuccessVerifyByForRangeParameterResult>,
        prove_goal: String,
        assignments: Vec<SuccessVerifyByAssignmentResult>,
        generated_forall: String,
    ) -> Self {
        Self::Ranges(Box::new(SuccessVerifyByForRangesResult {
            parameters,
            prove_goal,
            assignments,
            generated_forall,
        }))
    }

    pub fn cartesian_product_of_list_sets(
        parameter: String,
        factors: Vec<ListSet>,
        prove_goal: String,
        assignments: Vec<SuccessVerifyByAssignmentResult>,
        generated_forall: String,
    ) -> Self {
        Self::CartesianProductOfListSets(Box::new(
            SuccessVerifyByForCartesianProductOfListSetsResult {
                parameter,
                factors,
                prove_goal,
                assignments,
                generated_forall,
            },
        ))
    }
}
