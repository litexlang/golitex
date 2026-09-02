//! Integer-range enumeration proof outcomes.

use crate::prelude::*;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SuccessVerifyByEnumerateRangeEndpointPosition {
    Start,
    End,
}

pub struct SuccessVerifyByEnumerateRangeEndpointResult {
    pub position: SuccessVerifyByEnumerateRangeEndpointPosition,
    pub endpoint: Obj,
    pub integer_membership_fact: Fact,
    pub verification: Box<VerifyFactResult>,
}

pub struct SuccessVerifyByEnumerateRangeResult {
    pub element: Obj,
    pub range: ClosedRangeOrRange,
    pub membership_fact: Fact,
    pub generated_cases: Fact,
    pub membership_check: Box<VerifyFactResult>,
    pub endpoint_checks: Vec<SuccessVerifyByEnumerateRangeEndpointResult>,
}

impl fmt::Debug for SuccessVerifyByEnumerateRangeEndpointResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByEnumerateRangeEndpointResult")
            .field("position", &self.position)
            .field("endpoint", &self.endpoint.to_string())
            .field(
                "integer_membership_fact",
                &self.integer_membership_fact.to_string(),
            )
            .field("verification", &self.verification)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByEnumerateRangeResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByEnumerateRangeResult")
            .field("element", &self.element.to_string())
            .field("range", &self.range.to_string())
            .field("membership_fact", &self.membership_fact.to_string())
            .field("generated_cases", &self.generated_cases.to_string())
            .field("membership_check", &self.membership_check)
            .field("endpoint_checks", &self.endpoint_checks)
            .finish()
    }
}

impl SuccessVerifyByEnumerateRangeResult {
    pub fn new(
        element: Obj,
        range: ClosedRangeOrRange,
        membership_fact: Fact,
        generated_cases: Fact,
        membership_check: VerifyFactResult,
        endpoint_checks: Vec<SuccessVerifyByEnumerateRangeEndpointResult>,
    ) -> Self {
        SuccessVerifyByEnumerateRangeResult {
            element,
            range,
            membership_fact,
            generated_cases,
            membership_check: Box::new(membership_check),
            endpoint_checks,
        }
    }
}

impl SuccessVerifyByEnumerateRangeEndpointResult {
    pub fn new(
        position: SuccessVerifyByEnumerateRangeEndpointPosition,
        endpoint: Obj,
        integer_membership_fact: Fact,
        verification: VerifyFactResult,
    ) -> Self {
        Self {
            position,
            endpoint,
            integer_membership_fact,
            verification: Box::new(verification),
        }
    }
}
