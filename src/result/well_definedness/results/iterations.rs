//! Iteration domain, carrier, interval, and coverage checks.

use crate::prelude::*;
use std::fmt;
use std::rc::Rc;

#[derive(Debug)]
pub struct SuccessVerifyIterationWellDefinedResult {
    pub operation: String,
    pub scalar_return: Option<Box<SuccessVerifyIterationScalarReturnResult>>,
    pub interval: Box<SuccessVerifyIterationIntervalResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyIterationScalarReturnResult {
    pub parameter_carriers: Vec<SuccessVerifyChildObjWellDefinedResult>,
    pub parameters: Vec<SuccessVerifyBinderPremiseResult>,
    pub domains: Vec<SuccessVerifyBinderPremiseResult>,
    pub return_carrier: SuccessVerifyChildObjWellDefinedResult,
    pub return_subset: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub enum SuccessVerifyIterationCoverageResult {
    UniversalIntegerCarrier(Box<SuccessVerifyUniversalIntegerCarrierCoverageResult>),
    Enumerated(Box<SuccessVerifyEnumeratedIterationCoverageResult>),
    Endpoint(Box<SuccessVerifyEndpointIterationCoverageResult>),
    IntervalSubset(Box<SuccessVerifyIntervalSubsetCoverageResult>),
}

pub struct SuccessVerifyUniversalIntegerCarrierCoverageResult {
    pub parameter_set: Obj,
}

#[derive(Debug)]
pub struct SuccessVerifyEnumeratedIterationCoverageResult {
    pub checks: Vec<SuccessVerifyFactForObjWellDefinedResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyEndpointIterationCoverageResult {
    pub check: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyIntervalSubsetCoverageResult {
    pub check: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyIterationDomainResult {
    pub proposition: Fact,
    pub verification: Rc<SuccessFactProofNode>,
    pub store: SuccessStoreFactResult,
}

pub struct SuccessVerifyIterationIntervalResult {
    pub parameter_set: Obj,
    pub coverage: SuccessVerifyIterationCoverageResult,
    pub parameter_carriers: Vec<SuccessVerifyChildObjWellDefinedResult>,
    pub parameters: Vec<SuccessVerifyBinderPremiseResult>,
    pub lower_bound: SuccessStoreFactResult,
    pub upper_bound: SuccessStoreFactResult,
    pub domains: Vec<SuccessVerifyIterationDomainResult>,
    pub return_carrier: SuccessVerifyChildObjWellDefinedResult,
    pub body: Option<SuccessVerifyChildObjWellDefinedResult>,
    pub body_membership: Option<SuccessVerifyObjTargetRequirementResult>,
}

impl fmt::Debug for SuccessVerifyUniversalIntegerCarrierCoverageResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyUniversalIntegerCarrierCoverageResult")
            .field("parameter_set", &self.parameter_set.to_string())
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyIterationIntervalResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyIterationIntervalResult")
            .field("parameter_set", &self.parameter_set.to_string())
            .field("coverage", &self.coverage)
            .field("parameter_carriers", &self.parameter_carriers)
            .field("parameters", &self.parameters)
            .field("lower_bound", &self.lower_bound)
            .field("upper_bound", &self.upper_bound)
            .field("domains", &self.domains)
            .field("return_carrier", &self.return_carrier)
            .field("body", &self.body)
            .field("body_membership", &self.body_membership)
            .finish()
    }
}
