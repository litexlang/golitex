//! General and finite reduction well-definedness checks.

use crate::prelude::*;
use std::fmt;

pub struct SuccessVerifyReduceWellDefinedResult {
    pub operation: String,
    pub signature: SuccessVerifyReduceOperationSignatureResult,
    pub iterand_return_carrier: Obj,
    pub seed_membership: SuccessVerifyFactForObjWellDefinedResult,
    pub operation_laws: Option<Box<SuccessVerifyFiniteReduceOperationLawsResult>>,
    pub mode: SuccessVerifyReduceModeResult,
}

pub struct SuccessVerifyReduceOperationSignatureResult {
    pub left_parameter_carrier: Obj,
    pub right_parameter_carrier: Obj,
    pub return_carrier: Obj,
}

#[derive(Debug)]
pub enum SuccessVerifyReduceModeResult {
    Empty(Box<SuccessVerifyEmptyReduceResult>),
    Interval(Box<SuccessVerifyIntervalReduceResult>),
    Elements(Box<SuccessVerifyElementwiseReduceResult>),
    Symbolic(Box<SuccessVerifySymbolicReduceResult>),
}

#[derive(Debug)]
pub struct SuccessVerifyEmptyReduceResult {
    pub empty_range_or_set: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyIntervalReduceResult {
    pub interval: Box<SuccessVerifyIterationIntervalResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyElementwiseReduceResult {
    pub body_memberships: Vec<SuccessVerifyFactForObjWellDefinedResult>,
    pub applications: Vec<SuccessVerifyChildObjWellDefinedResult>,
}

#[derive(Debug)]
pub struct SuccessVerifySymbolicReduceResult {
    pub coverage: SuccessVerifyFiniteReduceDomainCoverageResult,
}

#[derive(Debug)]
pub enum SuccessVerifyFiniteReduceDomainCoverageResult {
    Exact(Box<SuccessVerifyExactFiniteReduceDomainResult>),
    Subset(Box<SuccessVerifySubsetFiniteReduceDomainResult>),
}

pub struct SuccessVerifyExactFiniteReduceDomainResult {
    pub aggregate_set: Obj,
    pub iterand_domain: Obj,
}

pub struct SuccessVerifySubsetFiniteReduceDomainResult {
    pub aggregate_set: Obj,
    pub iterand_domain: Obj,
    pub subset: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyFiniteReduceOperationLawsResult {
    pub parameter_carrier: SuccessVerifyChildObjWellDefinedResult,
    pub parameters: Vec<SuccessVerifyBinderPremiseResult>,
    pub associativity: SuccessVerifyFactForObjWellDefinedResult,
    pub commutativity: SuccessVerifyFactForObjWellDefinedResult,
}

impl fmt::Debug for SuccessVerifyReduceWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyReduceWellDefinedResult")
            .field("operation", &self.operation)
            .field("signature", &self.signature)
            .field(
                "iterand_return_carrier",
                &self.iterand_return_carrier.to_string(),
            )
            .field("seed_membership", &self.seed_membership)
            .field("operation_laws", &self.operation_laws)
            .field("mode", &self.mode)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyReduceOperationSignatureResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyReduceOperationSignatureResult")
            .field(
                "left_parameter_carrier",
                &self.left_parameter_carrier.to_string(),
            )
            .field(
                "right_parameter_carrier",
                &self.right_parameter_carrier.to_string(),
            )
            .field("return_carrier", &self.return_carrier.to_string())
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyExactFiniteReduceDomainResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyExactFiniteReduceDomainResult")
            .field("aggregate_set", &self.aggregate_set.to_string())
            .field("iterand_domain", &self.iterand_domain.to_string())
            .finish()
    }
}

impl fmt::Debug for SuccessVerifySubsetFiniteReduceDomainResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifySubsetFiniteReduceDomainResult")
            .field("aggregate_set", &self.aggregate_set.to_string())
            .field("iterand_domain", &self.iterand_domain.to_string())
            .field("subset", &self.subset)
            .finish()
    }
}
