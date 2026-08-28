//! Finite sum and product well-definedness modes.

use crate::prelude::*;
use std::fmt;

#[derive(Debug)]
pub struct SuccessVerifyFiniteAggregateWellDefinedResult {
    pub operation: String,
    pub scalar_return: Option<Box<SuccessVerifyIterationScalarReturnResult>>,
    pub mode: SuccessVerifyFiniteAggregateModeResult,
}

#[derive(Debug)]
pub enum SuccessVerifyFiniteAggregateModeResult {
    Empty(Box<SuccessVerifyEmptyFiniteAggregateResult>),
    Elements(Box<SuccessVerifyFiniteAggregateElementsResult>),
    ClosedRange(Box<SuccessVerifyFiniteAggregateClosedRangeResult>),
    Symbolic(Box<SuccessVerifySymbolicFiniteAggregateResult>),
}

#[derive(Debug)]
pub struct SuccessVerifyEmptyFiniteAggregateResult {
    pub empty_set: SuccessVerifyFactForObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyFiniteAggregateElementsResult {
    pub body_memberships: Vec<SuccessVerifyFactForObjWellDefinedResult>,
    pub applications: Vec<SuccessVerifyChildObjWellDefinedResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyFiniteAggregateClosedRangeResult {
    pub aggregate_dependency: SuccessVerifyChildObjWellDefinedResult,
}

pub struct SuccessVerifySymbolicFiniteAggregateResult {
    pub exact_domain: Obj,
}

impl fmt::Debug for SuccessVerifySymbolicFiniteAggregateResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifySymbolicFiniteAggregateResult")
            .field("exact_domain", &self.exact_domain.to_string())
            .finish()
    }
}
