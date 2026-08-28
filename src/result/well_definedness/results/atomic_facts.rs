//! Atomic fact and predicate-domain well-definedness results.

use crate::prelude::*;
use std::fmt;

pub struct SuccessVerifyAtomicFactWellDefinedResult {
    pub statement: AtomicFact,
    pub arguments: Vec<SuccessVerifyFactObjectWellDefinedResult>,
    pub predicate: SuccessVerifyAtomicPredicateWellDefinedResult,
}

impl SuccessVerifyAtomicFactWellDefinedResult {
    pub fn new(
        statement: AtomicFact,
        arguments: Vec<SuccessVerifyFactObjectWellDefinedResult>,
        predicate: SuccessVerifyAtomicPredicateWellDefinedResult,
    ) -> Self {
        Self {
            statement,
            arguments,
            predicate,
        }
    }
}

pub struct SuccessVerifyAtomicPredicateWellDefinedResult {
    pub name: String,
    pub expected_arity: usize,
    pub domain_checks: Vec<SuccessVerifyAtomicPredicateDomainCheckResult>,
}

pub struct SuccessVerifyAtomicPredicateDomainCheckResult {
    pub role: AtomicPredicateDomainCheckRole,
    pub result: Box<StmtResult>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AtomicPredicateDomainCheckRole {
    ChoiceFunctionIndexSet,
    ChoiceFunctionFamilySet,
    ChoiceFunctionFamily,
    ChoiceFunctionMember,
    PrimeNaturalArgument,
    CoprimeNaturalArgument,
    DivisibilityIntegerArgument,
    DivisibilityNonzeroIntegerArgument,
    OrderedRealCarrierEvidence,
    FunctionPropertySignature,
}

impl fmt::Debug for SuccessVerifyAtomicFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyAtomicFactWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("arguments", &self.arguments)
            .field("predicate", &self.predicate)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyAtomicPredicateWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyAtomicPredicateWellDefinedResult")
            .field("name", &self.name)
            .field("expected_arity", &self.expected_arity)
            .field("domain_checks", &self.domain_checks)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyAtomicPredicateDomainCheckResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyAtomicPredicateDomainCheckResult")
            .field("role", &self.role)
            .field("result", &self.result)
            .finish()
    }
}
