//! Conjunction, chain, and disjunction well-definedness results.

use crate::prelude::*;
use std::fmt;

pub struct SuccessVerifyAndFactWellDefinedResult {
    pub statement: AndFact,
    pub conjuncts: Vec<SuccessVerifyFactWellDefinedProofResult>,
}

pub struct SuccessVerifyChainFactWellDefinedResult {
    pub statement: ChainFact,
    pub comparisons: Vec<SuccessVerifyFactWellDefinedProofResult>,
}

pub struct SuccessVerifyOrFactWellDefinedResult {
    pub statement: OrFact,
    pub branches: Vec<SuccessVerifyFactWellDefinedProofResult>,
}

impl fmt::Debug for SuccessVerifyAndFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyAndFactWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("conjuncts", &self.conjuncts)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyChainFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyChainFactWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("comparisons", &self.comparisons)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyOrFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyOrFactWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("branches", &self.branches)
            .finish()
    }
}
