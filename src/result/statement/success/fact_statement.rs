//! Successful factual statement outcome.

use crate::prelude::*;
use std::fmt;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

/// Successful output of executing one fact statement. Verification and store
/// are explicit child results owned by the statement layer.
pub struct SuccessFactStmtResult {
    pub verification: Rc<SuccessVerifyFactResult>,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    pub store: SuccessStoreFactResult,
    pub execution_trace: Option<StatementExecutionTrace>,
}

impl SuccessFactStmtResult {
    pub fn new(statement: Fact, infers: SuccessInferResult, proof: SuccessFactProofResult) -> Self {
        Self {
            verification: Rc::new(SuccessVerifyFactResult::new(statement.clone(), proof)),
            well_definedness: SuccessVerifyFactWellDefinedResult::default(),
            store: SuccessStoreFactResult::new(statement, infers),
            execution_trace: None,
        }
    }

    pub fn fact(&self) -> Fact {
        self.verification.as_ref().fact()
    }

    pub fn proof(&self) -> &SuccessFactProofResult {
        self.verification.as_ref().proof()
    }

    pub fn with_verified_fact(mut self, statement: Fact) -> Self {
        let source = self.verification;
        self.verification = Rc::new(SuccessVerifyFactResult::new(
            statement.clone(),
            SuccessFactProofResult::Reuse(Box::new(SuccessReuseFactProofResult { source })),
        ));
        self.store.fact = statement;
        self
    }
}

impl Deref for SuccessFactStmtResult {
    type Target = SuccessStoreFactResult;

    fn deref(&self) -> &Self::Target {
        &self.store
    }
}

impl DerefMut for SuccessFactStmtResult {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.store
    }
}

impl fmt::Debug for SuccessFactStmtResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessFactStmtResult")
            .field("verification", &self.verification)
            .field("well_definedness", &self.well_definedness)
            .field("store", &self.store)
            .field("execution_trace", &self.execution_trace)
            .finish()
    }
}
