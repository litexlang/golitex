//! Successful factual statement outcome.

use crate::prelude::*;
use std::fmt;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

/// Proof-phase output for one fact. It has no statement identity and cannot
/// allocate a persistent FactId. `store` retains only proof-local inference
/// effects until those effects are migrated into named proof nodes.
pub struct SuccessProveFactResult {
    pub verification: Rc<SuccessFactProofNode>,
    pub store: SuccessStoreFactResult,
}

impl SuccessProveFactResult {
    pub fn new(statement: Fact, infers: SuccessInferResult, proof: SuccessFactProofResult) -> Self {
        Self {
            verification: Rc::new(SuccessFactProofNode::new(statement.clone(), proof)),
            store: SuccessStoreFactResult::new(statement, infers),
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
        self.verification = Rc::new(SuccessFactProofNode::new(
            statement.clone(),
            SuccessFactProofResult::Reuse(Box::new(SuccessReuseFactProofResult { source })),
        ));
        self.store.fact = statement;
        self
    }
}

impl Deref for SuccessProveFactResult {
    type Target = SuccessStoreFactResult;

    fn deref(&self) -> &Self::Target {
        &self.store
    }
}

impl DerefMut for SuccessProveFactResult {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.store
    }
}

impl fmt::Debug for SuccessProveFactResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessProveFactResult")
            .field("verification", &self.verification)
            .field("store", &self.store)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct TrustedFactResult {
    pub fact: Fact,
}

#[derive(Debug)]
pub enum FactStatementEvidence {
    Verified(Rc<VerifiedFactResult>),
    Trusted(TrustedFactResult),
}

/// Successful execution of one factual statement. Verification is complete
/// before this layer performs the persistent store/inference transition.
pub struct SuccessFactStmtResult {
    pub evidence: FactStatementEvidence,
    pub store: SuccessStoreFactResult,
}

impl SuccessFactStmtResult {
    pub fn verified(verification: Rc<VerifiedFactResult>, store: SuccessStoreFactResult) -> Self {
        Self {
            evidence: FactStatementEvidence::Verified(verification),
            store,
        }
    }

    pub fn trusted(fact: Fact, infers: SuccessInferResult) -> Self {
        Self {
            evidence: FactStatementEvidence::Trusted(TrustedFactResult { fact: fact.clone() }),
            store: SuccessStoreFactResult::new(fact, infers),
        }
    }

    pub fn fact(&self) -> Fact {
        match &self.evidence {
            FactStatementEvidence::Verified(result) => result.fact(),
            FactStatementEvidence::Trusted(result) => result.fact.clone(),
        }
    }

    pub fn verification(&self) -> Option<&Rc<VerifiedFactResult>> {
        match &self.evidence {
            FactStatementEvidence::Verified(result) => Some(result),
            FactStatementEvidence::Trusted(_) => None,
        }
    }

    pub fn verification_mut(&mut self) -> Option<&mut VerifiedFactResult> {
        match &mut self.evidence {
            FactStatementEvidence::Verified(result) => Rc::get_mut(result),
            FactStatementEvidence::Trusted(_) => None,
        }
    }

    pub fn checked(&self) -> Option<&WellDefinedFactResult> {
        self.verification().map(|result| &result.checked)
    }

    pub fn proof(&self) -> Option<&SuccessFactProofResult> {
        self.verification().map(|result| result.proof())
    }

    pub fn is_trusted(&self) -> bool {
        matches!(self.evidence, FactStatementEvidence::Trusted(_))
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
            .field("evidence", &self.evidence)
            .field("store", &self.store)
            .finish()
    }
}
