//! Theorem and claim verification outcomes.

use crate::prelude::*;
use std::fmt;

pub struct SuccessVerifyTheoremResult {
    pub name: String,
    pub forall_fact: ForallFact,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<StmtResult>,
}

pub enum SuccessVerifyClaimResult {
    Forall(Box<SuccessVerifyClaimForallResult>),
    Fact(Box<SuccessVerifyClaimFactResult>),
}

pub struct SuccessVerifyClaimForallResult {
    pub forall_fact: ForallFact,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<StmtResult>,
}

pub struct SuccessVerifyClaimFactResult {
    pub fact: Fact,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_check: Box<StmtResult>,
}

impl SuccessVerifyTheoremResult {
    pub fn new(
        name: String,
        forall_fact: ForallFact,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        proof_scope: SuccessVerifyLocalProofScopeResult,
        proof_steps: Vec<StmtResult>,
        conclusion_checks: Vec<StmtResult>,
    ) -> Self {
        SuccessVerifyTheoremResult {
            name,
            forall_fact,
            well_definedness,
            proof_scope,
            proof_steps,
            conclusion_checks,
        }
    }
}

impl SuccessVerifyClaimForallResult {
    pub fn new(
        forall_fact: ForallFact,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        proof_scope: SuccessVerifyLocalProofScopeResult,
        proof_steps: Vec<StmtResult>,
        conclusion_checks: Vec<StmtResult>,
    ) -> Self {
        SuccessVerifyClaimForallResult {
            forall_fact,
            well_definedness,
            proof_scope,
            proof_steps,
            conclusion_checks,
        }
    }
}

impl SuccessVerifyClaimFactResult {
    pub fn new(
        fact: Fact,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        proof_scope: SuccessVerifyLocalProofScopeResult,
        proof_steps: Vec<StmtResult>,
        conclusion_check: StmtResult,
    ) -> Self {
        SuccessVerifyClaimFactResult {
            fact,
            well_definedness,
            proof_scope,
            proof_steps,
            conclusion_check: Box::new(conclusion_check),
        }
    }
}

impl From<SuccessVerifyClaimForallResult> for SuccessVerifyClaimResult {
    fn from(v: SuccessVerifyClaimForallResult) -> Self {
        SuccessVerifyClaimResult::Forall(Box::new(v))
    }
}

impl From<SuccessVerifyClaimFactResult> for SuccessVerifyClaimResult {
    fn from(v: SuccessVerifyClaimFactResult) -> Self {
        SuccessVerifyClaimResult::Fact(Box::new(v))
    }
}

impl fmt::Debug for SuccessVerifyClaimResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            SuccessVerifyClaimResult::Forall(v) => f.debug_tuple("Forall").field(v).finish(),
            SuccessVerifyClaimResult::Fact(v) => f.debug_tuple("Fact").field(v).finish(),
        }
    }
}

impl fmt::Debug for SuccessVerifyTheoremResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyTheoremResult")
            .field("name", &self.name)
            .field("forall_fact", &self.forall_fact.to_string())
            .field("well_definedness", &self.well_definedness)
            .field("proof_scope", &self.proof_scope)
            .field("proof_steps", &self.proof_steps)
            .field("conclusion_checks", &self.conclusion_checks)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyClaimForallResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyClaimForallResult")
            .field("forall_fact", &self.forall_fact.to_string())
            .field("well_definedness", &self.well_definedness)
            .field("proof_scope", &self.proof_scope)
            .field("proof_steps", &self.proof_steps)
            .field("conclusion_checks", &self.conclusion_checks)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyClaimFactResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyClaimFactResult")
            .field("fact", &self.fact.to_string())
            .field("well_definedness", &self.well_definedness)
            .field("proof_scope", &self.proof_scope)
            .field("proof_steps", &self.proof_steps)
            .field("conclusion_check", &self.conclusion_check)
            .finish()
    }
}
