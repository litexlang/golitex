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

pub struct SuccessCheckedGoalBlockResult {
    pub fact: Fact,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    pub domain: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<StmtResult>,
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

impl SuccessCheckedGoalBlockResult {
    pub fn new(
        fact: Fact,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        domain: SuccessVerifyLocalProofScopeResult,
        proof_steps: Vec<StmtResult>,
        conclusion_checks: Vec<StmtResult>,
    ) -> Self {
        SuccessCheckedGoalBlockResult {
            fact,
            well_definedness,
            domain,
            proof_steps,
            conclusion_checks,
        }
    }
}

impl fmt::Debug for SuccessCheckedGoalBlockResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessCheckedGoalBlockResult")
            .field("fact", &self.fact.to_string())
            .field("well_definedness", &self.well_definedness)
            .field("domain", &self.domain)
            .field("proof_steps", &self.proof_steps)
            .field("conclusion_checks", &self.conclusion_checks)
            .finish()
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
