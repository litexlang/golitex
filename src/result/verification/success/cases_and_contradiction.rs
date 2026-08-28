//! Cases, contradiction, and local proof-scope outcomes.

use crate::prelude::*;
use std::fmt;

pub struct SuccessVerifyByCasesResult {
    /// Well-definedness of each exported goal, checked before any case-local
    /// assumptions are installed. This is intentionally separate from the
    /// branch conclusion checks below: it is the evidence needed to form the
    /// statement's result outside every branch scope.
    pub goal_well_definedness: Vec<SuccessVerifyFactWellDefinedResult>,
    pub coverage_check: Box<StmtResult>,
    pub then_facts: Vec<Fact>,
    pub branches: Vec<SuccessVerifyByCaseBranchResult>,
}

pub struct SuccessVerifyByCaseBranchResult {
    pub assumption: AndChainAtomicFact,
    pub assumption_fact_id: FactId,
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub exit: SuccessVerifyByCaseBranchExitResult,
}

pub enum SuccessVerifyByCaseBranchExitResult {
    Conclusions(Box<SuccessVerifyByCaseConclusionsResult>),
    Contradiction(Box<SuccessVerifyByCaseContradictionResult>),
}

pub struct SuccessVerifyByCaseConclusionsResult {
    pub checks: Vec<StmtResult>,
}

pub struct SuccessVerifyByCaseContradictionResult {
    pub impossible_fact: AtomicFact,
    pub contradiction: SuccessVerifyContradictionResult,
}

pub struct SuccessVerifyByContraResult {
    pub to_prove: Fact,
    pub reverse_assumption: Fact,
    /// Stable ID of the temporary reverse assumption while the contradiction
    /// proof environment was alive.
    pub reverse_assumption_fact_id: FactId,
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub impossible_fact: AtomicFact,
    pub contradiction: SuccessVerifyContradictionResult,
}

#[derive(Debug)]
pub struct SuccessVerifyContradictionResult {
    pub impossible_check: Box<StmtResult>,
    pub negated_impossible_check: Box<StmtResult>,
}

#[derive(Clone, Debug)]
pub struct SuccessVerifyLocalProofScopeResult {
    pub assumption_infers: SuccessInferResult,
    pub assumption_components: Vec<(FactId, Fact)>,
}

impl SuccessVerifyLocalProofScopeResult {
    pub fn new(
        assumption_infers: SuccessInferResult,
        assumption_components: Vec<(FactId, Fact)>,
    ) -> Self {
        Self {
            assumption_infers,
            assumption_components,
        }
    }
}

impl SuccessVerifyByCasesResult {
    pub fn new(
        goal_well_definedness: Vec<SuccessVerifyFactWellDefinedResult>,
        coverage_check: StmtResult,
        then_facts: Vec<Fact>,
        branches: Vec<SuccessVerifyByCaseBranchResult>,
    ) -> Self {
        SuccessVerifyByCasesResult {
            goal_well_definedness,
            coverage_check: Box::new(coverage_check),
            then_facts,
            branches,
        }
    }
}

impl SuccessVerifyByContraResult {
    pub fn new(
        to_prove: Fact,
        reverse_assumption: Fact,
        reverse_assumption_fact_id: FactId,
        proof_scope: SuccessVerifyLocalProofScopeResult,
        proof_steps: Vec<StmtResult>,
        impossible_fact: AtomicFact,
        contradiction: SuccessVerifyContradictionResult,
    ) -> Self {
        SuccessVerifyByContraResult {
            to_prove,
            reverse_assumption,
            reverse_assumption_fact_id,
            proof_scope,
            proof_steps,
            impossible_fact,
            contradiction,
        }
    }
}

impl fmt::Debug for SuccessVerifyByCasesResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let cases = self
            .branches
            .iter()
            .map(|branch| branch.assumption.to_string())
            .collect::<Vec<_>>();
        let then_facts = self
            .then_facts
            .iter()
            .map(|fact| fact.to_string())
            .collect::<Vec<_>>();
        f.debug_struct("SuccessVerifyByCasesResult")
            .field("goal_well_definedness", &self.goal_well_definedness)
            .field("coverage_check", &self.coverage_check)
            .field("cases", &cases)
            .field("then_facts", &then_facts)
            .field("branches", &self.branches)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByCaseBranchResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByCaseBranchResult")
            .field("assumption", &self.assumption.to_string())
            .field("assumption_fact_id", &self.assumption_fact_id)
            .field("proof_scope", &self.proof_scope)
            .field("proof_steps", &self.proof_steps)
            .field("exit", &self.exit)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByCaseBranchExitResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Conclusions(result) => f.debug_tuple("Conclusions").field(result).finish(),
            Self::Contradiction(result) => f.debug_tuple("Contradiction").field(result).finish(),
        }
    }
}

impl fmt::Debug for SuccessVerifyByCaseConclusionsResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByCaseConclusionsResult")
            .field("checks", &self.checks)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByCaseContradictionResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByCaseContradictionResult")
            .field("impossible_fact", &self.impossible_fact.to_string())
            .field("contradiction", &self.contradiction)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByContraResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByContraResult")
            .field("to_prove", &self.to_prove.to_string())
            .field("reverse_assumption", &self.reverse_assumption.to_string())
            .field(
                "reverse_assumption_fact_id",
                &self.reverse_assumption_fact_id,
            )
            .field("proof_scope", &self.proof_scope)
            .field("proof_steps", &self.proof_steps)
            .field("impossible_fact", &self.impossible_fact.to_string())
            .field("contradiction", &self.contradiction)
            .finish()
    }
}
