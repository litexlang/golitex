//! Integer and finite-set induction outcomes.

use crate::prelude::*;
use std::fmt;

pub struct SuccessVerifyByInducResult {
    pub parameter_binding: SymbolBinding,
    pub parameter: Obj,
    pub prove_goals: Vec<Fact>,
    pub generated_forall: ForallFact,
    pub proof: SuccessVerifyByInducProofResult,
}

#[derive(Debug)]
pub enum SuccessVerifyByInducProofResult {
    IntegerUnstructured(Box<SuccessVerifyByUnstructuredIntegerInducResult>),
    IntegerStructured(Box<SuccessVerifyByStructuredIntegerInducResult>),
    FiniteSet(Box<SuccessVerifyByFiniteSetInducResult>),
}

#[derive(Debug)]
pub struct SuccessVerifyByUnstructuredIntegerInducResult {
    pub strong: bool,
    pub start: String,
    pub base_assumptions: Vec<(String, String)>,
    pub step_assumptions: Vec<(String, String)>,
    pub proof_steps: Vec<StmtResult>,
    pub goals: Vec<SuccessVerifyByInducGoalResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyByInducGoalResult {
    pub source_goal: Fact,
    pub base_check: Box<StmtResult>,
    pub start_in_z_check: Box<StmtResult>,
    pub step_check: Box<StmtResult>,
    pub infers: SuccessInferResult,
}

pub struct SuccessVerifyByStructuredIntegerInducResult {
    pub strong: bool,
    pub start: Obj,
    pub start_in_z_check: Box<StmtResult>,
    pub base: SuccessVerifyByStructuredIntegerInducCaseResult,
    pub step: SuccessVerifyByStructuredIntegerInducCaseResult,
}

impl fmt::Debug for SuccessVerifyByInducResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByInducResult")
            .field("parameter_binding", &self.parameter_binding)
            .field("parameter", &self.parameter.to_string())
            .field(
                "prove_goals",
                &self
                    .prove_goals
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .field("generated_forall", &self.generated_forall.to_string())
            .field("proof", &self.proof)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyByStructuredIntegerInducResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByStructuredIntegerInducResult")
            .field("strong", &self.strong)
            .field("start", &self.start.to_string())
            .field("start_in_z_check", &self.start_in_z_check)
            .field("base", &self.base)
            .field("step", &self.step)
            .finish()
    }
}

#[derive(Debug)]
pub struct SuccessVerifyByStructuredIntegerInducCaseResult {
    pub assumptions: Vec<SuccessVerifyByInducAssumptionResult>,
    pub assumption_infers: SuccessInferResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusions: Vec<SuccessVerifyByInducConclusionResult>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SuccessVerifyByInducAssumptionRole {
    ParameterType,
    BaseCaseEquality,
    DomainLowerBound,
    CarrierConstraint,
    FreshInsertionElement,
    InductionHypothesis,
    StrongInductionHypothesis,
}

#[derive(Debug)]
pub struct SuccessVerifyByInducAssumptionResult {
    pub fact: Fact,
    pub fact_id: FactId,
    pub role: SuccessVerifyByInducAssumptionRole,
    pub goal_index: Option<usize>,
}

#[derive(Debug)]
pub struct SuccessVerifyByInducConclusionResult {
    pub goal: Fact,
    pub check: Box<StmtResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyByFiniteSetInducResult {
    pub base: SuccessVerifyByInducCaseResult,
    pub step: SuccessVerifyByInducCaseResult,
}

#[derive(Debug)]
pub struct SuccessVerifyByInducCaseResult {
    pub assumptions: Vec<SuccessVerifyByInducAssumptionResult>,
    pub assumption_infers: SuccessInferResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusions: Vec<SuccessVerifyByInducConclusionResult>,
}

impl SuccessVerifyByInducResult {
    pub fn new(
        parameter_binding: SymbolBinding,
        parameter: Obj,
        prove_goals: Vec<Fact>,
        generated_forall: ForallFact,
        proof: SuccessVerifyByInducProofResult,
    ) -> Self {
        SuccessVerifyByInducResult {
            parameter_binding,
            parameter,
            prove_goals,
            generated_forall,
            proof,
        }
    }
}
