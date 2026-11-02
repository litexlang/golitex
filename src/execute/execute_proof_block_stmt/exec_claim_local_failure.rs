//! Already completed claim stages and the detached, unaccepted proof scope.
use crate::prelude::*;

pub struct ExecClaimLocalFailure {
    pub statement: crate::ast::stmt::ClaimStmt,
    pub goal_wd: VerifyFactWellDefinedResult,
    pub body: ExecClaimBodyFailed,
    pub local_env: Box<ExecEnv>,
}

impl ExecClaimLocalFailure {
    pub fn new(
        statement: crate::ast::stmt::ClaimStmt,
        goal_wd: VerifyFactWellDefinedResult,
        body: ExecClaimBodyFailed,
        local_env: Box<ExecEnv>,
    ) -> Self {
        Self {
            statement,
            goal_wd,
            body,
            local_env,
        }
    }
}

pub enum ExecClaimBodyFailed {
    NonForall(ExecClaimNonForallFailed),
    Forall(ExecClaimForallFailed),
}

pub enum ExecClaimNonForallFailed {
    ProofBody(super::result::ProofBlockBodyFailed),
    Conclusion {
        proof_steps: Vec<ExecStmtResult>,
        result: VerifyFactResult,
    },
}

pub enum ExecClaimForallFailed {
    Introduce(crate::execute::IntroduceTypedParametersFailed),
    Entered {
        introduced_params: IntroduceTypedParametersResult,
        assumed_dom_facts: Vec<AssumeDomFactResult>,
        failure: ExecClaimForallEnteredFailed,
    },
}

pub enum ExecClaimForallEnteredFailed {
    PremiseWd {
        index: usize,
        result: VerifyFactWellDefinedResult,
    },
    ProofBody(super::result::ProofBlockBodyFailed),
    Conclusion {
        proof_steps: Vec<ExecStmtResult>,
        conclusion_proofs: Vec<VerifyFactResult>,
        index: usize,
        result: VerifyFactResult,
    },
}
