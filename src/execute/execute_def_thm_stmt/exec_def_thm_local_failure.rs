//! Original theorem stages and the detached, unaccepted local proof scope.
use crate::execute::execute_proof_block_stmt::ProofBlockBodyFailed;
use crate::execute::IntroduceTypedParametersFailed;
use crate::prelude::*;

pub struct ExecDefThmLocalFailure {
    pub statement: DefThmStmt,
    pub goal_wd: VerifyFactWellDefinedResult,
    pub body: ExecDefThmBodyFailed,
    pub local_env: Box<ExecEnv>,
}

impl ExecDefThmLocalFailure {
    pub fn new(
        statement: DefThmStmt,
        goal_wd: VerifyFactWellDefinedResult,
        body: ExecDefThmBodyFailed,
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

pub enum ExecDefThmBodyFailed {
    NonForall(ExecDefThmNonForallFailed),
    Forall(ExecDefThmForallFailed),
}

pub enum ExecDefThmNonForallFailed {
    ProofBody(ProofBlockBodyFailed),
    Conclusion {
        proof_steps: Vec<ExecStmtResult>,
        result: VerifyFactResult,
    },
}

pub enum ExecDefThmForallFailed {
    Introduce(IntroduceTypedParametersFailed),
    Entered {
        introduced_params: IntroduceTypedParametersResult,
        assumed_dom_facts: Vec<AssumeDomFactResult>,
        failure: ExecDefThmForallEnteredFailed,
    },
}

pub enum ExecDefThmForallEnteredFailed {
    PremiseWd {
        index: usize,
        result: VerifyFactWellDefinedResult,
    },
    ProofBody(ProofBlockBodyFailed),
    Conclusion {
        proof_steps: Vec<ExecStmtResult>,
        conclusion_proofs: Vec<VerifyFactResult>,
        index: usize,
        result: VerifyFactResult,
    },
}
