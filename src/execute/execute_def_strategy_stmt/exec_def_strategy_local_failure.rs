//! Completed strategy stages and their detached, unaccepted local scope.
use crate::ast::stmt::DefStrategyStmt;
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::execute_fact_stmt::{
    AssumeDomFactResult, VerifyFactResult, VerifyFactWellDefinedResult,
};
use crate::execute::execute_proof_block_stmt::ProofBlockBodyFailed;
use crate::execute::{
    ExecStmtResult, IntroduceTypedParametersFailed, IntroduceTypedParametersResult,
};

pub struct ExecDefStrategyLocalFailure {
    pub statement: DefStrategyStmt,
    pub goal_wd: VerifyFactWellDefinedResult,
    pub body: ExecDefStrategyForallFailed,
    pub local_env: Box<ExecEnv>,
}

pub enum ExecDefStrategyForallFailed {
    Introduce(IntroduceTypedParametersFailed),
    Entered {
        introduced_params: IntroduceTypedParametersResult,
        assumed_dom_facts: Vec<AssumeDomFactResult>,
        failure: ExecDefStrategyEnteredFailed,
    },
}

pub enum ExecDefStrategyEnteredFailed {
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
