//! The actual entered contradiction stages, including a failed opposite check.
use crate::prelude::*;

pub struct ExecByContraLocalFailure {
    pub statement: crate::ast::stmt::ByContraStmt,
    pub goal_wd: VerifyFactWellDefinedResult,
    pub reverse_assumption: Fact,
    pub failure: ExecByContraEnteredFailed,
    pub local_env: Box<ExecEnv>,
}

impl ExecByContraLocalFailure {
    pub fn new(
        statement: crate::ast::stmt::ByContraStmt,
        goal_wd: VerifyFactWellDefinedResult,
        reverse_assumption: Fact,
        failure: ExecByContraEnteredFailed,
        local_env: Box<ExecEnv>,
    ) -> Self {
        Self {
            statement,
            goal_wd,
            reverse_assumption,
            failure,
            local_env,
        }
    }
}

pub enum ExecByContraEnteredFailed {
    AssumptionWd(VerifyFactWellDefinedResult),
    ProofBody {
        assumption: ContraAssumption,
        failure: crate::execute::execute_proof_block_stmt::ProofBlockBodyFailed,
    },
    Closing {
        assumption: ContraAssumption,
        proof_steps: Vec<ExecStmtResult>,
        failure: super::ByContradictionClosingFailed,
    },
}

pub struct ContraAssumption {
    pub well_defined: FactWellDefinedProof,
    pub store_and_infer: StoreFactAndInferResult,
    pub fact_id: crate::runtime::FactId,
    pub components: Vec<(crate::runtime::FactId, AtomicFact)>,
}

impl ContraAssumption {
    pub fn new(
        well_defined: FactWellDefinedProof,
        store_and_infer: StoreFactAndInferResult,
    ) -> Self {
        let fact_id = store_and_infer.primary_fact_id();
        let components = store_and_infer.atomic_components();
        Self {
            well_defined,
            store_and_infer,
            fact_id,
            components,
        }
    }
}

pub struct ExecByContraLocalProof {
    pub assumption: ContraAssumption,
    pub proof_steps: Vec<ExecStmtResult>,
    pub closing: super::ByContradictionClosingSuccess,
}

impl ExecByContraLocalProof {
    pub fn new(
        assumption: ContraAssumption,
        proof_steps: Vec<ExecStmtResult>,
        closing: super::ByContradictionClosingSuccess,
    ) -> Self {
        Self {
            assumption,
            proof_steps,
            closing,
        }
    }
}

pub struct ExecByContraStoreFailure {
    pub statement: crate::ast::stmt::ByContraStmt,
    pub goal_wd: VerifyFactWellDefinedResult,
    pub reverse_assumption: Fact,
    pub proof: ExecByContraLocalProof,
    pub local_env: Box<ExecEnv>,
    pub result: VerifyFactWellDefinedResult,
}

impl ExecByContraStoreFailure {
    pub fn new(
        statement: crate::ast::stmt::ByContraStmt,
        goal_wd: VerifyFactWellDefinedResult,
        reverse_assumption: Fact,
        proof: ExecByContraLocalProof,
        local_env: Box<ExecEnv>,
        result: VerifyFactWellDefinedResult,
    ) -> Self {
        Self {
            statement,
            goal_wd,
            reverse_assumption,
            proof,
            local_env,
            result,
        }
    }
}

pub struct ByContradictionAfterImpossibleFailed {
    pub impossible_fact: Fact,
    pub impossible: VerifyFactResult,
    pub failure: ByContradictionOppositeFailed,
}

impl ByContradictionAfterImpossibleFailed {
    pub fn new(
        impossible_fact: Fact,
        impossible: VerifyFactResult,
        failure: ByContradictionOppositeFailed,
    ) -> Self {
        Self {
            impossible_fact,
            impossible,
            failure,
        }
    }
}

pub enum ByContradictionOppositeFailed {
    NegationUnsupported(String),
    Verification(VerifyFactResult),
}

pub struct ExecByContraNegationFailure {
    pub statement: crate::ast::stmt::ByContraStmt,
    pub goal_wd: VerifyFactWellDefinedResult,
    pub message: String,
}

impl ExecByContraNegationFailure {
    pub fn new(
        statement: crate::ast::stmt::ByContraStmt,
        goal_wd: VerifyFactWellDefinedResult,
        message: String,
    ) -> Self {
        Self {
            statement,
            goal_wd,
            message,
        }
    }
}
