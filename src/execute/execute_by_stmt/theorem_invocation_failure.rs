//! Actual stages of an unaccepted theorem invocation; no outer publication.
use crate::prelude::*;

pub struct TheoremInvocationLocalFailure {
    pub origin: TheoremInvocationOrigin,
    pub callee: super::ResolvedTheoremCallee,
    pub(crate) prepared: super::PreparedRelease,
    pub failure: TheoremInvocationLocalFailed,
    pub local_env: Box<ExecEnv>,
}

impl TheoremInvocationLocalFailure {
    pub(crate) fn new(
        origin: TheoremInvocationOrigin,
        callee: super::ResolvedTheoremCallee,
        prepared: super::PreparedRelease,
        failure: TheoremInvocationLocalFailed,
        local_env: Box<ExecEnv>,
    ) -> Self {
        Self {
            origin,
            callee,
            prepared,
            failure,
            local_env,
        }
    }
}

pub enum TheoremInvocationOrigin {
    ByThm(crate::ast::stmt::ByThmStmt),
    ReleaseThm(crate::ast::stmt::ReleaseThmStmt),
}

impl TheoremInvocationOrigin {
    pub fn call(&self) -> &crate::ast::stmt::TheoremCall {
        match self {
            Self::ByThm(stmt) => &stmt.call,
            Self::ReleaseThm(stmt) => &stmt.call,
        }
    }
}

pub struct TheoremInvocationPreparationFailure {
    pub origin: TheoremInvocationOrigin,
    pub failure: super::ExecReleaseThmStmtFailed,
}

impl TheoremInvocationPreparationFailure {
    pub fn new(origin: TheoremInvocationOrigin, failure: super::ExecReleaseThmStmtFailed) -> Self {
        Self { origin, failure }
    }
}

// One completed requirement is verified before its actual local store.
pub struct TheoremRequirementChecked {
    pub proof: VerifyFactResult,
    pub stored: StoreFactAndInferResult,
}

impl TheoremRequirementChecked {
    pub fn new(proof: VerifyFactResult, stored: StoreFactAndInferResult) -> Self {
        Self { proof, stored }
    }
}

pub struct VerifiedTheoremInvocation {
    pub type_checks: Vec<TheoremRequirementChecked>,
    pub function_domain: Option<super::BuiltinFunctionDomainProof>,
    pub premise_checks: Vec<TheoremRequirementChecked>,
    pub theorem_derivation: super::TheoremDerivationProof,
    pub conclusions_wd: Vec<FactWellDefinedProof>,
}

impl VerifiedTheoremInvocation {
    pub fn new(
        type_checks: Vec<TheoremRequirementChecked>,
        function_domain: Option<super::BuiltinFunctionDomainProof>,
        premise_checks: Vec<TheoremRequirementChecked>,
        theorem_derivation: super::TheoremDerivationProof,
        conclusions_wd: Vec<FactWellDefinedProof>,
    ) -> Self {
        Self {
            type_checks,
            function_domain,
            premise_checks,
            theorem_derivation,
            conclusions_wd,
        }
    }
}

pub struct TheoremFunctionDomainFailure {
    pub completed_peers:
        Vec<crate::execute::execute_fact_stmt::function_domain::FunctionDomainMatchProof>,
    pub failure: super::ExecReleaseThmStmtFailed,
}

impl TheoremFunctionDomainFailure {
    pub fn new(
        completed_peers: Vec<
            crate::execute::execute_fact_stmt::function_domain::FunctionDomainMatchProof,
        >,
        failure: super::ExecReleaseThmStmtFailed,
    ) -> Self {
        Self {
            completed_peers,
            failure,
        }
    }
}

pub enum TheoremInvocationFailed {
    Type {
        type_checks: Vec<TheoremRequirementChecked>,
        failure: super::ExecReleaseThmStmtFailed,
    },
    FunctionDomain {
        type_checks: Vec<TheoremRequirementChecked>,
        result: TheoremFunctionDomainFailure,
    },
    Premise {
        type_checks: Vec<TheoremRequirementChecked>,
        function_domain: Option<super::BuiltinFunctionDomainProof>,
        premise_checks: Vec<TheoremRequirementChecked>,
        failure: super::ExecReleaseThmStmtFailed,
    },
    Derivation {
        type_checks: Vec<TheoremRequirementChecked>,
        function_domain: Option<super::BuiltinFunctionDomainProof>,
        premise_checks: Vec<TheoremRequirementChecked>,
        failure: super::ExecReleaseThmStmtFailed,
    },
    ConclusionWd {
        type_checks: Vec<TheoremRequirementChecked>,
        function_domain: Option<super::BuiltinFunctionDomainProof>,
        premise_checks: Vec<TheoremRequirementChecked>,
        theorem_derivation: super::TheoremDerivationProof,
        conclusions_wd: Vec<FactWellDefinedProof>,
        failure: super::ExecReleaseThmStmtFailed,
    },
}

pub enum TheoremInvocationLocalFailed {
    Invocation(TheoremInvocationFailed),
    Selection {
        verified: VerifiedTheoremInvocation,
        returned_conclusions: Vec<StoreFactAndInferResult>,
        failure: TheoremSelectionFailed,
    },
}

pub enum TheoremSelectionFailed {
    NotReturned {
        fact: Fact,
    },
    Selected {
        fact: Fact,
        result: VerifyFactResult,
    },
}

pub struct SelectedTheoremInvocationVerified {
    pub invocation: VerifiedTheoremInvocation,
    pub returned_conclusions: Vec<StoreFactAndInferResult>,
    pub selected_proof: VerifyFactResult,
}

impl SelectedTheoremInvocationVerified {
    pub fn new(
        invocation: VerifiedTheoremInvocation,
        returned_conclusions: Vec<StoreFactAndInferResult>,
        selected_proof: VerifyFactResult,
    ) -> Self {
        Self {
            invocation,
            returned_conclusions,
            selected_proof,
        }
    }
}

pub enum TheoremInvocationCheckedLocal {
    Release(VerifiedTheoremInvocation),
    ByThm(SelectedTheoremInvocationVerified),
}

pub struct TheoremInvocationClosingFailure {
    pub origin: TheoremInvocationOrigin,
    pub callee: super::ResolvedTheoremCallee,
    pub(crate) prepared: super::PreparedRelease,
    pub checked: TheoremInvocationCheckedLocal,
    pub local_env: Box<ExecEnv>,
    pub failure: TheoremInvocationClosingFailed,
}

impl TheoremInvocationClosingFailure {
    pub(crate) fn new(
        origin: TheoremInvocationOrigin,
        callee: super::ResolvedTheoremCallee,
        prepared: super::PreparedRelease,
        checked: TheoremInvocationCheckedLocal,
        local_env: Box<ExecEnv>,
        failure: TheoremInvocationClosingFailed,
    ) -> Self {
        Self {
            origin,
            callee,
            prepared,
            checked,
            local_env,
            failure,
        }
    }
}

pub enum TheoremInvocationClosingFailed {
    Release {
        stored_wd: Vec<FactWellDefinedProof>,
        stored: Vec<StoreFactAndInferResult>,
        index: usize,
        result: VerifyFactWellDefinedResult,
    },
    ByThm {
        result: VerifyFactWellDefinedResult,
    },
}
