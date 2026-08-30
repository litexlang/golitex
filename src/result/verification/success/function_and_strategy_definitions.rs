//! Case-function, unique-existence function, and strategy definition outcomes.

use crate::prelude::*;
use std::rc::Rc;

/// The three object checks performed by the shared sequence/finite-sequence/
/// matrix definition layer. Keeping them named prevents the statement result
/// from collapsing constructor-specific WD work into an untyped vector.
pub struct SuccessVerifyIndexedFunctionDefinitionWellDefinedResult {
    pub surface_set: Rc<SuccessVerifyObjWellDefinedResult>,
    pub anonymous_function: Rc<SuccessVerifyObjWellDefinedResult>,
    pub function_set: Rc<SuccessVerifyObjWellDefinedResult>,
}

pub struct SuccessVerifyCaseFunctionDefinitionResult {
    pub coverage_check: Box<StmtResult>,
    pub return_checks: Vec<StmtResult>,
}

pub struct SuccessVerifyFunctionFromUniqueExistenceResult {
    /// Recursive well-definedness for the exact source `forall ... exist!`
    /// contract.  The Lean compiler needs the binder-owned object and fact
    /// certificates while replaying the chosen function under its arguments.
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    /// Parameter-membership and domain-premise facts created only inside the
    /// source forall scope.  Their FactIds must be frozen before that scope is
    /// removed; proof children cite these identities directly.
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub source_forall_check: Option<Box<StmtResult>>,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<StmtResult>,
}

impl SuccessVerifyFunctionFromUniqueExistenceResult {
    pub fn new(
        well_definedness: SuccessVerifyFactWellDefinedResult,
        proof_scope: SuccessVerifyLocalProofScopeResult,
        source_forall_check: Option<StmtResult>,
        proof_steps: Vec<StmtResult>,
        conclusion_checks: Vec<StmtResult>,
    ) -> Self {
        Self {
            well_definedness,
            proof_scope,
            source_forall_check: source_forall_check.map(Box::new),
            proof_steps,
            conclusion_checks,
        }
    }
}

pub struct SuccessVerifyStrategyDefinitionResult {
    pub name: String,
    pub forall_fact: ForallFact,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<StmtResult>,
}

impl SuccessVerifyStrategyDefinitionResult {
    pub fn new(
        name: String,
        forall_fact: ForallFact,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        proof_scope: SuccessVerifyLocalProofScopeResult,
        proof_steps: Vec<StmtResult>,
        conclusion_checks: Vec<StmtResult>,
    ) -> Self {
        Self {
            name,
            forall_fact,
            well_definedness,
            proof_scope,
            proof_steps,
            conclusion_checks,
        }
    }
}
