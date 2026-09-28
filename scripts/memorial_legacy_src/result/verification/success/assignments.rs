//! Assignment proof outcomes.

use crate::prelude::*;

#[derive(Debug)]
pub struct SuccessVerifyByAssignmentResult {
    pub assignment: Vec<(String, String)>,
    pub assumptions: Vec<SuccessVerifyByAssignmentAssumptionResult>,
    pub domain_checks: Vec<SuccessVerifyByAssignmentDomainResult>,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<VerifyFactResult>,
}

/// One exact fact introduced by a finite assignment branch. The complete
/// inference Result stays with the assumption because later proof children
/// may cite either its source FactId or one of its typed consequences.
#[derive(Debug)]
pub struct SuccessVerifyByAssignmentAssumptionResult {
    pub fact: Fact,
    pub fact_id: FactId,
    pub reason: String,
    pub infers: SuccessInferResult,
}

#[derive(Debug)]
pub struct SuccessVerifyByAssignmentDomainResult {
    pub fact: Fact,
    pub check: Box<VerifyFactResult>,
    pub negated_check: Option<Box<VerifyFactResult>>,
    pub satisfied: bool,
    /// Exact store/inference effects published only by a satisfied branch.
    /// A skipped assignment retains `None` and its checked negation instead.
    pub satisfied_infers: Option<SuccessInferResult>,
}

impl SuccessVerifyByAssignmentResult {
    pub fn new(
        assignment: Vec<(String, String)>,
        assumptions: Vec<SuccessVerifyByAssignmentAssumptionResult>,
        domain_checks: Vec<SuccessVerifyByAssignmentDomainResult>,
        proof_steps: Vec<StmtResult>,
        conclusion_checks: Vec<VerifyFactResult>,
    ) -> Self {
        SuccessVerifyByAssignmentResult {
            assignment,
            assumptions,
            domain_checks,
            proof_steps,
            conclusion_checks,
        }
    }
}
