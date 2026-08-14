use super::{LitexToLeanFactIr, LitexToLeanStatementIr, LitexToLeanWellDefinednessCertificateIr};

/// Checked IR for one source `DefThmStmt`.
#[derive(Clone, Debug)]
pub struct LitexToLeanDefThmStmtIr {
    pub name: String,
    pub theorem: LitexToLeanFactIr,
    pub expected_proof_step_count: usize,
    pub proof_steps: Vec<LitexToLeanDefThmStmtProofStepIr>,
    pub stored_projections: Vec<LitexToLeanFactIr>,
    pub inferred_facts: Vec<LitexToLeanFactIr>,
    pub well_definedness: LitexToLeanWellDefinednessCertificateIr,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanDefThmStmtProofStepIr {
    /// One-based source order, frozen independently from vector position.
    pub position: usize,
    pub statement: LitexToLeanStatementIr,
}
