use super::{LitexToLeanFactIr, LitexToLeanStatementIr, LitexToLeanWellDefinednessCertificateIr};

/// Checked declaration effect of one source `thm` statement.
///
/// The complete theorem remains separate from any clause-coverage projections:
/// it is emitted under `name`, while independently stored consequences retain
/// their ordinary `FactId` declarations.
#[derive(Clone, Debug)]
pub struct LitexToLeanNamedTheoremIr {
    pub name: String,
    pub theorem: LitexToLeanFactIr,
    pub expected_proof_step_count: usize,
    pub proof_steps: Vec<LitexToLeanNamedTheoremProofStepIr>,
    pub stored_projections: Vec<LitexToLeanFactIr>,
    pub inferred_facts: Vec<LitexToLeanFactIr>,
    pub well_definedness: LitexToLeanWellDefinednessCertificateIr,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanNamedTheoremProofStepIr {
    /// One-based source order, frozen independently from vector position.
    pub position: usize,
    pub statement: LitexToLeanStatementIr,
}
