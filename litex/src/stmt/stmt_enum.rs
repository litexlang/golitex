use std::fmt;
use crate::fact::Fact;
use super::definition_stmt::DefStmt;
use super::claim_stmt::ClaimStmt;
use super::know_stmt::KnowStmt;
use super::proof_technique_stmt::ProofTechniqueStmt;
use super::tooling_stmt::ToolingStmt;
use super::prove_stmt::ProveStmt;
use super::eval_stmt::EvalStmt;
use super::witness_stmt::WitnessStmt;

pub enum Stmt {
    Fact(Fact),
    DefStmt(DefStmt),
    ClaimStmt(ClaimStmt),
    KnowStmt(KnowStmt),
    ProveStmt(ProveStmt),
    ToolingStmt(ToolingStmt),
    EvalStmt(EvalStmt),
    WitnessStmt(WitnessStmt),
    ProofTechnique(ProofTechniqueStmt),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Fact(fact) => write!(f, "{}", fact),
            Stmt::DefStmt(def_stmt) => write!(f, "{}", def_stmt),
            Stmt::ClaimStmt(claim_stmt) => write!(f, "{}", claim_stmt),
            Stmt::KnowStmt(know_stmt) => write!(f, "{}", know_stmt),
            Stmt::ProofTechnique(proof_technique) => write!(f, "{}", proof_technique),
            Stmt::ToolingStmt(tooling_stmt) => write!(f, "{}", tooling_stmt),
            Stmt::ProveStmt(prove_stmt) => write!(f, "{}", prove_stmt),
            Stmt::EvalStmt(eval_stmt) => write!(f, "{}", eval_stmt),
            Stmt::WitnessStmt(witness_stmt) => write!(f, "{}", witness_stmt),
        }
    }
}

impl Stmt {
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            Stmt::Fact(fact) => fact.line_file(),
            Stmt::DefStmt(def_stmt) => def_stmt.line_file(),
            Stmt::ClaimStmt(claim_stmt) => claim_stmt.line_file(),
            Stmt::KnowStmt(know_stmt) => know_stmt.line_file(),
            Stmt::ProofTechnique(proof_technique) => proof_technique.line_file(),
            Stmt::ToolingStmt(tooling_stmt) => tooling_stmt.line_file(),
            Stmt::ProveStmt(prove_stmt) => prove_stmt.line_file_index,
            Stmt::EvalStmt(eval_stmt) => eval_stmt.line_file_index,
            Stmt::WitnessStmt(witness_stmt) => witness_stmt.line_file(),
        }
    }
}
