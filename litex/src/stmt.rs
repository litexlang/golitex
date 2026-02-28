use std::fmt;
use crate::fact::Fact;
use crate::definition_stmt::DefStmt;
use crate::claim_stmt::ClaimProveStmt;
use crate::know_stmt::KnowStmt;
use crate::proof_techniques_stmt::ProofTechnique;
use crate::import_stmt::ImportStmt;
use crate::prove_stmt::ProveStmt;
use crate::run_file_stmt::RunFileStmt;
pub enum Stmt {
    Fact(Fact),
    DefStmt(DefStmt),
    ClaimProveStmt(ClaimProveStmt),
    KnowStmt(KnowStmt),
    ProofTechnique(ProofTechnique),
    ImportStmt(ImportStmt),
    ProveStmt(ProveStmt),
    RunFileStmt(RunFileStmt),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Fact(fact) => write!(f, "{}", fact),
            Stmt::DefStmt(def_stmt) => write!(f, "{}", def_stmt),
            Stmt::ClaimProveStmt(claim_stmt) => write!(f, "{}", claim_stmt),
            Stmt::KnowStmt(know_stmt) => write!(f, "{}", know_stmt),
            Stmt::ProofTechnique(proof_technique) => write!(f, "{}", proof_technique),
            Stmt::ImportStmt(import_stmt) => write!(f, "{}", import_stmt),
            Stmt::ProveStmt(prove_stmt) => write!(f, "{}", prove_stmt),
            Stmt::RunFileStmt(run_file_stmt) => write!(f, "{}", run_file_stmt),
        }
    }
}

/// 从 Stmt 取得 line 与 file_index（仅用于 Display 等）
pub fn line_file(stmt: &Stmt) -> (u32, usize) {
    match stmt {
        Stmt::Fact(fact) => fact.line_file(),
        Stmt::DefStmt(def_stmt) => def_stmt.line_file(),
        Stmt::ClaimProveStmt(claim_prove_stmt) => (claim_prove_stmt.line, claim_prove_stmt.file_index),
        Stmt::KnowStmt(know_stmt) => know_stmt.line_file(),
        Stmt::ProofTechnique(proof_technique) => proof_technique.line_file(),
        Stmt::ImportStmt(import_stmt) => import_stmt.line_file(),
        Stmt::ProveStmt(prove_stmt) => (prove_stmt.line, prove_stmt.file_index),
        Stmt::RunFileStmt(run_file_stmt) => (run_file_stmt.line, run_file_stmt.file_index),
    }
}

