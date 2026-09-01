//! Factual and non-factual success accessors.

use crate::prelude::*;

impl StmtResult {
    pub fn factual_success(&self) -> Option<&SuccessFactStmtResult> {
        match self {
            StmtResult::Success(SuccessStmtResult::Fact(success)) => Some(success.as_ref()),
            _ => None,
        }
    }

    pub fn factual_success_mut(&mut self) -> Option<&mut SuccessFactStmtResult> {
        match self {
            StmtResult::Success(SuccessStmtResult::Fact(success)) => Some(success.as_mut()),
            _ => None,
        }
    }

    pub fn infer_result(&self) -> SuccessInferResult {
        if let Some(success) = self.factual_success() {
            success.infers.clone()
        } else if let StmtResult::Success(success) = self {
            match success {
                SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ClaimStmt(claim)) => {
                    claim.environment_effects.clone()
                }
                _ => success
                    .common()
                    .map(|common| common.infers.clone())
                    .unwrap_or_else(SuccessInferResult::new),
            }
        } else {
            SuccessInferResult::new()
        }
    }

    pub fn into_factual_success(self) -> Option<SuccessFactStmtResult> {
        match self {
            StmtResult::Success(SuccessStmtResult::Fact(success)) => Some(*success),
            _ => None,
        }
    }

    pub fn non_factual_success(&self) -> Option<&SuccessStmtResult> {
        match self {
            StmtResult::Success(SuccessStmtResult::Fact(_)) | StmtResult::Unknown(_) => None,
            StmtResult::Success(success) => Some(success),
        }
    }

    pub fn non_factual_success_mut(&mut self) -> Option<&mut SuccessStmtResult> {
        match self {
            StmtResult::Success(SuccessStmtResult::Fact(_)) | StmtResult::Unknown(_) => None,
            StmtResult::Success(success) => Some(success),
        }
    }

    pub fn into_non_factual_success(self) -> Option<SuccessStmtResult> {
        match self {
            StmtResult::Success(SuccessStmtResult::Fact(_)) | StmtResult::Unknown(_) => None,
            StmtResult::Success(success) => Some(success),
        }
    }
}
