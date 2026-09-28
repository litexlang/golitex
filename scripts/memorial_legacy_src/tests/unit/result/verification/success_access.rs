//! Test-only accessors for successful verification evidence.

use super::*;

impl SuccessFactStmtResult {
    pub fn underlying_verified_by(&self) -> &SuccessFactProofResult {
        let mut proof = self
            .proof()
            .expect("trusted statements have no underlying verification proof");
        loop {
            match proof {
                SuccessFactProofResult::Reuse(result) => proof = result.source.proof(),
                verified_by => return verified_by,
            }
        }
    }
}

impl VerifiedFactResult {
    pub fn underlying_verified_by(&self) -> &SuccessFactProofResult {
        let mut proof = self.proof();
        loop {
            match proof {
                SuccessFactProofResult::Reuse(result) => proof = result.source.proof(),
                verified_by => return verified_by,
            }
        }
    }
}
