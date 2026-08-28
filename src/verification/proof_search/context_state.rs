//! Verification options threaded through recursive proof search.

/// Control flags for one recursive verification attempt.
///
/// `proof_search_round` bounds how aggressively recursive verification may retry a goal.
/// Round 0 is the normal path. Later rounds are used by callers that need a
/// more restricted retry to avoid repeatedly re-entering the same known-forall,
/// strategy, or well-definedness search. Round 2 is the final retry.
///
/// `well_definedness_verified` means the current caller has already checked
/// the well-definedness obligations for the fact or object being verified, so
/// child checks should not repeat that gate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifyState {
    pub proof_search_round: u8,
    pub well_definedness_verified: bool,
}

impl VerifyState {
    const FINAL_ROUND: u8 = 2;

    pub fn initial() -> Self {
        Self::standard(0, false)
    }

    pub fn after_well_definedness() -> Self {
        Self::standard(0, true)
    }

    pub fn final_round() -> Self {
        Self::standard(Self::FINAL_ROUND, false)
    }

    pub fn final_round_after_well_definedness() -> Self {
        Self::standard(Self::FINAL_ROUND, true)
    }

    fn standard(proof_search_round: u8, well_definedness_verified: bool) -> Self {
        Self {
            proof_search_round,
            well_definedness_verified,
        }
    }

    pub fn with_next_round(&self) -> Self {
        Self {
            proof_search_round: self.proof_search_round + 1,
            ..*self
        }
    }

    pub fn with_well_definedness_verified(&self) -> Self {
        Self {
            well_definedness_verified: true,
            ..*self
        }
    }

    pub fn is_initial_round(&self) -> bool {
        self.proof_search_round == 0
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/verification/proof_search/context_state.rs"]
mod tests;
