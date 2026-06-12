/// Control flags for one recursive verification attempt.
///
/// `round` bounds how aggressively recursive verification may retry a goal.
/// Round 0 is the normal path. Later rounds are used by callers that need a
/// more restricted retry to avoid repeatedly re-entering the same known-forall,
/// strategy, or well-definedness search. Round 2 is treated as the final retry
/// by callers that explicitly request `make_final_round_state` or
/// `new_with_final_round`.
///
/// `well_defined_already_verified` means the current caller has already checked
/// the well-definedness obligations for the fact or object being verified, so
/// child checks should not repeat that gate.
///
/// `equality_can_use_known_forall` controls an important recursion boundary:
/// equality verification may usually instantiate known `forall` facts, but some
/// equality subchecks disable that route to prevent circular proof search.
pub struct VerifyState {
    pub round: u8,
    pub well_defined_already_verified: bool,
    pub equality_can_use_known_forall: bool,
}

impl VerifyState {
    pub fn new(round: u8, well_defined_already_verified: bool) -> Self {
        VerifyState {
            round,
            well_defined_already_verified,
            equality_can_use_known_forall: true,
        }
    }

    pub fn new_state_with_round_increased(&self) -> Self {
        return Self {
            round: self.round + 1,
            well_defined_already_verified: self.well_defined_already_verified,
            equality_can_use_known_forall: self.equality_can_use_known_forall,
        };
    }

    pub fn with_well_defined_already_verified(&self) -> Self {
        return Self {
            round: self.round,
            well_defined_already_verified: true,
            equality_can_use_known_forall: self.equality_can_use_known_forall,
        };
    }

    pub fn is_round_0(&self) -> bool {
        self.round == 0
    }

    pub fn make_final_round_state(&self) -> Self {
        return Self {
            round: 2,
            well_defined_already_verified: self.well_defined_already_verified,
            equality_can_use_known_forall: self.equality_can_use_known_forall,
        };
    }

    pub fn new_with_final_round(well_defined_already_verified: bool) -> Self {
        return Self::new(2, well_defined_already_verified);
    }

    pub fn without_known_forall_for_equality(&self) -> Self {
        return Self {
            round: self.round,
            well_defined_already_verified: self.well_defined_already_verified,
            equality_can_use_known_forall: false,
        };
    }
}
