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
///
/// `list_set_membership_can_use_equality_builtin` lets selected builtin premises
/// restrict list-set membership to reflexive or already-known element equality.
pub struct VerifyState {
    pub round: u8,
    pub well_defined_already_verified: bool,
    pub equality_can_use_known_forall: bool,
    pub list_set_membership_can_use_equality_builtin: bool,
}

impl VerifyState {
    pub fn new(round: u8, well_defined_already_verified: bool) -> Self {
        VerifyState {
            round,
            well_defined_already_verified,
            equality_can_use_known_forall: true,
            list_set_membership_can_use_equality_builtin: true,
        }
    }

    pub fn new_state_with_round_increased(&self) -> Self {
        return Self {
            round: self.round + 1,
            well_defined_already_verified: self.well_defined_already_verified,
            equality_can_use_known_forall: self.equality_can_use_known_forall,
            list_set_membership_can_use_equality_builtin: self
                .list_set_membership_can_use_equality_builtin,
        };
    }

    pub fn with_well_defined_already_verified(&self) -> Self {
        return Self {
            round: self.round,
            well_defined_already_verified: true,
            equality_can_use_known_forall: self.equality_can_use_known_forall,
            list_set_membership_can_use_equality_builtin: self
                .list_set_membership_can_use_equality_builtin,
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
            list_set_membership_can_use_equality_builtin: self
                .list_set_membership_can_use_equality_builtin,
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
            list_set_membership_can_use_equality_builtin: self
                .list_set_membership_can_use_equality_builtin,
        };
    }

    pub fn without_equality_builtin_for_list_set_membership(&self) -> Self {
        return Self {
            round: self.round,
            well_defined_already_verified: self.well_defined_already_verified,
            equality_can_use_known_forall: self.equality_can_use_known_forall,
            list_set_membership_can_use_equality_builtin: false,
        };
    }
}
