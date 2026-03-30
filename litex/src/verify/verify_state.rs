pub struct VerifyState {
    pub round: u8,
    pub well_defined_already_verified: bool,
}

impl VerifyState {
    pub fn new(round: u8, well_defined_already_verified: bool) -> Self {
        VerifyState {
            round,
            well_defined_already_verified,
        }
    }

    pub fn is_final_round(&self) -> bool {
        self.round >= 2
    }

    pub fn new_state_with_round_increased(&self) -> Self {
        return Self::new(self.round + 1, self.well_defined_already_verified);
    }

    pub fn make_state_with_req_ok_set_to_true(&self) -> Self {
        return Self::new(self.round, true);
    }

    pub fn is_round_0(&self) -> bool {
        self.round == 0
    }
}
