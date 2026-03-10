pub struct VerifyState {
    pub round: u8,
    pub req_ok: bool,
}

impl VerifyState {
    pub fn new(round: u8, req_ok: bool) -> Self {
        VerifyState {
            round,
            req_ok,
        }
    }

    pub fn is_final_round(&self) -> bool {
        self.round >= 2
    }

    pub fn new_state_with_round_increased(&mut self) -> Self {
        return Self::new(self.round + 1, self.req_ok);
    }

    pub fn new_state_with_req_ok_set_to_true(&mut self) -> Self {
        return Self::new(self.round, true);
    }
}