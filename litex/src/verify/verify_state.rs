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
}