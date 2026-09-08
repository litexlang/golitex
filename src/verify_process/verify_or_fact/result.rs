use crate::prelude::*;

pub struct VerifyOrFactResult {
    pub chosen_branch_index: usize,
    pub proof_of_chosen_branch: VerifyFactResult,
}
