use crate::prelude::*;
use crate::verify_rewrite::VerifyState;

// Each equality builtin rule gets its own variant and payload struct.
pub enum EqualitySearchProofByBuiltinRule {
    TheyAreTheSame(EqualitySearchProofByTheyAreTheSame),
    Calculation(EqualitySearchProofByCalculation),
}

pub struct EqualitySearchProofByTheyAreTheSame {}

pub struct EqualitySearchProofByCalculation {}
