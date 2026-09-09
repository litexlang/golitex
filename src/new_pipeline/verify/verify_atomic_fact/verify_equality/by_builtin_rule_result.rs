use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

// Each equality builtin rule gets its own variant and payload struct.
pub enum EqualitySearchProofByBuiltinRule2 {
    TheyAreTheSame(EqualitySearchProofByTheyAreTheSame2),
    Calculation(EqualitySearchProofByCalculation2),
}

pub struct EqualitySearchProofByTheyAreTheSame2 {}

pub struct EqualitySearchProofByCalculation2 {}
